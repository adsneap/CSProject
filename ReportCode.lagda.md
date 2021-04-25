\begin{code}

{-# OPTIONS --without-K --exact-split  #-}

\end{code}

I use the same module parameters as in the module parameters of the TypeTopology Library.
The modules I write in this file are my own work, the imports are from the TypeTopology Library.

\begin{code}

module ReportCode where

 open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology

 module RMoreNaturalProperties where

  open import NaturalsAddition --TypeTopology
  open import NaturalNumbers-Properties --TypeTopology

  addition-right-succ : (x y : ℕ) → x + succ y ≡ succ (x + y)
  addition-right-succ x y = refl

  succ-left : (x y : ℕ) → succ x + y ≡ succ (x + y)
  succ-left x = induction base step 
    where
      base : succ x + 0 ≡ succ (x + 0)
      base = ap succ refl

      step : (k : ℕ) → succ x + k ≡ succ (x + k) → succ x + succ k ≡ succ (x + succ k)
      step k IH = ap succ IH

  +-comm : (x n : ℕ) → x + n ≡ n + x
  +-comm x = induction base step
    where
      base : x + 0 ≡ 0 + x
      base = zero-left-neutral x ⁻¹

      step : (k : ℕ) → x + k ≡ k + x → x + succ k ≡ succ k + x
      step k IH = x + succ k    ≡⟨ refl ⟩
                  succ (x + k)  ≡⟨ ap succ IH ⟩
                  succ (k + x)  ≡⟨ succ-left k x ⁻¹ ⟩
                  succ k + x ∎

  addition-left-cancellable : (x y z : ℕ) → z + x ≡ z + y → x ≡ y
  addition-left-cancellable x y = induction base step
   where
    base : 0 + x ≡ 0 + y → x ≡ y
    base h = x      ≡⟨ zero-left-neutral x ⁻¹ ⟩
             0 + x  ≡⟨ h                      ⟩
             0 + y  ≡⟨ zero-left-neutral y    ⟩
             y ∎

    step : (k : ℕ)
         → (k + x      ≡ k + y      → x ≡ y)
         → (succ k + x ≡ succ k + y → x ≡ y)
    step k IH r = IH (succ-lc (lemma₁ r))
     where
      lemma₁ : succ k + x ≡ succ k + y → succ (k + x) ≡ succ (k + y)
      lemma₁ r = succ (k + x)           ≡⟨ succ-left k x ⁻¹ ⟩
                 succ k + x             ≡⟨ r                         ⟩
                 succ k + y             ≡⟨ succ-left k y    ⟩
                 succ (k + y) ∎        


  addition-right-cancellable : (x y z : ℕ) → x + z ≡ y + z → x ≡ y
  addition-right-cancellable x y z r = addition-left-cancellable x y z lemma₀
   where
    lemma₀ : z + x ≡ z + y
    lemma₀ = z + x      ≡⟨ addition-commutativity z x ⟩
             x + z      ≡⟨ r                          ⟩
             y + z      ≡⟨ addition-commutativity y z ⟩ 
             z + y ∎

  sum-to-zero-gives-zero : (x y : ℕ) → x + y ≡ 0 → y ≡ 0
  sum-to-zero-gives-zero x 0        e = refl
  sum-to-zero-gives-zero x (succ y) e = have positive-not-zero (x + y) which-contradicts e

  succ-pred : (x : ℕ) → succ (pred (succ x)) ≡ succ x
  succ-pred x = refl

  succ-pred' : (x : ℕ) → ¬ (x ≡ 0) → succ (pred x) ≡ x
  succ-pred' zero     nz = 𝟘-elim (nz refl)
  succ-pred' (succ n) _ = refl

  pred-succ : (x : ℕ) → pred (succ (succ x)) ≡ succ x
  pred-succ x = refl

\end{code}

Sum of these properties are for use in later modules, and were simple enough for me to work on with limited Agda experience. I now extend Martin's Implementation of Order on the Natural Numbers

\begin{code}

 module RNaturalsOrderExtended where

  open import NaturalsAddition --TypeTopology
  open import NaturalsOrder --TypeTopology

  ≤-trans₂ : (x y u v : ℕ) → x ≤ y → y ≤ u → u ≤ v → x ≤ v
  ≤-trans₂ x y u v l₁ l₂ = ≤-trans x u v I
   where
    I : x ≤ u
    I = ≤-trans x y u l₁ l₂

  <-trans₂ : (x y u v : ℕ) → x < y → y < u → u < v → x < v
  <-trans₂ x y u v l₁ l₂ = <-trans x u v I
   where
    I : x < u
    I = <-trans x y u l₁ l₂

  nat-order-trichotomous : (x y : ℕ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
  nat-order-trichotomous 0        0        = inr (inl refl)
  nat-order-trichotomous 0        (succ y) = inl (zero-minimal y)
  nat-order-trichotomous (succ x) 0        = inr (inr (zero-minimal x))
  nat-order-trichotomous (succ x) (succ y) = tri-split (nat-order-trichotomous x y)
   where
    tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → (succ x < succ y) ∔ (succ x ≡ succ y) ∔ (succ y < succ x)
    tri-split (inl z)       = inl z
    tri-split (inr (inl z)) = inr (inl (ap succ z))
    tri-split (inr (inr z)) = inr (inr z)

  ≤-n-monotone-right : (x y z : ℕ) → x ≤ y → (x + z) ≤ (y + z)
  ≤-n-monotone-right x y 0        l = l
  ≤-n-monotone-right x y (succ n) l = ≤-n-monotone-right x y n l

  open import UF-Base

  ≤-n-monotone-left : (x y z : ℕ) → x ≤ y → (z + x) ≤ (z + y)
  ≤-n-monotone-left x y z l = transport₂ _≤_ (addition-commutativity x z) (addition-commutativity y z) (≤-n-monotone-right x y z l)

  ≤-adding : (x y u v : ℕ) → x ≤ y → u ≤ v → (x + u) ≤ (y + v)
  ≤-adding x y u v l₁ l₂ = ≤-trans (x + u) (y + u) (y + v) (≤-n-monotone-right x y u l₁) (≤-n-monotone-left u v y l₂)

  <-succ-monotone : (x y : ℕ) → x < y → succ x < succ y
  <-succ-monotone x y = id

  <-n-monotone-right : (x y z : ℕ) → x < y → (x + z) < (y + z)
  <-n-monotone-right x y  0       l = l
  <-n-monotone-right x y (succ z) l = <-n-monotone-right x y z l

  <-n-monotone-left : (x y z : ℕ) → x < y → (z + x) < (z + y)
  <-n-monotone-left x y z l = transport₂ _<_ (addition-commutativity x z) (addition-commutativity y z) (<-n-monotone-right x y z l)

  <-adding : (x y u v : ℕ) → x < y → u < v → (x + u) < (y + v)
  <-adding x y u v l₁ l₂ = <-trans (x + u) (y + u) (y + v) (<-n-monotone-right x y u l₁) (<-n-monotone-left u v y l₂)

  <-+ : (x y z : ℕ) → x < y → x < y + z
  <-+ x y z l₁ = ≤-trans (succ x) y (y + z) l₁ l₂
   where
    l₂ : y ≤ y + z
    l₂ = ≤-+ y z

  equal-gives-less-than-or-equal : (x y : ℕ) → x ≡ y → x ≤ y
  equal-gives-less-than-or-equal x y p = transport (_≤ y) (p ⁻¹) (≤-refl y)

  less-than-not-equal : (x y : ℕ) → x < y → ¬ (x ≡ y)
  less-than-not-equal x y r p = less-not-bigger-or-equal x y r (equal-gives-less-than-or-equal y x (p ⁻¹))

  less-than-one-is-zero : (x : ℕ) → x < 1 → x ≡ 0
  less-than-one-is-zero 0        l = refl
  less-than-one-is-zero (succ x) l = 𝟘-elim l

  not-less-or-equal-is-bigger : (x y : ℕ) → ¬(x ≤ y) → y < x
  not-less-or-equal-is-bigger 0        y        l = l (zero-minimal y)
  not-less-or-equal-is-bigger (succ x) 0        l = zero-minimal x
  not-less-or-equal-is-bigger (succ x) (succ y) l = not-less-or-equal-is-bigger x y l

  ≥-dichotomy : (x y : ℕ) → x ≥ y ∔ x ≤ y
  ≥-dichotomy 0        y        = inr (zero-minimal y)
  ≥-dichotomy (succ x) 0        = inl (zero-minimal (succ x))
  ≥-dichotomy (succ x) (succ y) = ≥-dichotomy x y

  subtraction' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , (z + x ≡ y)
  subtraction' 0        0        l = 𝟘-induction l
  subtraction' 0        (succ y) l = (succ y) , refl
  subtraction' (succ x) (succ y) l = pr₁ IH , ap succ (pr₂ IH)
   where
    IH : Σ z ꞉ ℕ , z + x ≡ y 
    IH = subtraction' x y l

  subtraction'' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , ((succ z) + x ≡ y)
  subtraction'' 0        0        l = 𝟘-elim l
  subtraction'' 0        (succ y) l = y , refl
  subtraction'' (succ x) 0        l = 𝟘-elim l
  subtraction'' (succ x) (succ y) l = z , ap succ e
   where
    I : Σ z ꞉ ℕ , succ z + x ≡ y
    I = subtraction'' x y l

    z : ℕ
    z = pr₁ I

    e : succ z + x ≡ y
    e = pr₂ I

  open import DecidableAndDetachable --TypeTopology

  least-element-unique : {A : ℕ → 𝓤 ̇} → (σ : detachable A)
                                        → ((α , αₚ) : Σ k ꞉ ℕ , A k × ((z : ℕ) → A z → k ≤ z))
                                        → ((β , βₚ) : Σ n ꞉ ℕ , A n × ((z : ℕ) → A z → n ≤ z))
                                        → α ≡ β
  least-element-unique σ (α , α₀ , α₁) (β , β₀ , β₁) = ≤-anti α β I II
   where
    I : α ≤ β
    I = α₁ β β₀

    II : β ≤ α
    II = β₁ α α₀

  least-element-unique' : {A : ℕ → 𝓤 ̇} → (σ : detachable A)
                                         → (x y : ℕ)
                                         → (δ : Σ A) → x ≡ pr₁ (minimal-from-given A σ δ) → y ≡ pr₁ (minimal-from-given A σ δ)
                                         → x ≡ y
  least-element-unique' σ x y δ e₁ e₂ = e₁ ∙ e₂ ⁻¹

  order-split : (x y : ℕ) → (x < y) ∔ (x ≥ y)
  order-split 0        0        = inr (zero-minimal 0)
  order-split 0        (succ y) = inl (zero-minimal (succ y))
  order-split (succ x) 0        = inr (zero-minimal (succ x))
  order-split (succ x) (succ y) = order-split x y

  bounded-maximisation : (A : ℕ → 𝓤 ̇) → detachable A
                       → (k : ℕ)
                       → (Σ m ꞉ ℕ , (m < k × A m × ((n : ℕ) → n < k → A n → n ≤ m))) ∔ ((n : ℕ) → A n → n ≥ k) 
  bounded-maximisation A δ zero = inr (λ n a → zero-minimal n)
  bounded-maximisation A δ (succ k) = f (bounded-maximisation A δ k)
   where
    conclusion = (Σ m ꞉ ℕ , (m < succ k) × A m × ((n : ℕ) → n < succ k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ succ k)

    f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → n < k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ k)
      → conclusion
    f (inl (m , l , a , ψ)) = g (δ k)
     where
      g : A k ∔ ¬ A k → conclusion 
      g (inl k-holds) = inl (k , ((<-succ k) , (k-holds , ψ')))
       where
         ψ' : (n : ℕ) → n < succ k → A n → n ≤ k
         ψ' n z a' = z
      g (inr k-fails) = inl (m , ((<-trans m k (succ k) l (<-succ k)) , a , ψ'))
       where
        ψ' : (n : ℕ) → n < succ k → A n → n ≤ m
        ψ' n z a' = ψ n (ρ (<-split n k z)) a'
         where
          ρ : (n < k) ∔ (n ≡ k) → n < k
          ρ (inl r) = r
          ρ (inr r) = 𝟘-elim (k-fails (transport (λ - → A -) r a'))
    f (inr ω) = g (δ k)
     where
      g : A k ∔ ¬ A k → conclusion
      g (inl k-holds) = inl (k , (<-succ k , k-holds , (λ z l a' → l)))
      g (inr k-fails) = inr ψ
       where
        ψ : (n : ℕ) → A n → n ≥ succ k
        ψ n n-holds = τ (<-split k n (ω n n-holds))
         where
          τ : (k < n) ∔ (k ≡ n) → n ≥ succ k
          τ (inr w) = 𝟘-elim (k-fails (transport (λ - → A -) (w ⁻¹) n-holds))
          τ (inl w) = w

  bounded-maximisation' : (A : ℕ → 𝓤 ̇) → detachable A
     → (k : ℕ)
     → (Σ m ꞉ ℕ , (m ≤ k × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m))) ∔ ((n : ℕ) → A n → n > k)
  bounded-maximisation' A δ k = result (bounded-maximisation A δ k) (δ k)
   where
    result : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → n < k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ k) → A k ∔ ¬ A k
           → (Σ m ꞉ ℕ , (m ≤ k) × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n > k)
    result (inl z) (inl k-holds) = inl (k , (≤-refl k , (k-holds , (λ _ t _ → t))))
    result (inr z) (inl k-holds) = inl (k , ≤-refl k , k-holds , (λ _ t _ → t))
    result (inl (m , l , a , ψ)) (inr k-fails) = inl (m , (<-coarser-than-≤ m k l) , a , g)
     where
      g : (n : ℕ) → n ≤ k → A n → n ≤ m
      g n l' a' = ψ n (h (<-split n k l')) a'
       where
        h : (n < k) ∔ (n ≡ k) → n < k
        h (inl j) = j
        h (inr j) = 𝟘-elim (k-fails (transport (λ - → A -) j a'))
    result (inr z) (inr k-fails) = inr f
     where
      f : (n : ℕ) → A n → n > k
      f n a = g (<-split k n (z n a)) 
       where
        g : (k < n) ∔ (k ≡ n) → n > k
        g (inl j) = j
        g (inr j) = 𝟘-elim (k-fails (transport (λ - → A -) (j ⁻¹) a))

  -- type of maximal element m : ℕ such that A m holds, given an upper bound

  maximal-element : (A : ℕ → 𝓤 ̇) → (k : ℕ) → 𝓤 ̇
  maximal-element A k = Σ m ꞉ ℕ , (m < k × A m × ((n : ℕ) → n < k → A n → n ≤ m))

  maximal-element' : (A : ℕ → 𝓤 ̇) → (k : ℕ) → 𝓤 ̇
  maximal-element' A k = Σ m ꞉ ℕ , (m ≤ k × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m))

  --with bound b

  maximal-from-given : (A : ℕ → 𝓤 ̇) → (b : ℕ) → detachable A → Σ k ꞉ ℕ , A k × k < b → maximal-element A b
  maximal-from-given A b δ (k , a) = f (bounded-maximisation A δ b)
   where
    f : (Σ m ꞉ ℕ , (m < b) × A m × ((n : ℕ) → n < b → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ b) → maximal-element A b
    f (inl x) = x
    f (inr x) = 𝟘-elim (less-not-bigger-or-equal k b (pr₂ a) (x k (pr₁ a)))

  maximal-from-given' : (A : ℕ → 𝓤 ̇) → (b : ℕ) → detachable A → Σ k ꞉ ℕ , A k × k ≤ b → maximal-element' A b
  maximal-from-given' A b δ (k , a , c) = f (bounded-maximisation' A δ b)
   where
    f : (Σ m ꞉ ℕ , (m ≤ b) × A m × ((n : ℕ) → n ≤ b → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n > b) → maximal-element' A b
    f (inr x) = 𝟘-elim (bigger-or-equal-not-less k b c (x k a))
    f (inl x) = x

\end{code}



\begin{code}

 module RNaturalsMultiplication where

  open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) -- TypeTopology
  open import NaturalsAddition -- TypeTopology

  _*_ : (x y : ℕ) → ℕ
  x * 0      = 0
  x * succ y = x + x * y

  infixl 32 _*_

  zero-right-is-zero : (x : ℕ) → x * 0 ≡ 0
  zero-right-is-zero x = refl

  zero-left-is-zero : (x : ℕ) → 0 * x ≡ 0
  zero-left-is-zero = induction refl step
   where
    step : (x : ℕ)
         → 0 * x     ≡ 0
         → 0 + 0 * x ≡ 0
    step x IH = 0 + 0 * x  ≡⟨ ap (0 +_) IH ⟩
                0 + 0      ≡⟨ refl         ⟩
                0          ∎

  zero-left-is-zero' : (x : ℕ) → 0 * x ≡ 0
  zero-left-is-zero' 0        = refl
  zero-left-is-zero' (succ x) = 0 * succ x ≡⟨ refl                             ⟩
                                0 + 0 * x  ≡⟨ ap (0 +_) (zero-left-is-zero' x) ⟩
                                0 + 0      ≡⟨ refl                             ⟩
                                0          ∎

  mult-right-id : (x : ℕ) → x * 1 ≡ x
  mult-right-id x = refl

  mult-left-id : (x : ℕ) → 1 * x ≡ x
  mult-left-id = induction base step
   where
    base : 1 * 0 ≡ 0
    base = refl

    step : (x : ℕ)
         → 1 * x     ≡ x
         → 1 + 1 * x ≡ succ x

    step x IH = 1 + 1 * x  ≡⟨ ap (1 +_) IH        ⟩
                1 + x      ≡⟨ addition-commutativity 1 x ⟩
                x + 1      ≡⟨ refl                       ⟩
                succ x     ∎

  distributivity-mult-over-nat : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
  distributivity-mult-over-nat x y = induction refl step
   where
    step : (k : ℕ)
         → x * (y + k)      ≡ x * y + x * k
         → x * (y + succ k) ≡ x * y + x * succ k

    step k IH = x * (y + succ k)        ≡⟨ refl                                                ⟩
                x + x * (y + k)         ≡⟨ ap (x +_ ) IH                                       ⟩
                x + (x * y + x * k)     ≡⟨ ap (x +_ ) (addition-commutativity (x * y) (x * k)) ⟩ 
                x + (x * k + x * y)     ≡⟨ addition-associativity x (x * k) (x * y) ⁻¹         ⟩
                x + x * k + x * y       ≡⟨ addition-commutativity (x + x * k) (x * y)          ⟩
                x * y + (x + x * k)     ≡⟨ refl                                                ⟩  
                x * y + (x * (succ k))  ∎

  addition-associativity-lemma : (x y u v : ℕ) → x + y + (u + v) ≡ x + y + u + v
  addition-associativity-lemma x y u v = x + y + (u + v) ≡⟨ addition-associativity (x + y) u v ⁻¹ ⟩
                                         x + y + u + v   ∎

  distributivity-mult-over-nat' : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
  distributivity-mult-over-nat' x y = induction refl step
   where
    step : (k : ℕ)
         → (x + y) * k      ≡ x * k + y * k
         → (x + y) * succ k ≡ x * succ k + y * succ k

    step k IH = (x + y) * succ k                  ≡⟨ refl                                                        ⟩
                x + y + (x + y) * k               ≡⟨ ap (x + y +_) IH                                            ⟩
                x + y + (x * k + y * k)           ≡⟨ addition-associativity-lemma x y (x * k) (y * k)            ⟩
                x + y + x * k + y * k             ≡⟨ ap (_+ y * k) (addition-associativity x y (x * k))          ⟩
                x + (y + x * k) + y * k           ≡⟨ ap (λ - → x + - + y * k) (addition-commutativity y (x * k)) ⟩
                x + (x * k + y) + y * k           ≡⟨ ap (_+ y * k) (addition-associativity x (x * k) y) ⁻¹       ⟩
                x + x * k + y + y * k             ≡⟨ addition-associativity (x + x * k) y (y * k)                ⟩ 
                x + x * k + (y + y * k)           ≡⟨ refl                                                        ⟩
                x * succ k + y * succ k           ∎

  mult-commutativity : (x y : ℕ) → x * y ≡ y * x
  mult-commutativity x = induction base step
   where
    base : 0 ≡ 0 * x
    base = zero-left-is-zero x ⁻¹

    step : (k : ℕ)
         → x * k     ≡ k * x
         → x + x * k ≡ succ k * x

    step k IH = x + x * k       ≡⟨ ap (x +_ ) IH                          ⟩
                x + k * x       ≡⟨ ap (_+ k * x) (mult-left-id x ⁻¹)      ⟩
                1 * x + k * x   ≡⟨ distributivity-mult-over-nat' 1 k x ⁻¹ ⟩
                (1 + k) * x     ≡⟨ ap (_* x) (addition-commutativity 1 k) ⟩
                succ k * x ∎

  mult-associativity : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  mult-associativity x y = induction base step
   where
    base : x * y * 0 ≡ x * (y * 0)
    base = x * y * 0   ≡⟨ refl ⟩
           (x * y) * 0 ≡⟨ refl ⟩
           0           ≡⟨ refl ⟩
           y * 0       ≡⟨ refl ⟩
           x * (y * 0) ∎

    step : (k : ℕ)
         → (x * y) * k      ≡ x * (y * k)
         → (x * y) * succ k ≡ x * (y * succ k)

    step k r = (x * y) * succ k          ≡⟨ refl                                        ⟩
               x * y + x * y * k         ≡⟨ ap ((x * y) +_) r                           ⟩
               x * y + x * (y * k)       ≡⟨ distributivity-mult-over-nat x y (y * k) ⁻¹ ⟩
               x * (y + y * k)           ≡⟨ refl                                        ⟩
               x * (y * succ k)          ∎

  mult-rearrangement : (x y z : ℕ) → x * (y * z) ≡ y * (x * z)
  mult-rearrangement x y z = x * (y * z)         ≡⟨ mult-associativity x y z ⁻¹ ⟩
                             x * y * z           ≡⟨ ap (_* z) (mult-commutativity x y) ⟩
                             y * x * z           ≡⟨ mult-associativity y x z ⟩
                             y * (x * z) ∎

  open RMoreNaturalProperties

  pos-mult-is-succ : (x y : ℕ) → Σ z ꞉ ℕ , succ z ≡ succ x * succ y
  pos-mult-is-succ x = induction base step
   where
    base : Σ z ꞉ ℕ , succ z ≡ succ x * 1
    base = x , refl

    step : (k : ℕ)
         → Σ z ꞉ ℕ , succ z ≡ succ x * succ k
         → Σ z' ꞉ ℕ , succ z' ≡ succ x * succ (succ k)
    step k (z , IH) = x + succ z , I
     where
      I : succ (x + succ z) ≡ succ x * succ (succ k)
      I = succ (x + succ z)               ≡⟨ succ-left x (succ z) ⁻¹ ⟩
          succ x + succ z                 ≡⟨ ap (succ x +_) IH ⟩
          succ x + (succ x + succ x * k)  ≡⟨ refl ⟩
          succ x * succ (succ k) ∎

\end{code}

In order to prove that multiplication is cancellable with respect to equality, I first needed to prove that multiplication is cancellable with respect or order of the Natural Numbers.

\begin{code}

  open import NaturalsOrder --TypeTopology
  open RNaturalsOrderExtended

  ordering-multiplication-compatible : (m n k : ℕ) → m < n → m * succ k < n * succ k
  ordering-multiplication-compatible m n = induction base step
   where
    base : m < n
         → succ m < succ n
    base i = i

    step : (k : ℕ)
         → (m < n → m * succ k < n * succ k)
         → m < n
         → m * succ (succ k) < n * succ (succ k)
    step k IH i = <-adding m n (m + m * k) (n + n * k) i (IH i)

  mult-right-cancellable : (x y z : ℕ) → (x * succ z) ≡ (y * succ z) → x ≡ y
  mult-right-cancellable x y z e = tri-split (nat-order-trichotomous x y)
   where
    tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
    tri-split (inl t)       = have less-than-not-equal (x * succ z) (y * succ z) (ordering-multiplication-compatible x y z t) which-contradicts e
    tri-split (inr (inl t)) = t
    tri-split (inr (inr t)) = have less-than-not-equal (y * succ z) (x * succ z) (ordering-multiplication-compatible y x z t) which-contradicts (e ⁻¹)

  mult-left-cancellable : (x y z : ℕ) → succ z * x ≡ succ z * y → x ≡ y
  mult-left-cancellable x y z r = mult-right-cancellable x y z lemma₀
   where
    lemma₀ : x * succ z ≡ y * succ z
    lemma₀ = x * succ z ≡⟨ mult-commutativity x (succ z)  ⟩
             succ z * x ≡⟨ r                              ⟩
             succ z * y ≡⟨ mult-commutativity (succ z) y  ⟩
             y * succ z ∎

  open import UF-Base --TypeTopology

  mult-cancellable : (x y z : ℕ) → (x * succ z ≡ y * succ z)
                                  ∔ (succ z * x ≡ succ z * y)
                                  ∔ (succ z * x ≡ y * succ z)
                                  ∔ (x * succ z ≡ succ z * y)
                                 → x ≡ y
  mult-cancellable x y z (inl e)             = mult-right-cancellable x y z e
  mult-cancellable x y z (inr (inl e))       = mult-right-cancellable x y z (transport₂ (λ k k' → k ≡ k') (mult-commutativity (succ z) x) (mult-commutativity (succ z) y) e)
  mult-cancellable x y z (inr (inr (inl e))) = mult-right-cancellable x y z (transport (_≡ y * succ z) (mult-commutativity (succ z) x) e)
  mult-cancellable x y z (inr (inr (inr e))) = mult-right-cancellable x y z (transport (x * succ z ≡_) (mult-commutativity (succ z) y) e)

  product-less-than-cancellable : (x y z : ℕ) → x * (succ y) ≤ z → x ≤ z
  product-less-than-cancellable x = induction base step
   where
    base : (z : ℕ) → x * 1 ≤ z → x ≤ z
    base z l = l

    step : (k : ℕ)
         → ((z : ℕ) → (x * succ k) ≤ z → x ≤ z)
         → (z : ℕ)
         → x * succ (succ k) ≤ z
         → x ≤ z
    step k IH z l₁ = IH z (≤-trans (x * (succ k)) (x * (succ (succ k))) z I l₁)
     where
      I : (x * succ k) ≤ (x + x * succ k)
      I = ≤-+' x (x * (succ k))

  less-than-pos-mult : (x y z : ℕ) → x < y → x < y * succ z
  less-than-pos-mult x y z l = <-+ x y (y * z) l

  open import NaturalNumbers-Properties --TypeTopology

  ℕ-positive-multiplication-not-zero : (x y : ℕ) → ¬ (succ x * succ y ≡ 0)
  ℕ-positive-multiplication-not-zero x = induction base step
   where
    base : ¬ (succ x * 1 ≡ 0)
    base e = 𝟘-elim (positive-not-zero x e) 

    step : (k : ℕ) → ¬ (succ x * succ k ≡ 0) → ¬ (succ x * succ (succ k) ≡ 0)
    step k IH e = IH I
     where
      I : succ x + succ x * k ≡ 0
      I = sum-to-zero-gives-zero (succ x) (succ x + succ x * k) e

  succ-pred-multiplication : (x y : ℕ) → succ x * succ y ≡ succ (pred (succ x * succ y))
  succ-pred-multiplication x y = succ-pred' (succ x * succ y) (ℕ-positive-multiplication-not-zero x y) ⁻¹

\end{code}

\begin{code}

 module RNaturalsDivision where

  open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆) --TypeTopology
  open import NaturalNumbers-Properties --TypeTopology
  open RNaturalsMultiplication --TypeTopology

  _∣_ : ℕ → ℕ → 𝓤₀ ̇
  x ∣ y = Σ a ꞉ ℕ , (x * a ≡ y)

  open import UF-Miscelanea --TypeTopology
  open import UF-Subsingletons --TypeTopology

  _∣_-is-prop : (x y : ℕ) → is-prop (succ x ∣ y)
  _∣_-is-prop x y (a , p) (b , p') = to-subtype-≡ (λ _ → ℕ-is-set) (mult-left-cancellable a b x (p ∙ p' ⁻¹))

  zero-does-not-divide-positive : (x : ℕ) → ¬(0 ∣ succ x)
  zero-does-not-divide-positive x (a , p) = positive-not-zero x (p ⁻¹ ∙ zero-left-is-zero a)

  open import NaturalsOrder --TypeTopology
  open RNaturalsOrderExtended

  ∣-anti-lemma : (x y z : ℕ) → x < y → x < z → x < y * z
  ∣-anti-lemma x y = induction base step
   where
    base : x < y
         → x < zero
         → x < y * zero
    base _ = id

    step : (k : ℕ)
         → (x < y → x < k → x < y * k)
         → (x < y)
         → (x < succ k)
         → x < y * succ k
    step k IH l₁ _ = <-+ x y (y * k) l₁

  product-one-gives-one : (x y : ℕ) → x * y ≡ 1 → x ≡ 1
  product-one-gives-one x y r = tri-split (nat-order-trichotomous x 1)
   where
    tri-split : (x < 1) ∔ (x ≡ 1) ∔ (1 < x) → x ≡ 1
    tri-split (inl z) = have succ-no-fp 0 which-contradicts I
      where
        I : 0 ≡ 1
        I = 0     ≡⟨ zero-left-is-zero y ⁻¹                    ⟩
            0 * y ≡⟨ ap (_* y) (less-than-one-is-zero x z ⁻¹ ) ⟩
            x * y ≡⟨ r                                         ⟩
            1     ∎

    tri-split (inr (inl z)) = z
    tri-split (inr (inr z)) = tri-split' (nat-order-trichotomous y 1)
     where
      tri-split' : (y < 1) ∔ (y ≡ 1) ∔ (1 < y) → x ≡ 1
      tri-split' (inl z')       = have succ-no-fp 0 which-contradicts I
       where
        I : 0 ≡ 1
        I = 0     ≡⟨ zero-right-is-zero x ⁻¹                    ⟩
            x * 0 ≡⟨ ap (x *_) (less-than-one-is-zero y z' ⁻¹)  ⟩
            x * y ≡⟨ r                                          ⟩
            1     ∎

      tri-split' (inr (inl z')) = have less-than-not-equal 1 x z which-contradicts I
       where
        I : 1 ≡ x
        I = 1     ≡⟨ r ⁻¹         ⟩
            x * y ≡⟨ ap (x *_) z' ⟩
            x     ∎
      tri-split' (inr (inr z')) = have I which-contradicts (r ⁻¹)
       where
        I : 1 ≡ x * y → 𝟘
        I = less-than-not-equal 1 (x * y) (∣-anti-lemma 1 x y z z')

  ∣-anti : (x y : ℕ) → x ∣ y → y ∣ x → x ≡ y
  ∣-anti 0        y (a , p) (b , q) = δ
   where
    δ : zero ≡ y
    δ = zero     ≡⟨ zero-left-is-zero a ⁻¹ ⟩
        zero * a ≡⟨ p                      ⟩
        y        ∎ 
  ∣-anti (succ x) y (a , p) (b , q) = δ
   where
    a*b-is-one : a * b ≡ 1
    a*b-is-one = mult-left-cancellable (a * b) 1 x I
     where
      I : succ x * (a * b) ≡ succ x * 1
      I = succ x * (a * b) ≡⟨ mult-associativity (succ x) a b ⁻¹ ⟩
          succ x * a * b   ≡⟨ ap (_* b) p                        ⟩
          y * b            ≡⟨ q                                  ⟩
          succ x           ≡⟨ refl ⟩
          succ x * 1       ∎

    b-is-1 : b ≡ 1
    b-is-1 = product-one-gives-one b a I
     where
      I : b * a ≡ 1
      I = b * a ≡⟨ mult-commutativity b a ⟩
          a * b ≡⟨ a*b-is-one             ⟩
          1     ∎                              

    δ : succ x ≡ y
    δ = succ x ≡⟨ q ⁻¹             ⟩
        y * b  ≡⟨ ap (y *_) b-is-1 ⟩
        y      ∎

  open import NaturalsAddition --TypeTopology

  ∣-respects-addition : (x y z : ℕ) → x ∣ y → x ∣ z → x ∣ (y + z)
  ∣-respects-addition x y z (a , p) (b , q) = (a + b , I)
   where
    I : x * (a + b) ≡ y + z
    I = x * (a + b)   ≡⟨ distributivity-mult-over-nat x a b ⟩
        x * a + x * b ≡⟨ ap (_+ x * b) p                    ⟩
        y + x * b     ≡⟨ ap (y +_) q                        ⟩
        y + z         ∎

  open import UF-Base --TypeTopology

  ∣-respects-multiples : (a b c k l : ℕ) → a ∣ b → a ∣ c → a ∣ (k * b + l * c)
  ∣-respects-multiples a b c k l (x , p) (y , q) = (k * x + l * y , I)
   where
    I : a * (k * x + l * y) ≡ k * b + l * c
    I = a * (k * x + l * y)       ≡⟨ distributivity-mult-over-nat a (k * x) (l * y)                                     ⟩
        a * (k * x) + a * (l * y) ≡⟨ ap₂ _+_ (ap (a *_) (mult-commutativity k x)) (ap (a *_) (mult-commutativity l y))  ⟩
        a * (x * k) + a * (y * l) ≡⟨ ap₂ _+_ (mult-associativity a x k ⁻¹) (mult-associativity a y l ⁻¹)                ⟩
        (a * x) * k + (a * y) * l ≡⟨ ap₂ _+_ (ap (_* k) p) (ap (_* l) q)                                                ⟩
        b * k + c * l             ≡⟨ ap₂ _+_ (mult-commutativity b k) (mult-commutativity c l)                          ⟩
        k * b + l * c             ∎                                                                                      

  ∣-trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
  ∣-trans a b c (x , p) (y , q) = (x * y) , I
   where
    I : a * (x * y) ≡ c
    I = a * (x * y)  ≡⟨ mult-associativity a x y ⁻¹ ⟩
        (a * x) * y  ≡⟨ ap ( _* y) p                ⟩
        b * y        ≡⟨ q                           ⟩
        c            ∎

  ∣-divisor-divides-multiple : (a b k : ℕ) → a ∣ b → a ∣ k * b
  ∣-divisor-divides-multiple a b k (x , p) = (x * k) , I
   where
    I : a * (x * k) ≡ k * b
    I = a * (x * k) ≡⟨ mult-associativity a x k ⁻¹ ⟩
        a * x * k   ≡⟨ ap (_* k) p                 ⟩
        b * k       ≡⟨ mult-commutativity b k ⟩
        k * b       ∎

  divisiontheorem : (a d : ℕ) → 𝓤₀ ̇
  divisiontheorem a d = Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * d + r) × (r < d)

  open RMoreNaturalProperties

  division : (a d : ℕ) → divisiontheorem a (succ d)
  division a d = induction base step a
   where
    base : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (0 ≡ q * succ d + r) × (r < succ d)  
    base = 0 , (0 , (I , II))
     where
      I : 0 ≡ 0 * succ d + 0
      I = 0         ≡⟨ refl                               ⟩
          0 + 0     ≡⟨ ap (0 +_) (zero-left-is-zero d ⁻¹) ⟩
          0 + 0 * d ∎

      II : 0 < succ d
      II = unique-to-𝟙 (0 < succ d)

    step : (k : ℕ)
         → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (k ≡ q * succ d + r) × (r < succ d)
         → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
    step k (q , r , e , l) = helper (<-split r d l)
     where
      helper : (r < d) ∔ (r ≡ d) →  Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
      helper (inl x) = q , succ r , ap succ e , x
      helper (inr x) = succ q , 0 , I , unique-to-𝟙 (0 < succ d)
       where
        I : succ k ≡ succ q + succ q * d
        I = succ k                        ≡⟨ ap succ e                                           ⟩
            succ (q + q * d + r)          ≡⟨ ap succ (ap (q + q * d +_) x)                       ⟩
            succ (q + q * d + d)          ≡⟨ ap succ (addition-associativity q (q * d) d)        ⟩
            succ (q + (q * d + d))        ≡⟨ succ-left q (q * d + d) ⁻¹                          ⟩
            succ q + (q * d + d)          ≡⟨ ap (succ q +_) (ap (_+ d) (mult-commutativity q d)) ⟩
            succ q + (d * q + d)          ≡⟨ ap (succ q +_) (addition-commutativity (d * q) d)   ⟩ 
            succ q + (d + d * q)          ≡⟨ ap (succ q +_) (mult-commutativity d (succ q))      ⟩ 
            succ q + succ q * d           ∎

  division-is-prop-lemma : (a b c : ℕ) → a ≤ b → b < c → a < c
  division-is-prop-lemma a b c l₀ l₁ = ≤-trans (succ a) (succ b) c l₀ l₁

  division-is-prop : (a d : ℕ) → is-prop (divisiontheorem a d)
  division-is-prop a d (q₀ , r₀ , α , αₚ) (q₁ , r₁ , β , βₚ) = to-subtype-≡ I II
   where
    I : (q : ℕ) → is-prop (Σ r ꞉ ℕ , (a ≡ q * d + r) × (r < d))
    I q (r₀ , δ) (r₁ , γ) = to-subtype-≡ (λ r → ×-is-prop ℕ-is-set (<-is-prop-valued r d)) remainders-equal
     where
      remainders-equal : r₀ ≡ r₁
      remainders-equal = addition-left-cancellable r₀ r₁ (q * d) i
       where
        i : q * d + r₀ ≡ q * d + r₁
        i = q * d + r₀ ≡⟨ pr₁ δ ⁻¹ ⟩
            a          ≡⟨ pr₁ γ ⟩
            q * d + r₁ ∎

    assumption : q₀ * d + r₀ ≡ q₁ * d + r₁
    assumption = α ⁻¹ ∙ β

    II-abstract : (q q' r r' : ℕ) → q * d + r ≡ q' * d + r' → q < q' → r < d → q ≡ q'
    II-abstract q q' r r' e l₁ l₂ = 𝟘-elim (not-less-than-itself (d * succ k) vii)
     where
      i : Σ k ꞉ ℕ , (succ k) + q ≡ q'
      i = subtraction'' q q' l₁

      k : ℕ
      k = pr₁ i

      μ : (succ k) + q ≡ q'
      μ = pr₂ i

      ii : q * d + r ≡ q * d + ((succ k) * d + r')
      ii = q * d + r                   ≡⟨ e ⟩
           q' * d + r'                 ≡⟨ ap (λ - → - * d + r') (μ ⁻¹) ⟩
           ((succ k) + q) * d + r'     ≡⟨ ap (_+ r') (distributivity-mult-over-nat' (succ k) q d) ⟩
           (succ k) * d + q * d + r'   ≡⟨ ap (_+ r') (addition-commutativity ((succ k) * d) (q * d)) ⟩
           q * d + (succ k) * d + r'   ≡⟨ addition-associativity (q * d) ((succ k) * d) r' ⟩
           q * d + ((succ k) * d + r') ∎

      iii : r' + d * (succ k) ≡ r
      iii = r' + d * succ k         ≡⟨ ap (r' +_) (mult-commutativity d (succ k)) ⟩
            r' + (succ k) * d       ≡⟨ addition-commutativity r' ((succ k) * d) ⟩
            (succ k) * d + r'       ≡⟨ addition-left-cancellable r ((succ k) * d + r') (q * d) ii ⁻¹ ⟩ 
            r                       ∎

      iv : d * (succ k) ≤ r
      iv = cosubtraction (d * succ k) r (r' , iii)

      v : r < d * succ k
      v = less-than-pos-mult r d k l₂

      vii : d * succ k < d * succ k
      vii = division-is-prop-lemma (d * succ k) r (d * succ k) iv v

    II : q₀ ≡ q₁
    II = f (nat-order-trichotomous q₀ q₁)
     where
      f : (q₀ < q₁) ∔ (q₀ ≡ q₁) ∔ (q₁ < q₀) → q₀ ≡ q₁
      f (inl z)       = II-abstract q₀ q₁ r₀ r₁ assumption z αₚ
      f (inr (inl z)) = z
      f (inr (inr z)) = II-abstract q₁ q₀ r₁ r₀ (assumption ⁻¹) z βₚ ⁻¹

\end{code}

I re-implemented division using Bounded Maximisation once I had more experience with Agda. Using the proof that the division theorem is a proposition, it is trivial to show that the two different algorithms for division are pointwise equal.

\begin{code}

  division' : (a d : ℕ) → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * (succ d) + r) × (r < (succ d))
  division' 0 d     = 0 , (0 , (I , II))
   where
    I : 0 ≡ 0 * succ d + 0
    I = 0         ≡⟨ refl                               ⟩
        0 + 0     ≡⟨ ap (0 +_) (zero-left-is-zero d ⁻¹) ⟩
        0 + 0 * d ∎

    II : 0 < succ d
    II = unique-to-𝟙 (0 < succ d)
  division' (succ a) d = f (maximal-from-given' (λ - → - * succ d ≤ succ a) (succ a) (λ q → ≤-decidable (q * succ d) (succ a)) ii)
   where
    i : (0 + 0 * d) ≤ succ a
    i = transport (_≤ succ a) (zero-left-is-zero (succ d) ⁻¹) (zero-minimal (succ a))

    ii : Σ k ꞉ ℕ , (k * succ d ≤ succ a) × (k ≤ succ a)
    ii = 0 , i , zero-minimal (succ a)

    f : Σ q ꞉ ℕ , q ≤ succ a × (q * succ d) ≤ succ a × ((n : ℕ) → n ≤ succ a → n * succ d ≤ succ a → n ≤ q)
      → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
    f (q , l₁ , l₂ , qf) = g (subtraction (q * succ d) (succ a) l₂)
     where
      g : Σ r ꞉ ℕ , r + q * succ d ≡ succ a
        → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
      g (r , rf) = q , r , I , II (order-split r (succ d))
       where
        I : succ a ≡ q * succ d + r
        I = succ a         ≡⟨ rf ⁻¹                                 ⟩
            r + q * succ d ≡⟨ addition-commutativity r (q * succ d) ⟩
            q * succ d + r ∎

        II : r < succ d ∔ r ≥ succ d → r < succ d
        II (inl z) = z
        II (inr z) = 𝟘-elim (not-less-than-itself q IV)
         where
          III : succ q * succ d ≤ succ a
          III = transport₂ _≤_ α (addition-commutativity (q * succ d) r ∙ rf) β
           where
            α : q * succ d + succ d ≡ succ q * succ d
            α = q * succ d + succ d     ≡⟨ ap (q * succ d +_) (mult-left-id (succ d) ⁻¹) ⟩
                q * succ d + 1 * succ d ≡⟨ distributivity-mult-over-nat' q 1 (succ d) ⁻¹ ⟩
                (q + 1) * succ d        ≡⟨ refl ⟩
                succ q * succ d ∎

            β : q * succ d + succ d ≤ q * succ d + r
            β = ≤-n-monotone-left (succ d) r (q * succ d) z

          IV : q < q
          IV = qf (succ q) (product-less-than-cancellable (succ q) d (succ a) III) III

  division-agrees-with-division' : (x y : ℕ) → division x y ≡ division' x y
  division-agrees-with-division' a d = division-is-prop a (succ d) (division a d) (division' a d)

\end{code}

\begin{code}

 module RHCF where

  open import NaturalNumbers-Properties --TypeTopology
  open import UF-Subsingletons --TypeTopology

  open RNaturalsDivision

  is-common-divisor : (d x y : ℕ) → 𝓤₀ ̇
  is-common-divisor d x y = (d ∣ x) × (d ∣ y)

  is-common-divisor-is-prop : (d x y : ℕ) → is-prop (is-common-divisor (succ d) x y)
  is-common-divisor-is-prop d x y = ×-is-prop (d ∣ x -is-prop) (d ∣ y -is-prop)

  is-hcf : (d x y : ℕ) → 𝓤₀ ̇
  is-hcf d x y = (is-common-divisor d x y) × ((f : ℕ) →  is-common-divisor f x y → f ∣ d)

  is-hcf-gives-is-common-divisor : (d x y : ℕ) → is-hcf d x y → is-common-divisor d x y
  is-hcf-gives-is-common-divisor d x y (a , p) = a

  open import UF-FunExt
  open import UF-Subsingletons-FunExt

  is-hcf-is-prop : Fun-Ext → (d x y : ℕ) → is-prop (is-hcf (succ d) x y)
  is-hcf-is-prop fe d x y p q = ×-is-prop (is-common-divisor-is-prop d x y) g p q
    where
      h : (f : ℕ) → is-common-divisor f x y → is-prop (f ∣ succ d)
      h 0        i x = 𝟘-elim (zero-does-not-divide-positive d x)
      h (succ f) i   = f ∣ (succ d) -is-prop

      g : is-prop ((f : ℕ) → is-common-divisor f x y → f ∣ succ d)
      g p' q' = Π₂-is-prop fe h p' q'

  has-hcf : (x y : ℕ) → 𝓤₀ ̇
  has-hcf x y = Σ d ꞉ ℕ , is-hcf (succ d) x y

  has-hcf-is-prop : Fun-Ext → (x y : ℕ) → is-prop (has-hcf x y)
  has-hcf-is-prop fe x y (a , p , p') (b , q , q') = to-subtype-≡ I II
   where
    I : (d : ℕ) → is-prop (is-hcf (succ d) x y)
    I d = is-hcf-is-prop fe d x y

    II : a ≡ b
    II = succ-lc (∣-anti (succ a) (succ b) α β)
     where
      α : succ a ∣ succ b
      α = q' (succ a) p

      β : succ b ∣ succ a
      β = p' (succ b) q

  open import NaturalsAddition --TypeTopology
  open import NaturalsOrder --TypeTopoology

  open RMoreNaturalProperties
  open RNaturalsMultiplication
  open RNaturalsOrderExtended

  hcflemma : (a b c d : ℕ) → a * b ≡ a * c + d → a ∣ d
  hcflemma a b c d e = subtraction-gives-factor (dichotomy-split (≥-dichotomy b c))
   where
    dichotomy-split : b ≥ c ∔ b ≤ c → (Σ f ꞉ ℕ , f + c ≡ b) ∔ (Σ f ꞉ ℕ , f + b ≡ c)
    dichotomy-split (inl x) = inl (subtraction c b x)
    dichotomy-split (inr x) = inr (subtraction b c x)

    subtraction-gives-factor : (Σ f ꞉ ℕ , f + c ≡ b) ∔ (Σ f ꞉ ℕ , f + b ≡ c) → a ∣ d
    subtraction-gives-factor (inl (f , p)) = f , addition-left-cancellable (a * f) d (a * c) I
     where
      I : a * c + a * f ≡ a * c + d
      I = a * c + a * f ≡⟨ distributivity-mult-over-nat a c f ⁻¹  ⟩
          a * (c + f)   ≡⟨ ap (a *_) (addition-commutativity c f) ⟩
          a * (f + c)   ≡⟨ ap (a *_) p                            ⟩
          a * b         ≡⟨ e                                      ⟩
          a * c + d ∎
    subtraction-gives-factor (inr (f , p)) = 0 , (sum-to-zero-gives-zero (a * f) d II ⁻¹)
     where
      I : a * f + d + a * b ≡ 0 + a * b
      I = a * f + d + a * b ≡⟨ trivial-addition-rearrangement (a * f) d (a * b)         ⟩
          a * f + a * b + d ≡⟨ ap (λ z → z + d) (distributivity-mult-over-nat a f b ⁻¹) ⟩
          a * (f + b) + d   ≡⟨ ap (λ z → a * z + d) p                                   ⟩
          a * c + d         ≡⟨ e ⁻¹                                                     ⟩
          a * b             ≡⟨ zero-left-neutral (a * b) ⁻¹                             ⟩
          0 + a * b         ∎

      II : a * f + d ≡ 0
      II = addition-right-cancellable (a * f + d) 0 (a * b) I

  HCF : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
  HCF = course-of-values-induction (λ n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h n b) step
   where
    step : (n : ℕ) → ((m : ℕ) → m < n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h m b) → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h n b
    step zero IH b = b , ((zero , refl) , 1 , refl) , (λ x → pr₂)
    step (succ n) IH b = I (division b n)
     where
      I : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (b ≡ q * succ n + r) × (r < succ n) → Σ h ꞉ ℕ , is-hcf h (succ n) b
      I (q , r , e₀ , l) = II (IH r l (succ n))
       where
        II : Σ h ꞉ ℕ , is-hcf h r (succ n) → Σ h ꞉ ℕ , is-hcf h (succ n) b
        II (h , ((x , xₚ) , y , yₚ) , γ) = h , ((y , yₚ) , i) , ii
         where
          i : h ∣ b
          i = (q * y + x) , e₁
           where
            e₁ : h * (q * y + x) ≡ b
            e₁ = h * (q * y + x)         ≡⟨ distributivity-mult-over-nat h (q * y) x      ⟩ 
                 h * (q * y) + h * x     ≡⟨ ap (λ z → h * (q * y) + z) xₚ                 ⟩
                 h * (q * y) + r         ≡⟨ ap (_+ r) (mult-associativity h q y) ⁻¹       ⟩
                 h * q * y + r           ≡⟨ ap (λ z → z * y + r) (mult-commutativity h q) ⟩
                 q * h * y + r           ≡⟨ ap (_+ r) (mult-associativity q h y)          ⟩
                 q * (h * y) + r         ≡⟨ ap (λ z → q * z + r) yₚ                       ⟩
                 q * succ n + r          ≡⟨ e₀ ⁻¹ ⟩
                 b                       ∎

          ii : (f : ℕ) → is-common-divisor f (succ n) b → f ∣ h
          ii f ((α , αₚ) , β , βₚ) = γ f ((hcflemma f β (q * α) r e₂) , (α , αₚ))
           where
            e₂ : f * β ≡ f * (q * α) + r
            e₂ = f * β           ≡⟨ βₚ                                             ⟩
                 b               ≡⟨ e₀                                             ⟩
                 q * succ n + r  ≡⟨ ap (λ z → q * z + r) (αₚ ⁻¹)                  ⟩
                 q * (f * α) + r ≡⟨ ap (_+ r) (mult-associativity q f α ⁻¹)       ⟩
                 q * f * α + r   ≡⟨ ap (λ z → z * α + r) (mult-commutativity q f) ⟩
                 f * q * α + r   ≡⟨ ap (_+ r ) (mult-associativity f q α)         ⟩
                 f * (q * α) + r ∎

  hcf : (a b : ℕ) → ℕ
  hcf a b = pr₁ (HCF a b)

  coprime : (a b : ℕ) → 𝓤₀ ̇
  coprime a b = is-hcf 1 a b

  coprime-is-prop : Fun-Ext → (a b : ℕ) → is-prop (coprime a b)
  coprime-is-prop fe a b = is-hcf-is-prop fe zero a b

  divbyhcf : (a b : ℕ) → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ≡ a) × (h * y ≡ b)) × coprime x y
  divbyhcf zero     b = b , (zero , (1 , ((refl , refl) , ((zero , refl) , 1 , refl) , (λ x → pr₂))))
  divbyhcf (succ a) b = I (HCF (succ a) b)
   where
    I : Σ c ꞉ ℕ , is-hcf c (succ a) b → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ≡ (succ a)) × (h * y ≡ b)) × coprime x y 
    I (zero , ((x , xₚ) , y , yₚ) , γ) = have positive-not-zero a which-contradicts II
     where
      II : succ a ≡ 0
      II = succ a  ≡⟨ xₚ ⁻¹                     ⟩
           0 * x   ≡⟨ mult-commutativity zero x ⟩
           0       ∎
    I (succ h , ((x , xₚ) , y , yₚ) , γ) = (succ h) , (x , (y , ((xₚ , yₚ) , (((x , mult-commutativity 1 x) , y , (mult-commutativity 1 y)) , II))))
     where
      II : (f' : ℕ) → is-common-divisor f' x y → f' ∣ 1
      II f' ((α , αₚ) , β , βₚ) = III (γ (succ h * f') ((α , αₚ') , β , βₚ'))
       where
        αₚ' : succ h * f' * α ≡ succ a
        αₚ' = succ h * f' * α     ≡⟨ mult-associativity (succ h) f' α ⟩
              succ h * (f' * α)   ≡⟨ ap (succ h *_) αₚ                ⟩
              succ h * x          ≡⟨ xₚ                               ⟩
              succ a              ∎

        βₚ' : succ h * f' * β ≡ b
        βₚ' = succ h * f' * β   ≡⟨ mult-associativity (succ h) f' β ⟩
              succ h * (f' * β) ≡⟨ ap (succ h *_) βₚ                ⟩
              succ h * y        ≡⟨ yₚ                               ⟩
              b                 ∎

        III : (succ h) * f' ∣ (succ h) → f' ∣ 1
        III (δ , δₚ) = 1 , product-one-gives-one f' δ (mult-left-cancellable (f' * δ) 1 h e)
         where
          e : succ h * (f' * δ) ≡ succ h * 1
          e = succ h * (f' * δ) ≡⟨ mult-associativity (succ h) f' δ ⁻¹ ⟩
              succ h * f' * δ   ≡⟨ δₚ ⟩
              succ h            ∎

  hcf-unique : (a b : ℕ) → ((h , p) : Σ h ꞉ ℕ , is-hcf h a b) → ((h' , p') : Σ h' ꞉ ℕ , is-hcf h' a b) → h ≡ h'
  hcf-unique a b (h , h-icd , f) (h' , h'-icd , f') = ∣-anti h h' I II
   where
    I : h ∣ h'
    I = f' h h-icd

    II : h' ∣ h
    II = f h' h'-icd

\end{code}

\begin{code}
 module RIntegers where
  data ℤ : 𝓤₀ ̇ where 
   pos     : ℕ → ℤ
   negsucc : ℕ → ℤ

  predℤ : ℤ → ℤ
  predℤ (pos 0)        = negsucc 0
  predℤ (pos (succ x)) = pos x
  predℤ (negsucc x)    = negsucc (succ x)

  succℤ : ℤ → ℤ
  succℤ (pos x)            = pos (succ x)
  succℤ (negsucc 0)        = pos 0
  succℤ (negsucc (succ x)) = negsucc x

  ℤ-induction : {A : ℤ → 𝓤 ̇} → A (pos 0)
                               → ((k : ℤ) → A k → A (succℤ k))
                               → ((k : ℤ) → A (succℤ k) → A k)
                               → (x : ℤ)
                               → A x 
  ℤ-induction base step₀ step₁ (pos 0)            = base
  ℤ-induction base step₀ step₁ (pos (succ x))     = step₀ (pos x) (ℤ-induction base step₀ step₁ (pos x))
  ℤ-induction base step₀ step₁ (negsucc 0)        = step₁ (negsucc 0) base
  ℤ-induction base step₀ step₁ (negsucc (succ x)) = step₁ (negsucc (succ x)) (ℤ-induction base step₀ step₁ (negsucc x))

  succpredℤ : (x : ℤ) → succℤ (predℤ x) ≡ x 
  succpredℤ (pos 0)        = refl
  succpredℤ (pos (succ x)) = refl
  succpredℤ (negsucc x)    = refl

  predsuccℤ : (x : ℤ) → predℤ (succℤ x) ≡ x 
  predsuccℤ (pos x)            = refl
  predsuccℤ (negsucc 0)        = refl
  predsuccℤ (negsucc (succ x)) = refl

  -_ : ℤ → ℤ
  -_ (pos 0)        = pos 0
  -_ (pos (succ x)) = negsucc x
  -_ (negsucc x)    = pos (succ x)

  infix 30 -_

  predminus : (x : ℤ) → predℤ (- x) ≡ (- succℤ x)
  predminus (pos 0)            = refl
  predminus (pos (succ x))     = refl
  predminus (negsucc 0)        = refl
  predminus (negsucc (succ x)) = refl

  abs : ℤ → ℕ
  abs (pos x)     = x
  abs (negsucc x) = succ x

  absℤ : ℤ → ℤ
  absℤ (pos x)     = pos x
  absℤ (negsucc x) = pos (succ x)

  _+pos_ : ℤ → ℕ → ℤ 
  x +pos 0      = x
  x +pos succ y = succℤ (x +pos y)

  _+negsucc_ : ℤ → ℕ → ℤ 
  x +negsucc 0      = predℤ x
  x +negsucc succ y = predℤ (x +negsucc y)

  open import NaturalsAddition renaming (_+_ to _ℕ+_)

  _+_ : ℤ → ℤ → ℤ 
  x + pos y     = x +pos y
  x + negsucc y = x +negsucc y

  infixl 31 _+_

  _*_ : ℤ → ℤ → ℤ
  x * pos 0            = pos 0
  x * pos (succ y)     = x + (x * pos y)
  x * negsucc 0        = - x
  x * negsucc (succ y) = (- x) + (x * negsucc y)

  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)

  infixl 32 _*_

  _-_ : ℤ → ℤ → ℤ 
  x - pos 0        = x + (- pos 0)
  x - pos (succ y) = x + (- pos (succ y))
  x - negsucc y    = x + (- negsucc y)

  positive : ℤ → 𝓤₀ ̇
  positive (pos x)     = 𝟙
  positive (negsucc x) = 𝟘

  negative : ℤ → 𝓤₀ ̇
  negative (pos x)     = 𝟘
  negative (negsucc x) = 𝟙

  is-zero : ℤ → 𝓤₀ ̇
  is-zero (pos 0)        = 𝟙
  is-zero (pos (succ x)) = 𝟘
  is-zero (negsucc x)    = 𝟘

  not-zero : ℤ → 𝓤₀ ̇
  not-zero z = ¬ (is-zero z)

  greater-than-zero : ℤ → 𝓤₀ ̇
  greater-than-zero (pos 0)        = 𝟘
  greater-than-zero (pos (succ z)) = 𝟙
  greater-than-zero (negsucc z)    = 𝟘
\end{code}

\begin{code}

 module RIntegersProperties where

  open RIntegers

  pos-lc : {x y : ℕ} → pos x ≡ pos y → x ≡ y
  pos-lc = ap abs

  open import NaturalNumbers-Properties renaming (pred to ℕpred) -- TypeTopology

  negsuc-lc : {x y : ℕ} → negsucc x ≡ negsucc y → x ≡ y
  negsuc-lc {x} {y} p = succ-lc (ap abs p)

  ℤ-left-succ-pos : (x : ℤ) → (y : ℕ) → succℤ x +pos y ≡ succℤ (x +pos y)  --cubical
  ℤ-left-succ-pos x 0        = refl
  ℤ-left-succ-pos x (succ y) = ap succℤ (ℤ-left-succ-pos x y)

  ℤ-left-pred-pos : (x : ℤ) → (y : ℕ) → predℤ x +pos y ≡ predℤ (x +pos y) --cubical
  ℤ-left-pred-pos x 0        = refl
  ℤ-left-pred-pos x (succ y) = succℤ (predℤ x +pos y)       ≡⟨ ℤ-left-succ-pos (predℤ x) y ⁻¹ ⟩
                                (succℤ (predℤ x) +pos y)    ≡⟨ ap (_+pos y) (succpredℤ x)     ⟩
                                x +pos y                    ≡⟨ predsuccℤ (x +pos y) ⁻¹        ⟩
                                predℤ (succℤ (x +pos y))    ∎

  ℤ-left-pred-negsucc : (x : ℤ) → (y : ℕ) → predℤ x +negsucc y ≡ predℤ (x +negsucc y) 
  ℤ-left-pred-negsucc x 0        = refl
  ℤ-left-pred-negsucc x (succ y) = ap predℤ (ℤ-left-pred-negsucc x y)

  ℤ-left-succ-negsucc : (x : ℤ) → (y : ℕ) → succℤ x +negsucc y ≡ succℤ (x +negsucc y) --cubical agda
  ℤ-left-succ-negsucc x 0        = predsuccℤ x ∙ succpredℤ x ⁻¹
  ℤ-left-succ-negsucc x (succ y) = (succℤ x +negsucc succ y)             ≡⟨ ℤ-left-pred-negsucc (succℤ x) y ⁻¹  ⟩
                                   (predℤ (succℤ x) +negsucc y)          ≡⟨ ap (_+ (negsucc y)) (predsuccℤ x)   ⟩
                                   (x + negsucc y)                       ≡⟨ succpredℤ (x +negsucc y) ⁻¹         ⟩
                                   succℤ (x +negsucc succ y)             ∎

  ℤ-right-succ : (x y : ℤ) → x + succℤ y ≡ succℤ (x + y)
  ℤ-right-succ x (pos y)            = refl
  ℤ-right-succ x (negsucc 0)        = succpredℤ x ⁻¹
  ℤ-right-succ x (negsucc (succ y)) = succpredℤ (x +negsucc y) ⁻¹

  ℤ-left-succ : (x y : ℤ) → succℤ x + y ≡ succℤ (x + y)
  ℤ-left-succ x (pos y)     = ℤ-left-succ-pos x y
  ℤ-left-succ x (negsucc y) = ℤ-left-succ-negsucc x y

  ℤ-left-pred : (x y : ℤ) → predℤ x + y ≡ predℤ (x + y)
  ℤ-left-pred x (pos y)     = ℤ-left-pred-pos x y
  ℤ-left-pred x (negsucc y) = ℤ-left-pred-negsucc x y

  ℤ-right-pred : (x y : ℤ) → x + predℤ y ≡ predℤ (x + y)
  ℤ-right-pred x (pos 0)        = refl
  ℤ-right-pred x (pos (succ y)) = predsuccℤ (x +pos y) ⁻¹
  ℤ-right-pred x (negsucc y)    = refl

  ℤ-zero-right-neutral : (x : ℤ) → x + pos 0 ≡ x
  ℤ-zero-right-neutral x = refl

  ℤ-zero-left-neutral : (x : ℤ) → pos 0 + x ≡ x
  ℤ-zero-left-neutral (pos 0)            = refl
  ℤ-zero-left-neutral (pos (succ x))     = ap succℤ (ℤ-zero-left-neutral (pos x))
  ℤ-zero-left-neutral (negsucc 0)        = refl
  ℤ-zero-left-neutral (negsucc (succ x)) = ap predℤ (ℤ-zero-left-neutral (negsucc x))

  ℤ-pred-is-minus-one : (x : ℤ) → predℤ x ≡ negsucc 0 + x
  ℤ-pred-is-minus-one (pos 0)            = refl
  ℤ-pred-is-minus-one (pos (succ x))     = predℤ (pos (succ x))      ≡⟨ succpredℤ (pos x) ⁻¹                   ⟩
                                           succℤ (predℤ (pos x))     ≡⟨ ap succℤ (ℤ-pred-is-minus-one (pos x)) ⟩
                                           negsucc 0 + pos (succ x)  ∎
  ℤ-pred-is-minus-one (negsucc 0)        = refl
  ℤ-pred-is-minus-one (negsucc (succ x)) = predℤ (negsucc (succ x))      ≡⟨ ap predℤ (ℤ-pred-is-minus-one (negsucc x)) ⟩
                                           predℤ (negsucc 0 + negsucc x) ∎

  succℤ-lc : {x y : ℤ} → succℤ x ≡ succℤ y → x ≡ y
  succℤ-lc {x} {y} p = x               ≡⟨ predsuccℤ x ⁻¹ ⟩
                       predℤ (succℤ x) ≡⟨ ap predℤ p     ⟩
                       predℤ (succℤ y) ≡⟨ predsuccℤ y    ⟩
                       y               ∎

  predℤ-lc : {x y : ℤ} →  predℤ x ≡ predℤ y → x ≡ y
  predℤ-lc {x} {y} p = x               ≡⟨ succpredℤ x ⁻¹ ⟩
                       succℤ (predℤ x) ≡⟨ ap succℤ p     ⟩
                       succℤ (predℤ y) ≡⟨ succpredℤ y    ⟩
                       y               ∎

  ℤ+-comm : (x y : ℤ) → x + y ≡ y + x
  ℤ+-comm x = ℤ-induction base step₁ step₂
   where
    base : x ≡ (pos 0 + x)
    base = ℤ-zero-left-neutral x ⁻¹

    step₁ : (k : ℤ)
          → x + k         ≡ k + x
          → x + succℤ k   ≡ succℤ k + x
    step₁ k IH = x + succℤ k   ≡⟨ ℤ-right-succ x k   ⟩
                 succℤ (x + k) ≡⟨ ap succℤ IH        ⟩
                 succℤ (k + x) ≡⟨ ℤ-left-succ k x ⁻¹ ⟩
                 succℤ k + x   ∎ 

    step₂ : (k : ℤ)
          → x + succℤ k ≡ succℤ k + x
          → x + k       ≡ k + x
    step₂ k IH = succℤ-lc I
     where
      I : succℤ (x + k) ≡ succℤ (k + x)
      I = succℤ (x + k) ≡⟨ ℤ-right-succ x k ⁻¹ ⟩
          x + succℤ k   ≡⟨ IH                  ⟩
          succℤ k + x   ≡⟨ ℤ-left-succ k x     ⟩
          succℤ (k + x) ∎

  ℤ+-assoc : (a b c : ℤ) → (a + b) + c ≡ a + (b + c)
  ℤ+-assoc a b = ℤ-induction base step₁ step₂
   where
    base : (a + b) + pos 0 ≡ a + (b + pos 0)
    base = refl

    step₁ : (k : ℤ)
          → (a + b) + k       ≡ a + (b + k)
          → (a + b) + succℤ k ≡ a + (b + succℤ k)
    step₁ k IH = (a + b) + succℤ k   ≡⟨ ℤ-right-succ (a + b) k           ⟩
                 succℤ ((a + b) + k) ≡⟨ ap succℤ IH                     ⟩
                 succℤ (a + (b + k)) ≡⟨ ℤ-right-succ a (b + k) ⁻¹       ⟩
                 a + succℤ (b + k)   ≡⟨ ap (a +_) (ℤ-right-succ b k ⁻¹) ⟩
                 a + (b + succℤ k)   ∎

    step₂ : (k : ℤ)
          → (a + b) + succℤ k ≡ a + (b + succℤ k)
          → (a + b) + k       ≡ a + (b + k)
    step₂ k IH = succℤ-lc I
     where
      I : succℤ (a + b + k) ≡ succℤ (a + (b + k))
      I = succℤ ((a + b) + k)        ≡⟨ ℤ-right-succ (a + b) k ⁻¹    ⟩
          (a + b) + succℤ k          ≡⟨ IH                           ⟩ 
          a + (b + succℤ k)          ≡⟨ ap (a +_) (ℤ-right-succ b k) ⟩
          a + succℤ (b + k)          ≡⟨ ℤ-right-succ a (b + k)       ⟩
          succℤ (a + (b + k))        ∎

  ℤ+-rearrangement : (a b c : ℤ) → a + c + b ≡ a + (b + c)
  ℤ+-rearrangement a b c = a + c + b   ≡⟨ ℤ+-assoc a c b          ⟩ 
                           a + (c + b) ≡⟨ ap (a +_) (ℤ+-comm c b) ⟩
                           a + (b + c) ∎

  ℤ+-lc : (x y z : ℤ) → z + x ≡ z + y → x ≡ y
  ℤ+-lc x y = ℤ-induction base step₁ step₂
   where
    base : pos 0 + x ≡ pos 0 + y → x ≡ y
    base l = x           ≡⟨ ℤ-zero-left-neutral x ⁻¹ ⟩
             pos 0 + x   ≡⟨ l                        ⟩
             pos 0 + y   ≡⟨ ℤ-zero-left-neutral y    ⟩
             y           ∎

    step₁ : (k : ℤ)
          → (k + x ≡ k + y → x ≡ y)
          → succℤ k + x ≡ succℤ k + y
          → x ≡ y
    step₁ k IH l = IH (succℤ-lc I)
     where
      I : succℤ (k + x) ≡ succℤ (k + y)
      I = succℤ (k + x)  ≡⟨ ℤ-left-succ k x ⁻¹ ⟩
          succℤ k + x    ≡⟨ l                  ⟩
          succℤ k + y    ≡⟨ ℤ-left-succ k y    ⟩
          succℤ (k + y)  ∎

    step₂ : (k : ℤ)
          → (succℤ k + x ≡ succℤ k + y → x ≡ y)
          → k + x ≡ k + y
          → x ≡ y
    step₂ k IH l = IH I
     where
      I : succℤ k + x ≡ succℤ k + y
      I = succℤ k + x    ≡⟨ ℤ-left-succ k x    ⟩ 
          succℤ (k + x)  ≡⟨ ap succℤ l         ⟩
          succℤ (k + y)  ≡⟨ ℤ-left-succ k y ⁻¹ ⟩
          succℤ k + y    ∎

  ℤ-zero-right-is-zero : (x : ℤ) → x * pos 0 ≡ pos 0
  ℤ-zero-right-is-zero x = refl

  ℤ-zero-left-is-zero : (x : ℤ) → pos 0 * x ≡ pos 0
  ℤ-zero-left-is-zero = ℤ-induction base step₁ step₂
   where
    base : pos 0 * pos 0 ≡ pos 0
    base = refl

    step₁ : (k : ℤ)
          → pos 0 * k       ≡ pos 0
          → pos 0 * succℤ k ≡ pos 0
    step₁ (pos x)            IH = I
     where
      I : pos 0 * succℤ (pos x) ≡ pos 0
      I = pos 0 * succℤ (pos x) ≡⟨ refl             ⟩
          pos 0 + pos 0 * pos x ≡⟨ ap (pos 0 +_) IH ⟩
          pos 0 + pos 0         ≡⟨ refl             ⟩
          pos 0                 ∎
    step₁ (negsucc 0)        IH = refl
    step₁ (negsucc (succ x)) IH = I
     where
      I : pos 0 * negsucc x ≡ pos 0
      I = pos 0 * negsucc x            ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⁻¹ ⟩
          pos 0 + pos 0 * negsucc x    ≡⟨ refl                                       ⟩
          pos 0 * negsucc (succ x)     ≡⟨ IH                                         ⟩
          pos 0                        ∎

    step₂ : (k : ℤ)
          → pos 0 * succℤ k ≡ pos 0
          → pos 0 * k       ≡ pos 0
    step₂ (pos x)            IH = I
     where
      I : pos 0 * pos x ≡ pos 0
      I = pos 0 * pos x         ≡⟨ ℤ-zero-left-neutral (pos 0 * pos x) ⁻¹ ⟩
          pos 0 + pos 0 * pos x ≡⟨ IH                                     ⟩
          pos 0                 ∎
    step₂ (negsucc 0)        IH = refl
    step₂ (negsucc (succ x)) IH = I
     where
      I : pos 0 + pos 0 * negsucc x ≡ pos 0
      I = pos 0 + pos 0 * negsucc x ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⟩
          pos 0 * negsucc x         ≡⟨ IH                                      ⟩
          pos 0                     ∎

  ℤ-mult-right-id : (x : ℤ) → x * pos 1 ≡ x
  ℤ-mult-right-id x = refl

  ℤ-mult-left-id : (x : ℤ) → pos 1 * x ≡ x
  ℤ-mult-left-id = ℤ-induction base step₁ step₂
   where
    base : pos 1 * pos 0 ≡ pos 0
    base = refl

    step₁ : (k : ℤ)
          → pos 1 * k       ≡ k
          → pos 1 * succℤ k ≡ succℤ k
    step₁ (pos x) IH = I
     where
      I : pos 1 * succℤ (pos x) ≡ succℤ (pos x)
      I = pos 1 * succℤ (pos x) ≡⟨ ap (pos 1 +_) IH        ⟩
          pos 1 + pos x         ≡⟨ ℤ+-comm (pos 1) (pos x) ⟩
          succℤ (pos x)         ∎
    step₁ (negsucc 0)        IH = refl
    step₁ (negsucc (succ x)) IH = I
     where
      I : pos 1 * negsucc x ≡ negsucc x
      I = ℤ+-lc (pos 1 * negsucc x) (negsucc x) (negsucc 0) II
       where
        II : negsucc 0 + pos 1 * negsucc x ≡ negsucc 0 + negsucc x
        II = negsucc 0 + pos 1 * negsucc x ≡⟨ IH                                 ⟩
             negsucc (succ x)              ≡⟨ ℤ+-comm (negsucc x) (negsucc 0)    ⟩
             negsucc 0 + negsucc x         ∎

    step₂ : (k : ℤ)
          → pos 1 * succℤ k ≡ succℤ k
          → pos 1 * k       ≡ k
    step₂ (pos x)            IH = ℤ+-lc (pos 1 * pos x) (pos x) (pos 1) I
     where
      I : pos 1 + pos 1 * pos x ≡ pos 1 + pos x
      I = pos 1 + pos 1 * pos x ≡⟨ IH                      ⟩
          succℤ (pos x)         ≡⟨ ℤ+-comm (pos x) (pos 1) ⟩
          pos 1 + pos x         ∎
    step₂ (negsucc 0)        IH = refl
    step₂ (negsucc (succ x)) IH = I
     where
      I : pos 1 * negsucc (succ x) ≡ negsucc (succ x)
      I = pos 1 * negsucc (succ x) ≡⟨ ap (negsucc 0 +_) IH            ⟩
          negsucc 0 + negsucc x    ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
          negsucc (succ x)         ∎

  negsucctopredℤ : (k : ℕ) → negsucc k ≡ predℤ (- pos k)
  negsucctopredℤ 0        = refl
  negsucctopredℤ (succ k) = refl

  predℤtominussuccℤ : (x : ℤ) → (k : ℕ) → predℤ (- (x + pos k)) ≡ - succℤ (x + pos k)
  predℤtominussuccℤ x k = predminus (x + pos k)

  succℤtominuspredℤ : (x : ℤ) → succℤ (- x) ≡ (- predℤ x)
  succℤtominuspredℤ (pos 0)               = refl
  succℤtominuspredℤ (pos (succ 0))        = refl
  succℤtominuspredℤ (pos (succ (succ x))) = refl
  succℤtominuspredℤ (negsucc x)           = refl

  subtraction-dist₀ : (x : ℤ) (y : ℕ) → (- x) + (- pos y) ≡ - (x + pos y)
  subtraction-dist₀ x = induction base step
   where
    base : (- x) + (- pos 0) ≡ - (x + pos 0)
    base = refl

    step : (k : ℕ)
         → (- x) + (- pos k)        ≡ - (x + pos k)
         → (- x) + (- pos (succ k)) ≡ - (x + pos (succ k))
    step k IH = (- x) + negsucc k            ≡⟨ ap ((- x) +_) (negsucctopredℤ k) ⟩
                (- x) + predℤ (- pos k)      ≡⟨ ℤ-right-pred (- x) (- pos k)     ⟩
                predℤ ((- x) + (- pos k))    ≡⟨ ap predℤ IH                      ⟩
                predℤ (- (x + pos k))        ≡⟨ predℤtominussuccℤ x k            ⟩
                - (x + pos (succ k))         ∎

  subtraction-dist₁ : (x : ℤ) → (y : ℕ) → (- x) + (- (negsucc y)) ≡ - (x + negsucc y)
  subtraction-dist₁ x = induction base step
   where
    base : ((- x) + (- negsucc 0)) ≡ (- (x + negsucc 0))
    base = succℤtominuspredℤ x

    step : (k : ℕ)
         → (- x) + pos (succ k)         ≡ - (x + negsucc k)
         → (- x) + (- negsucc (succ k)) ≡ - (x + negsucc (succ k))
    step k IH = (- x) + succℤ (pos (succ k))   ≡⟨ ℤ-right-succ (- x) (pos (succ k)) ⟩
                succℤ ((- x) + pos (succ k))   ≡⟨ ap succℤ IH                       ⟩
                succℤ (- (x +negsucc k))       ≡⟨ succℤtominuspredℤ (x +negsucc k) ⟩
                - (x + negsucc (succ k))       ∎

  subtraction-dist : (x y : ℤ) → (- x) + (- y) ≡ - (x + y)
  subtraction-dist x (pos y)     = subtraction-dist₀ x y
  subtraction-dist x (negsucc y) = subtraction-dist₁ x y


  distributivity-mult-over-ℤ₀ : (x y : ℤ) → (z : ℕ) → (x + y) * (pos z) ≡ (x * pos z) + (y * pos z)
  distributivity-mult-over-ℤ₀ x y = induction base step
   where
    base : (x + y) * pos 0 ≡ (x * pos 0) + (y * pos 0)
    base = refl

    step : (k : ℕ)
         → (x + y) * pos k        ≡ x * pos k + y * pos k
         → (x + y) * pos (succ k) ≡ x * pos (succ k) + y * pos (succ k)
    step k IH = (x + y) * pos (succ k)             ≡⟨ ap ((x + y) +_) IH ⟩
                (x + y) + (u + v)                  ≡⟨ ℤ+-assoc (x + y) u v ⁻¹ ⟩
                ((x + y) + u) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x y u) ⟩
                (x + (y + u)) + v                  ≡⟨ ap (λ z → (x + z) + v) (ℤ+-comm y u) ⟩
                (x + (u + y)) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x u y ⁻¹) ⟩
                ((x + u) + y) + v                  ≡⟨ ℤ+-assoc (x + u) y v ⟩
                (x + u) + (y + v) ∎
       where
         u v : ℤ
         u = x * pos k
         v = y * pos k

  distributivity-mult-over-ℤ₁ : (x y : ℤ) → (z : ℕ) → (x + y) * (negsucc z) ≡ (x * negsucc z) + (y * negsucc z)
  distributivity-mult-over-ℤ₁ x y = induction base step
   where
    base : (x + y) * negsucc 0 ≡ x * negsucc 0 + y * negsucc 0
    base = (x + y) * negsucc 0           ≡⟨ refl                    ⟩
           - (x + y)                     ≡⟨ subtraction-dist x y ⁻¹ ⟩
           (- x) + (- y)                 ≡⟨ refl                    ⟩
           x * negsucc 0 + y * negsucc 0 ∎

    step : (k : ℕ)
         → (x + y) * negsucc k               ≡ x * negsucc k + y * negsucc k
         → (- (x + y)) + (x + y) * negsucc k ≡ (- x) + x * negsucc k + ((- y) + y * negsucc k)
    step k IH = (- x + y) + (x + y) * negsucc k                   ≡⟨ ap ((- (x + y)) +_) IH                                                   ⟩
                (- x + y) + (x * negsucc k + y * negsucc k)       ≡⟨ ap (_+ (((x * negsucc k) + (y * negsucc k)))) (subtraction-dist x y ⁻¹) ⟩
                (- x) + (- y) + (x * negsucc k + y * negsucc k)   ≡⟨ ℤ+-assoc (- x) (- y) (u + v)                                            ⟩
                (- x) + ((- y) + (x * negsucc k + y * negsucc k)) ≡⟨ ap ((- x) +_) (ℤ+-assoc (- y) u v ⁻¹)                                   ⟩
                (- x) + ((- y) + x * negsucc k + y * negsucc k)   ≡⟨ ap (λ z → (- x) + (z + v)) (ℤ+-comm (- y) u)                            ⟩
                (- x) + (x * negsucc k + (- y) + y * negsucc k)   ≡⟨ ap ((- x) +_) (ℤ+-assoc u (- y) v)                                      ⟩
                (- x) + (x * negsucc k + ((- y) + y * negsucc k)) ≡⟨ ℤ+-assoc (- x) u ((- y) + v) ⁻¹                                         ⟩
                (- x) + x * negsucc k + ((- y) + y * negsucc k) ∎
      where
        u v : ℤ
        u = x * negsucc k
        v = y * negsucc k

  distributivity-mult-over-ℤ : (x y z : ℤ) → (x + y) * z ≡ (x * z) + (y * z)
  distributivity-mult-over-ℤ x y (pos z)     = distributivity-mult-over-ℤ₀ x y z
  distributivity-mult-over-ℤ x y (negsucc z) = distributivity-mult-over-ℤ₁ x y z

  ℤ*-comm₀ : (x : ℤ) → (y : ℕ) → x * pos y ≡ pos y * x
  ℤ*-comm₀ x = induction base step
   where
    base : (x * pos 0) ≡ (pos 0 * x)
    base = x * pos 0 ≡⟨ ℤ-zero-left-is-zero x ⁻¹ ⟩
           pos 0 * x ∎

    step : (k : ℕ)
         → x * pos k     ≡ pos k * x
         → x + x * pos k ≡ (pos k + pos 1) * x
    step k IH = x + x * pos k         ≡⟨ ap (x +_) IH                                    ⟩
                x + pos k * x         ≡⟨ ap (_+ (pos k * x)) (ℤ-mult-left-id x ⁻¹)       ⟩
                pos 1 * x + pos k * x ≡⟨ distributivity-mult-over-ℤ (pos 1) (pos k) x ⁻¹ ⟩
                (pos 1 + pos k) * x   ≡⟨ ap (_* x) (ℤ+-comm (pos 1) (pos k))             ⟩
                (pos k + pos 1) * x   ∎

  mult-inverse : (x : ℤ) → (- x) ≡ (negsucc 0 * x)
  mult-inverse = ℤ-induction base step₁ step₂
   where
    base : (- pos 0) ≡ (negsucc 0 * pos 0)
    base = refl

    step₁ : (k : ℤ)
          → (- k)     ≡ negsucc 0 * k
          → - succℤ k ≡ negsucc 0 * succℤ k
    step₁ (pos 0)            IH = refl 
    step₁ (pos (succ x))     IH = predℤ (negsucc x)                ≡⟨ ap predℤ IH                                           ⟩
                                  predℤ (negsucc 0 * pos (succ x)) ≡⟨ ℤ-pred-is-minus-one (negsucc 0 + (negsucc 0 * pos x)) ⟩
                                  negsucc 0 * succℤ (pos (succ x)) ∎ 
    step₁ (negsucc 0)        IH = refl
    step₁ (negsucc (succ x)) IH = ℤ+-lc (- succℤ (negsucc (succ x))) (negsucc 0 * succℤ (negsucc (succ x))) (pos 1) I
     where
      I : pos 1 + (- succℤ (negsucc (succ x))) ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
      I = pos 1 + (- succℤ (negsucc (succ x))) ≡⟨ ap succℤ (ℤ+-comm (pos 1) (pos x)) ⟩
          succℤ (pos x + pos 1)                ≡⟨ IH ⟩
          negsucc 0 * negsucc (succ x)         ∎

    step₂ : (k : ℤ)
          → - succℤ k ≡ negsucc 0 * succℤ k
          → - k       ≡ negsucc 0 * k
    step₂ (pos 0)        IH = refl
    step₂ (pos (succ x)) IH = ℤ+-lc (- pos (succ x)) (negsucc 0 * pos (succ x)) (negsucc 0) I
     where
      I : negsucc 0 + (- pos (succ x)) ≡ negsucc 0 + negsucc 0 * pos (succ x)
      I = negsucc 0 + (- pos (succ x))     ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
          negsucc x + negsucc 0            ≡⟨ IH ⟩
          negsucc 0 * succℤ (pos (succ x)) ∎
    step₂ (negsucc 0)        IH = refl
    step₂ (negsucc (succ x)) IH = I
     where
      I : pos (succ x) + pos 1 ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
      I = pos (succ x) + pos 1                         ≡⟨ ℤ+-comm (pos (succ x)) (pos 1) ⟩
          pos 1 + pos (succ x)                         ≡⟨  ap (pos (succ 0) +_) IH    ⟩
          pos 1 + negsucc 0 * succℤ (negsucc (succ x)) ∎

  ℤ*-comm₁ : (x : ℤ) → (y : ℕ) → x * (negsucc y) ≡ (negsucc y) * x
  ℤ*-comm₁ x = induction base step
   where
    base : (x * negsucc 0) ≡ (negsucc 0 * x)
    base = mult-inverse x

    step : (k : ℕ)
         → x * negsucc k        ≡ negsucc k * x
         → x * negsucc (succ k) ≡ negsucc (succ k) * x
    step k IH = x * negsucc (succ k)              ≡⟨ refl                                                       ⟩
                (- x) + x * negsucc k             ≡⟨ ap ((- x) +_) IH                                           ⟩
                (- x) + negsucc k * x             ≡⟨ ap (_+ (negsucc k * x)) (mult-inverse x)                   ⟩
                (negsucc 0) * x + negsucc k * x   ≡⟨ distributivity-mult-over-ℤ (negsucc 0) (negsucc k) x ⁻¹ ⟩
                (negsucc 0 + negsucc k) * x       ≡⟨ ap (_* x) (ℤ+-comm (negsucc 0) (negsucc k))             ⟩ 
                negsucc (succ k) * x              ∎

  ℤ*-comm : (x y : ℤ) → x * y ≡ y * x
  ℤ*-comm x (pos y)     = ℤ*-comm₀ x y
  ℤ*-comm x (negsucc y) = ℤ*-comm₁ x y

  open import UF-Base -- TypeTopology

  distributivity-mult-over-ℤ' : (x y z : ℤ) → z * (x + y) ≡ (z * x) + (z * y)
  distributivity-mult-over-ℤ' x y z = z * (x + y)      ≡⟨ ℤ*-comm z (x + y)                                 ⟩
                                      (x + y) * z      ≡⟨ distributivity-mult-over-ℤ x y z                  ⟩
                                      x * z + y * z    ≡⟨ ap₂ (λ z z' → z + z') (ℤ*-comm x z) (ℤ*-comm y z) ⟩
                                      z * x + z * y    ∎

  ℤ*-assoc₀ : (x y : ℤ) → (z : ℕ ) → x * (y * pos z) ≡ (x * y) * pos z
  ℤ*-assoc₀ x y = induction base step
    where
      base : x * (y * pos 0) ≡ (x * y) * pos 0
      base = refl

      step : (k : ℕ)
           → x * (y * pos k)         ≡ (x * y) * pos k
           → x * (y * pos (succ k))  ≡ (x * y) * pos (succ k)
      step k IH = x * (y * pos (succ k))        ≡⟨ distributivity-mult-over-ℤ' y (y * pos k) x ⟩
                  x * y + x * (y * pos k)       ≡⟨ ap ((x * y) +_) IH                          ⟩
                  x * y + (x * y) * pos k       ∎


  subtraction-dist-over-mult₀ : (x : ℤ) → (y : ℕ) → x * (- pos y) ≡ - x * pos y
  subtraction-dist-over-mult₀ x = induction base step
    where
      base : x * (- pos 0) ≡ - (x * pos 0)
      base = refl

      step : (k : ℕ)
           → x * (- pos k)        ≡ - (x * pos k)
           → x * (- pos (succ k)) ≡ - (x * pos (succ k))
      step 0        IH = refl
      step (succ k) IH = x * (- pos (succ (succ k)))  ≡⟨ ap ((- x) +_) IH                     ⟩
                         (- x) + (- x * pos (succ k)) ≡⟨ subtraction-dist x (x + (x * pos k)) ⟩
                         - x + (x + x * pos k)        ∎

  minus-minus-is-plus : (x : ℤ) → - (- x) ≡ x
  minus-minus-is-plus (pos 0)        = refl
  minus-minus-is-plus (pos (succ x)) = refl
  minus-minus-is-plus (negsucc x)    = refl

  subtraction-dist-over-mult₁ : (x : ℤ) → (y : ℕ) → x * (- negsucc y) ≡ - x * negsucc y
  subtraction-dist-over-mult₁ x = induction base step
   where
    base : x * (- negsucc 0) ≡ - x * negsucc 0
    base = minus-minus-is-plus x ⁻¹

    step : (k : ℕ)
         → x * (- negsucc k) ≡ - x * negsucc k
         → x + x * (- negsucc k) ≡ - (- x) + x * negsucc k
    step k IH = x + x * (- negsucc k)         ≡⟨ ap (x +_) IH                                            ⟩
                x + (- x * negsucc k)         ≡⟨ ap (_+ (- (x * negsucc k)) ) (minus-minus-is-plus x ⁻¹) ⟩
                (- (- x)) + (- x * negsucc k) ≡⟨ subtraction-dist (- x) (x * negsucc k)                  ⟩
                - (- x) + x * negsucc k       ∎

  subtraction-dist-over-mult : (x y : ℤ) → x * (- y) ≡ - (x * y)
  subtraction-dist-over-mult x (pos y)     = subtraction-dist-over-mult₀ x y 
  subtraction-dist-over-mult x (negsucc y) = subtraction-dist-over-mult₁ x y

  subtraction-dist-over-mult' : (x y : ℤ) → (- x) * y ≡ - (x * y)
  subtraction-dist-over-mult' x y = II
   where
    I : y * (- x) ≡ - (y * x)
    I = subtraction-dist-over-mult y x

    II : (- x) * y ≡ - x * y
    II = (- x) * y ≡⟨ ℤ*-comm (- x) y     ⟩
         y * (- x) ≡⟨ I                   ⟩
         - (y * x) ≡⟨ ap -_ (ℤ*-comm y x) ⟩
         - (x * y)   ∎

  ℤ*-assoc₁ : (x y : ℤ) → (z : ℕ) → x * (y * negsucc z) ≡ (x * y) * negsucc z

  ℤ*-assoc₁ x y = induction base step
   where
    base : x * (y * negsucc 0) ≡ (x * y) * negsucc 0
    base = subtraction-dist-over-mult x y

    step : (k : ℕ)
         → x * (y * negsucc k) ≡ (x * y) * negsucc k
         → x * (y * negsucc (succ k)) ≡ (x * y) * negsucc (succ k)
    step k IH = x * (y * negsucc (succ k))        ≡⟨ distributivity-mult-over-ℤ' (- y) (y * negsucc k) x            ⟩
                x * (- y) + x * (y * negsucc k)   ≡⟨ ap ((x * (- y)) +_) IH                                         ⟩
                x * (- y) + x * y * negsucc k     ≡⟨ ap (_+ ((x * y) * negsucc k)) (subtraction-dist-over-mult x y) ⟩ 
                (- x * y) + x * y * negsucc k     ∎

  ℤ*-assoc : (x y z : ℤ) → x * (y * z) ≡ (x * y) * z
  ℤ*-assoc x y (pos z)     = ℤ*-assoc₀ x y z
  ℤ*-assoc x y (negsucc z) = ℤ*-assoc₁ x y z

  open import UF-Subsingletons -- TypeTopology

  positive-is-prop : (x : ℤ) → is-prop (positive x)
  positive-is-prop (pos x)     = 𝟙-is-prop
  positive-is-prop (negsucc x) = 𝟘-is-prop

  negative-is-prop : (x : ℤ) → is-prop (negative x)
  negative-is-prop (pos x) = 𝟘-is-prop
  negative-is-prop (negsucc x) = 𝟙-is-prop

  greater-than-zero-is-positive : (z : ℤ) → greater-than-zero z → positive z
  greater-than-zero-is-positive (negsucc x) g = g
  greater-than-zero-is-positive (pos x)     g = unique-to-𝟙 g

  greater-than-zero-is-prop : (z : ℤ) → is-prop (greater-than-zero z)
  greater-than-zero-is-prop (pos 0)        = 𝟘-is-prop
  greater-than-zero-is-prop (pos (succ x)) = 𝟙-is-prop
  greater-than-zero-is-prop (negsucc x)    = 𝟘-is-prop

  greater-than-zero-succℤ : (x : ℤ) → greater-than-zero x → greater-than-zero (succℤ x)
  greater-than-zero-succℤ (pos 0)        g = 𝟘-elim g
  greater-than-zero-succℤ (pos (succ x)) g = g
  greater-than-zero-succℤ (negsucc x)    g = 𝟘-elim g

  gtz₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x + (pos y))
  gtz₀ x = induction base step
   where
    base : greater-than-zero x
         → greater-than-zero (pos 0)
         → greater-than-zero (x + pos 0)
    base l r = 𝟘-elim r

    step : (k : ℕ)
         → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x + pos k))
         → greater-than-zero x
         → greater-than-zero (pos (succ k))
         → greater-than-zero (x + pos (succ k))
    step 0        IH l r = greater-than-zero-succℤ x l
    step (succ k) IH l r = greater-than-zero-succℤ (x + pos (succ k)) (IH l r)

  greater-than-zero-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x + y)
  greater-than-zero-trans x (pos y)         = gtz₀ x y
  greater-than-zero-trans x (negsucc y) l r = 𝟘-elim r

  gtzmt₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x * pos y)
  gtzmt₀ x = induction base step
   where
    base : greater-than-zero x → greater-than-zero (pos 0) → greater-than-zero (x * pos 0)
    base l r = 𝟘-elim r

    step : (k : ℕ)
         → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x * pos k))
         → greater-than-zero x
         → greater-than-zero (pos (succ k))
         → greater-than-zero (x * pos (succ k))
    step zero IH l r = l
    step (succ k) IH l r = greater-than-zero-trans x (x * pos (succ k)) l (IH l r)

  greater-than-zero-mult-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x * y)
  greater-than-zero-mult-trans x (negsucc y) l r = 𝟘-elim r
  greater-than-zero-mult-trans x (pos y)     l r = gtzmt₀ x y l r

  greater-than-zero-trans' : (x y : ℤ) → greater-than-zero x → positive y → greater-than-zero (x + y)
  greater-than-zero-trans' (pos 0)        y              g p = 𝟘-elim g
  greater-than-zero-trans' (pos (succ x)) (negsucc y)    g p = 𝟘-elim p
  greater-than-zero-trans' (pos (succ x)) (pos 0)        g p = g
  greater-than-zero-trans' (pos (succ x)) (pos (succ y)) g p = greater-than-zero-trans (pos (succ x)) (pos (succ y)) g p
  greater-than-zero-trans' (negsucc x)    y              g p = 𝟘-elim g

  negsucc-lc : {x y : ℕ} → negsucc x ≡ negsucc y → x ≡ y
  negsucc-lc p = succ-lc (ap abs p)

  open import Unit-Properties -- TypeTopology

  pos-not-negative : {x y : ℕ} → pos x ≢ negsucc y
  pos-not-negative p = 𝟙-is-not-𝟘 (ap positive p)

  neg-not-positive : {x y : ℕ} → negsucc x ≢ pos y
  neg-not-positive p = pos-not-negative (p ⁻¹)

  pos-int-not-zero : (x : ℕ) → pos (succ x) ≢ pos 0
  pos-int-not-zero x p = positive-not-zero x (pos-lc p)

  neg-int-not-zero : (x : ℕ) → negsucc x ≢ pos 0
  neg-int-not-zero x p = positive-not-zero x (ap abs p)

  open import DiscreteAndSeparated -- TypeTopology

  ℤ-is-discrete : is-discrete ℤ
  ℤ-is-discrete (pos x) (pos y) = f (ℕ-is-discrete x y)
    where
      f : (x ≡ y) ∔ ¬ (x ≡ y) → (pos x ≡ pos y) ∔ ¬ (pos x ≡ pos y)
      f (inl z) = inl (ap pos z)
      f (inr z) = inr (λ k → z (pos-lc k))
  ℤ-is-discrete (pos x)     (negsucc y) = inr pos-not-negative
  ℤ-is-discrete (negsucc x) (pos y)     = inr neg-not-positive
  ℤ-is-discrete (negsucc x) (negsucc y) = f (ℕ-is-discrete x y)
    where
      f : (x ≡ y) ∔ ¬ (x ≡ y) → decidable (negsucc x ≡ negsucc y)
      f (inl z) = inl (ap negsucc z)
      f (inr z) = inr (λ k → z (negsucc-lc k) )

  open import UF-Miscelanea -- TypeTopology

  ℤ-is-set : is-set ℤ
  ℤ-is-set = discrete-types-are-sets ℤ-is-discrete

  positive-succℤ : (x : ℤ) → positive x → positive (succℤ x)
  positive-succℤ (negsucc x) z = 𝟘-elim z
  positive-succℤ (pos x)     z = unique-to-𝟙 z

  positive-trans₀ : (x : ℤ) → (y : ℕ) → positive x → positive (x + pos y) 
  positive-trans₀ x = induction base step
   where
    base : positive x → positive (x + pos 0)
    base p = p

    step : (k : ℕ)
         → (positive x → positive (x + pos k))
         → positive x
         → positive (x + pos (succ k))
    step k IH z = positive-succℤ (x + (pos k)) (IH z)

  positive-trans : (x y : ℤ) → positive x →  positive y → positive (x + y) --NEED TO ADD THE REST OF THE CASES IN
  positive-trans (negsucc x) (negsucc y) p q = 𝟘-elim p
  positive-trans (negsucc x) (pos y)     p q = 𝟘-elim p
  positive-trans (pos x)     (negsucc y) p q = 𝟘-elim q
  positive-trans (pos x)     (pos y)     p q = positive-trans₀ (pos x) y (unique-to-𝟙 (positive (pos x + pos y)))

  pos-succ-greater-than-zero : (x : ℕ) → greater-than-zero (pos (succ x))
  pos-succ-greater-than-zero x = unique-to-𝟙 (greater-than-zero (pos (succ x)))

  pos-succ-not-zero : (x : ℕ) → not-zero (pos (succ x))
  pos-succ-not-zero x = λ z → z

  open import NaturalsAddition renaming (_+_ to _ℕ+_) -- TypeTopology

  pos-addition-equiv-to-ℕ : (x y : ℕ) → pos x + pos y ≡ pos (x ℕ+ y)
  pos-addition-equiv-to-ℕ x = induction base step
   where
    base : (pos x + pos 0) ≡ pos (x ℕ+ 0)
    base = refl

    step : (k : ℕ)
         → pos x + pos k        ≡ pos (x ℕ+ k)
         → pos x + pos (succ k) ≡ pos (x ℕ+ succ k)
    step k IH = pos x + pos (succ k)  ≡⟨ ap succℤ IH ⟩
                succℤ (pos (x ℕ+ k))  ∎

  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)

  pos-multiplication-equiv-to-ℕ : (x y : ℕ) → pos x * pos y ≡ pos (x ℕ* y)
  pos-multiplication-equiv-to-ℕ x = induction base step
    where
      base : (pos x * pos 0) ≡ pos (x ℕ* 0)
      base = refl

      step : (k : ℕ) →
               (pos x * pos k) ≡ pos (x ℕ* k) →
               (pos x * pos (succ k)) ≡ pos (x ℕ* succ k)
      step k IH = (pos x * pos (succ k))   ≡⟨ ap (pos x +_) IH                    ⟩
                  (pos x + pos (x ℕ* k))   ≡⟨ pos-addition-equiv-to-ℕ x (x ℕ* k) ⟩
                  pos (x ℕ* succ k) ∎

  ppnnp-lemma : (a b : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc b ≡ negsucc c
  ppnnp-lemma a = induction base step
   where
    base : Sigma ℕ (λ c → negsucc a + negsucc 0 ≡ negsucc c)
    base = succ a , refl

    step : (k : ℕ) →
             Sigma ℕ (λ c → negsucc a + negsucc k ≡ negsucc c) →
             Sigma ℕ (λ c → negsucc a + negsucc (succ k) ≡ negsucc c)
    step k (c , IH) = succ c , ap predℤ IH


  product-positive-negative-not-positive : (a b c : ℕ) → ¬ ((pos a * negsucc b) ≡ pos (succ c))
  product-positive-negative-not-positive zero zero c e = 𝟘-elim (positive-not-zero c (pos-lc e ⁻¹))
  product-positive-negative-not-positive zero (succ b) c e = 𝟘-elim (positive-not-zero c (I ⁻¹))
   where
    I : 0 ≡ succ c
    I = pos-lc (pos 0                    ≡⟨ ℤ-zero-left-is-zero (negsucc (succ b)) ⁻¹ ⟩
                pos 0 * negsucc (succ b) ≡⟨ e ⟩
                pos (succ c)             ∎)
  product-positive-negative-not-positive (succ a) (succ b) c e = neg-not-positive (III ⁻¹ ∙ e)
    where
     II : Σ z ꞉ ℕ , succ z ≡ succ a ℕ* succ b
     II = pos-mult-is-succ a b

     z : ℕ
     z = pr₁ II

     IV : Σ c ꞉ ℕ , negsucc a + negsucc z ≡ negsucc c
     IV = ppnnp-lemma a z

     I : pos (succ a) * negsucc b ≡ negsucc z
     I = pos (succ a) * negsucc b        ≡⟨ refl ⟩
         pos (succ a) * (- pos (succ b)) ≡⟨ subtraction-dist-over-mult (pos (succ a)) (pos (succ b)) ⟩
         - (pos (succ a) * pos (succ b)) ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⟩
         - pos (succ a ℕ* succ b)        ≡⟨ ap (λ - → -_ (pos -)) ((pr₂ II) ⁻¹) ⟩
         - pos (succ z)                  ≡⟨ refl ⟩
         negsucc z                       ∎

     III : negsucc a + pos (succ a) * negsucc b ≡ negsucc (pr₁ IV)
     III = ap ((negsucc a) +_) I ∙ pr₂ IV

  ℤ-sum-of-inverse-is-zero₀ : (x : ℕ) → pos x + (- pos x) ≡ pos 0
  ℤ-sum-of-inverse-is-zero₀ = induction base step
   where
    base : pos 0 + (- pos 0) ≡ pos 0
    base = refl

    step : (k : ℕ)
         → pos k + (- pos k)               ≡ pos 0
         → pos (succ k) + (- pos (succ k)) ≡ pos 0
    step 0        IH = refl
    step (succ k) IH = predℤ (pos (succ (succ k)) + negsucc k) ≡⟨ ℤ-left-pred (pos (succ (succ k))) (negsucc k) ⁻¹ ⟩
                       (pos (succ k) + (- pos (succ k)))       ≡⟨ IH                                               ⟩
                       pos 0                                   ∎

  ℤ-sum-of-inverse-is-zero₁ : (x : ℕ) → negsucc x + (- (negsucc x)) ≡ pos 0
  ℤ-sum-of-inverse-is-zero₁ = induction base step
   where
    base : (negsucc 0 + (- negsucc 0)) ≡ pos 0
    base = refl

    step : (k : ℕ)
         → negsucc k + (- negsucc k)               ≡ pos 0
         → negsucc (succ k) + (- negsucc (succ k)) ≡ pos 0
    step k IH = negsucc (succ k) + (- negsucc (succ k))  ≡⟨ ap succℤ (ℤ-left-succ (negsucc (succ k)) (pos k) ⁻¹) ⟩
                succℤ (succℤ (negsucc (succ k)) + pos k) ≡⟨ IH                                                   ⟩
                pos 0                                    ∎

  ℤ-sum-of-inverse-is-zero : (x : ℤ) → x + (- x) ≡ pos 0
  ℤ-sum-of-inverse-is-zero (pos x)     = ℤ-sum-of-inverse-is-zero₀ x
  ℤ-sum-of-inverse-is-zero (negsucc x) = ℤ-sum-of-inverse-is-zero₁ x 

  ℤ-mult-rearrangement : (x y z : ℤ) → (x * y) * z ≡ (x * z) * y
  ℤ-mult-rearrangement x y z = x * y * z   ≡⟨ ℤ*-assoc x y z ⁻¹       ⟩
                               x * (y * z) ≡⟨ ap (x *_) (ℤ*-comm y z) ⟩
                               x * (z * y) ≡⟨ ℤ*-assoc x z y          ⟩
                               x * z * y   ∎

  ℤ-mult-rearrangement' : (x y z : ℤ) → z * (x * y) ≡ y * (x * z)
  ℤ-mult-rearrangement' x y z = z * (x * y) ≡⟨ ℤ*-comm z (x * y)          ⟩
                                x * y * z   ≡⟨ ℤ-mult-rearrangement x y z ⟩
                                x * z * y   ≡⟨ ℤ*-comm (x * z) y          ⟩
                                y * (x * z) ∎

  ℤ-mult-rearrangement'' : (w x y z : ℤ) → (x * y) * (w * z) ≡ (w * y) * (x * z)
  ℤ-mult-rearrangement'' w x y z = (x * y) * (w * z)     ≡⟨ ℤ-mult-rearrangement x y (w * z)     ⟩
                                  (x * (w * z)) * y      ≡⟨ ap (_* y) (ℤ*-assoc x w z)           ⟩
                                  ((x * w) * z) * y      ≡⟨ ap (λ a → (a * z) * y) (ℤ*-comm x w) ⟩
                                  ((w * x) * z) * y      ≡⟨ ℤ*-assoc (w * x) z y ⁻¹              ⟩
                                  (w * x) * (z * y)      ≡⟨ ap ((w * x) *_) (ℤ*-comm z y)        ⟩
                                  (w * x) * (y * z)      ≡⟨ ℤ*-assoc (w * x) y z                 ⟩
                                  ((w * x) * y) * z      ≡⟨ ap (_* z) (ℤ*-assoc w x y ⁻¹)        ⟩
                                  (w * (x * y)) * z      ≡⟨ ap (λ a → (w * a) * z) (ℤ*-comm x y) ⟩
                                  (w * (y * x)) * z      ≡⟨ ap (_* z) (ℤ*-assoc w y x)           ⟩
                                  ((w * y) * x) * z      ≡⟨ ℤ*-assoc (w * y) x z ⁻¹              ⟩
                                  (w * y) * (x * z) ∎

  ℤ-mult-rearrangement''' : (x y z : ℤ) → x * (y * z) ≡ y * (x * z)
  ℤ-mult-rearrangement''' x y z = x * (y * z) ≡⟨ ℤ*-assoc x y z ⟩
                                  x * y * z   ≡⟨ ap (_* z) (ℤ*-comm x y) ⟩
                                  y * x * z   ≡⟨ ℤ*-assoc y x z ⁻¹ ⟩
                                  y * (x * z) ∎

  abs-removes-neg-sign : (x : ℤ) → abs x ≡ abs (- x)
  abs-removes-neg-sign (pos zero)     = refl
  abs-removes-neg-sign (pos (succ x)) = refl
  abs-removes-neg-sign (negsucc x)    = refl

  abs-over-mult : (a b : ℤ) → abs (a * b) ≡ abs a ℕ* abs b
  abs-over-mult (pos x) (pos b) = I
   where
    I : abs (pos x * pos b) ≡ abs (pos x) ℕ* abs (pos b)
    I = abs (pos x * pos b)        ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ x b) ⟩
        abs (pos (x ℕ* b))         ≡⟨ refl ⟩
        abs (pos x) ℕ* abs (pos b) ∎
  abs-over-mult (pos zero) (negsucc b) = I
   where
    I : abs (pos zero * negsucc b) ≡ abs (pos zero) ℕ* abs (negsucc b)
    I = abs (pos zero * negsucc b) ≡⟨ ap abs (ℤ-zero-left-is-zero (negsucc b)) ⟩
        abs (pos 0)                ≡⟨ zero-left-is-zero (abs (negsucc b)) ⁻¹ ⟩
        abs (pos zero) ℕ* abs (negsucc b) ∎
  abs-over-mult (pos (succ x)) (negsucc b) = I
   where
    I : abs (pos (succ x) * negsucc b) ≡ abs (pos (succ x)) ℕ* abs (negsucc b)
    I = abs (pos (succ x) * negsucc b)           ≡⟨ ap abs (subtraction-dist-over-mult (pos (succ x)) (pos (succ b))) ⟩
        abs (- ((pos (succ x) * pos (succ b))))  ≡⟨ ap (λ z → (abs (- z))) (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
        abs (- pos (succ x ℕ* succ b))           ≡⟨ abs-removes-neg-sign ( pos (succ x ℕ* succ b)) ⁻¹ ⟩
        abs (pos (succ x ℕ* succ b))             ≡⟨ refl ⟩
        succ x ℕ* succ b                         ≡⟨ refl ⟩
        abs (pos (succ x)) ℕ* abs (negsucc b)    ∎
  abs-over-mult (negsucc x) (pos b) = I
   where
    I : abs (negsucc x * pos b) ≡ abs (negsucc x) ℕ* abs (pos b)
    I = abs (negsucc x * pos b)        ≡⟨ ap abs (subtraction-dist-over-mult' (pos (succ x)) (pos b)) ⟩
        abs (- pos (succ x) * pos b)   ≡⟨ ap (λ z → abs (- z)) (pos-multiplication-equiv-to-ℕ (succ x) b) ⟩
        abs (- pos (succ x ℕ* b))      ≡⟨ abs-removes-neg-sign (pos (succ x ℕ* b)) ⁻¹ ⟩
        (succ x) ℕ* b                  ≡⟨ refl ⟩
        abs (negsucc x) ℕ* abs (pos b) ∎
  abs-over-mult (negsucc x) (negsucc b) = I
   where
    I : abs (negsucc x * negsucc b) ≡ abs (negsucc x) ℕ* abs (negsucc b)
    I = abs (negsucc x * negsucc b)               ≡⟨ ap abs (subtraction-dist-over-mult (negsucc x) (pos (succ b))) ⟩
        abs (- negsucc x * pos (succ b) )         ≡⟨ ap (λ z → abs (- z)) (subtraction-dist-over-mult' (pos (succ x)) (pos (succ b))) ⟩
        abs (- (- pos (succ x) * pos (succ b)))   ≡⟨ ap abs (minus-minus-is-plus (pos (succ x) * pos (succ b))) ⟩
        abs (pos (succ x) * pos (succ b))         ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
        (succ x) ℕ* (succ b)                      ≡⟨ refl ⟩
        abs (negsucc x) ℕ* abs (negsucc b)       ∎

  open import Groups -- TypeTopology

  integers-+-group : Group-structure ℤ
  integers-+-group = _+_ , ℤ-is-set , ℤ+-assoc , (pos 0) , (ℤ-zero-left-neutral , ℤ-zero-right-neutral , (λ x → (- x) , ((ℤ+-comm (- x) x ∙ ℤ-sum-of-inverse-is-zero x) , (ℤ-sum-of-inverse-is-zero x))))

\end{code}

\begin{code}

 module RIntegersOrder where

  open RIntegers

  _≤_ _≥_ _<_ _>_ : (x y : ℤ) → 𝓤₀ ̇
  x ≤ y = Σ c ꞉ ℤ , positive c × (x + c ≡ y)
  x ≥ y = y ≤ x
  x < y = Σ c ꞉ ℤ , greater-than-zero c × (x + c ≡ y) --Σ c ꞉ ℤ , positive c × (x + (succℤ c) ≡ y) -- succℤ x ≤ y
  x > y = y < x

  open import UF-Subsingletons --TypeTopology
  open RIntegersProperties

  ℤ≤-is-prop : (x y : ℤ) → is-prop (x ≤ y)
  ℤ≤-is-prop x y (p , q , r) (p' , q' , r') = to-subtype-≡ (λ a → ×-is-prop (positive-is-prop a) ℤ-is-set) (ℤ+-lc p p' x (r ∙ (r' ⁻¹)))

  ℤ<-is-prop : (x y : ℤ) → is-prop (x < y)
  ℤ<-is-prop x y (p , q , r) (p' , q' , r') = to-subtype-≡ (λ a → ×-is-prop (greater-than-zero-is-prop a) ℤ-is-set) (ℤ+-lc p p' x (r ∙ r' ⁻¹))

  ≤-incrℤ : (x : ℤ) → x ≤ succℤ x
  ≤-incrℤ x = pos 1 , ⋆ , refl

  <-incrℤ : (x : ℤ) → x < succℤ x
  <-incrℤ x = pos 1 , ⋆ , refl

  <-predℤ : (x : ℤ) → predℤ x < x
  <-predℤ x = pos 1 , ⋆ , (succpredℤ x)

  ℤ≤-trans : (x y z : ℤ) → x ≤ y → y ≤ z → x ≤ z
  ℤ≤-trans x y z (c , p , q) (c' , p' , q') = (c + c') , (positive-trans c c' p p' , I)
   where
    I : x + (c + c') ≡ z
    I = x + (c + c') ≡⟨ ℤ+-assoc x c c' ⁻¹ ⟩
        (x + c) + c' ≡⟨ ap (_+ c') q       ⟩
        y + c'       ≡⟨ q'                 ⟩
        z            ∎

  ℤ<-trans : (x y z : ℤ) → x < y → y < z → x < z
  ℤ<-trans x y z (c , p , q) (c' , p' , q') = c + c' , (greater-than-zero-trans c c' p p') , I
   where
    I : x + (c + c') ≡ z
    I = x + (c + c') ≡⟨ ℤ+-assoc x c c' ⁻¹ ⟩
        x + c + c'   ≡⟨  ap (_+ c') q      ⟩
        y + c'       ≡⟨ q'                 ⟩
        z            ∎

  ℤ≤-refl : (x : ℤ) → x ≤ x
  ℤ≤-refl x = pos 0 , ⋆ , refl

  ℤ≤-anti-lemma : (x y : ℤ) → x + y ≡ x → y ≡ pos 0
  ℤ≤-anti-lemma x y l = ℤ+-lc y (pos 0) x l

  ℤ≤-succℤ-ap : (x y : ℤ) → x ≤ y → succℤ x ≤ succℤ y
  ℤ≤-succℤ-ap x y (p , q , r) = p , q , I
   where
    I : succℤ x + p ≡ succℤ y
    I = succℤ x + p   ≡⟨ ℤ-left-succ x p ⟩
        succℤ (x + p) ≡⟨ ap succℤ r      ⟩
        succℤ y       ∎

  ℤ<-adding : (a b c d : ℤ) → a < b → c < d → (a + c) < (b + d)
  ℤ<-adding a b c d (p , α , β) (q , α' , β') = (p + q) , (greater-than-zero-trans p q α α') , I
   where
     I : (a + c) + (p + q) ≡ (b + d)
     I = (a + c) + (p + q)      ≡⟨ ℤ+-assoc (a + c) p q ⁻¹              ⟩
         ((a + c) + p) + q      ≡⟨ ap (λ z → (z + p) + q) (ℤ+-comm a c) ⟩
         ((c + a) + p) + q      ≡⟨ ap (_+ q) (ℤ+-assoc c a p)           ⟩
         (c + (a + p)) + q      ≡⟨ ap (λ z → (c + z) + q) β             ⟩
         (c + b) + q            ≡⟨ ap (_+ q) (ℤ+-comm c b)              ⟩
         (b + c) + q            ≡⟨ ℤ+-assoc b c q                       ⟩
         b + (c + q)            ≡⟨ ap (b +_) β'                         ⟩
         b + d                  ∎

  ℤ≤-adding : (a b c d : ℤ) → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
  ℤ≤-adding a b c d (p , α , β) (q , α' , β') = (p + q) , (positive-trans p q α α') , I
   where
    I : (a + c) + (p + q) ≡ (b + d)
    I = (a + c) + (p + q)      ≡⟨ ℤ+-assoc (a + c) p q ⁻¹              ⟩
        ((a + c) + p) + q      ≡⟨ ap (λ z → (z + p) + q) (ℤ+-comm a c) ⟩
        ((c + a) + p) + q      ≡⟨ ap (_+ q) (ℤ+-assoc c a p)           ⟩
        (c + (a + p)) + q      ≡⟨ ap (λ z → (c + z) + q) β             ⟩
        (c + b) + q            ≡⟨ ap (_+ q) (ℤ+-comm c b)              ⟩
        (b + c) + q            ≡⟨ ℤ+-assoc b c q                       ⟩
        b + (c + q)            ≡⟨ ap (b +_) β'                         ⟩
        b + d                  ∎

  ℤ<-adding' : (a b c : ℤ) → a < b → a + c < b + c
  ℤ<-adding' a b c (k , α , β) = k , (α , I)
   where
    I : a + c + k ≡ b + c
    I = a + c + k       ≡⟨ ℤ+-assoc a c k ⟩
        a + (c + k)     ≡⟨ ap (a +_) (ℤ+-comm c k) ⟩
        a + (k + c)     ≡⟨ ℤ+-assoc a k c ⁻¹ ⟩
        a + k + c       ≡⟨ ap (_+ c) β ⟩
        b + c ∎

  open import UF-Base --TypeTopology

  ℤ<-adding'' : (a b c : ℤ) → a < b → c + a < c + b
  ℤ<-adding'' a b c l = transport₂ _<_ (ℤ+-comm a c) (ℤ+-comm b c) I
   where
    I : (a + c) < (b + c)
    I = ℤ<-adding' a b c l

  ℤ<-less-than-pos-addition' : (a b c : ℤ) → greater-than-zero c → a < b → a < b + c
  ℤ<-less-than-pos-addition' a b (negsucc x) g l       = 𝟘-elim g
  ℤ<-less-than-pos-addition' a b (pos x) g (k , g' , p) = (k + pos x) , ((greater-than-zero-trans k (pos x) g' g) , I)
   where
    I : a + (k + pos x) ≡ b + pos x
    I = a + (k + pos x) ≡⟨ ℤ+-assoc a k (pos x) ⁻¹ ⟩
        a + k + pos x   ≡⟨ ap (_+ pos x) p         ⟩
        b + pos x ∎

  ℤ<-less-than-pos-addition : (a b : ℤ) → greater-than-zero b → a < a + b
  ℤ<-less-than-pos-addition a (negsucc x) g = 𝟘-elim g
  ℤ<-less-than-pos-addition a (pos x)     g = (pos x) , (g , refl)

  negative-less-than-positive : (x y : ℤ) → negative x → positive y → x < y
  negative-less-than-positive (pos x)     (pos y)     n p = 𝟘-elim n
  negative-less-than-positive (pos x)     (negsucc y) n p = 𝟘-elim p
  negative-less-than-positive (negsucc x) (pos y)     n p = (pos (succ x) + (pos y)) , (greater-than-zero-trans' (pos (succ x)) (pos y) ⋆ ⋆ , I)
   where
    I : negsucc x + (pos (succ x) + pos y) ≡ pos y
    I = negsucc x + (pos (succ x) + pos y)  ≡⟨ ℤ+-assoc (negsucc x) (pos (succ x)) (pos y) ⁻¹       ⟩
        (negsucc x + pos (succ x)) + pos y  ≡⟨ ap (_+ pos y) (ℤ-sum-of-inverse-is-zero (negsucc x)) ⟩
        pos 0 + pos y                       ≡⟨ ℤ+-comm  (pos 0) (pos y)                             ⟩                 
        pos y                               ∎
  negative-less-than-positive (negsucc x) (negsucc y) n p = 𝟘-elim p

  ℤ<-succℤ-ap : (x y : ℤ) → x < y → succℤ x < succℤ y
  ℤ<-succℤ-ap x y (c , p , e) = c , p , I
   where
    I : succℤ x + c ≡ succℤ y
    I = succℤ x + c   ≡⟨ ℤ-left-succ x c ⟩
        succℤ (x + c) ≡⟨ ap succℤ e      ⟩
        succℤ y       ∎

  open RMoreNaturalProperties
  open import NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology

  greater-than-zero-not-less-than-zero : (k : ℕ) → ¬ (pos (succ k) < pos zero)
  greater-than-zero-not-less-than-zero k (negsucc x    , p , q) = 𝟘-elim p
  greater-than-zero-not-less-than-zero k (pos 0        , p , q) = 𝟘-elim p
  greater-than-zero-not-less-than-zero k (pos (succ x) , p , q) = 𝟘-elim (pos-int-not-zero (k ℕ+ succ x) I)
   where
    I : pos (succ (k ℕ+ succ x)) ≡ pos 0
    I = pos (succ (k ℕ+ succ x))    ≡⟨ ap pos (succ-left k (succ x) ⁻¹)    ⟩
        pos (succ k ℕ+ succ x)      ≡⟨ pos-addition-equiv-to-ℕ (succ k) (succ x) ⁻¹ ⟩
        pos (succ k) + pos (succ x) ≡⟨ q                                            ⟩
        pos 0                       ∎

  zero-not-greater-than-zero : ¬ greater-than-zero (pos zero)
  zero-not-greater-than-zero z = z

  ℤ-equal-not-less-than : (a b : ℤ) → a ≡ b → ¬ (a < b)
  ℤ-equal-not-less-than a b e (negsucc x    , g , p) = 𝟘-elim g
  ℤ-equal-not-less-than a b e (pos 0        , g , p) = 𝟘-elim g
  ℤ-equal-not-less-than a b e (pos (succ x) , g , p) = pos-int-not-zero x (ℤ+-lc (pos (succ x)) (pos 0) a p')
   where
    p' : a + pos (succ x) ≡ a + (pos zero)
    p' = a + pos (succ x) ≡⟨ p    ⟩
         b                ≡⟨ e ⁻¹ ⟩
         a                ∎

  ℤ-trichotomous-lemma : (x : ℕ) → (negsucc x) + (pos x) ≡ negsucc zero
  ℤ-trichotomous-lemma = induction base step
   where
    base : (negsucc 0 + pos 0) ≡ negsucc zero
    base = refl

    step : (k : ℕ)
         → (negsucc k + pos k)               ≡ negsucc 0
         → (negsucc (succ k) + pos (succ k)) ≡ negsucc 0
    step k IH = negsucc (succ k) + pos (succ k)  ≡⟨ ℤ-left-pred (negsucc k) (pos (succ k)) ⟩
                predℤ (negsucc k + pos (succ k)) ≡⟨ predsuccℤ (negsucc k + pos k)          ⟩
                negsucc k + pos k                ≡⟨ IH                                     ⟩
                negsucc 0                        ∎

  ℤ-trichotomous : (x y : ℤ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
  ℤ-trichotomous (pos 0)        (pos 0)            = inr (inl refl)
  ℤ-trichotomous (pos 0)        (pos (succ y))     = inl ((pos (succ y)) , ⋆ , ap succℤ (ℤ+-comm (pos 0) (pos y)))
  ℤ-trichotomous (pos 0)        (negsucc 0)        = inr (inr (pos 1 , ⋆ , refl))
  ℤ-trichotomous (pos 0)        (negsucc (succ y)) = inr (inr ((pos (succ (succ y))) , (⋆ , (ℤ-sum-of-inverse-is-zero (negsucc (succ y))))))
  ℤ-trichotomous (pos (succ x)) (pos 0)            = inr (inr ((pos (succ x)) , (⋆ , (ap succℤ (ℤ+-comm (pos 0) (pos x))))))
  ℤ-trichotomous (pos (succ x)) (pos (succ y))     = helper (ℤ-trichotomous (pos x) (pos y))
   where
    helper : (pos x < pos y) ∔ (pos x ≡ pos y) ∔ (pos y < pos x) →
             (pos (succ x) < pos (succ y)) ∔ (pos (succ x) ≡ pos (succ y)) ∔ (pos (succ y) < pos (succ x))
    helper (inl (c , (g , p)))       = inl (c , (g  , (ℤ-left-succ (pos x) c ∙ ap succℤ p)))
    helper (inr (inl z))             = inr (inl (ap succℤ z))
    helper (inr (inr (c , (g , p)))) = inr (inr (c , (g , (ℤ-left-succ (pos y) c ∙ ap succℤ p))))
  ℤ-trichotomous (pos (succ x))     (negsucc 0)        = inr (inr ((pos (succ (succ x))) , ⋆ , (ℤ+-comm (negsucc 0) (pos (succ (succ x))))))
  ℤ-trichotomous (pos (succ x))     (negsucc (succ y)) = inr (inr (negative-less-than-positive (negsucc (succ y)) (pos (succ x)) ⋆ ⋆))
  ℤ-trichotomous (negsucc 0)        (pos 0)            = inl (pos 1 , ⋆ , refl)
  ℤ-trichotomous (negsucc 0)        (pos (succ y))     = inl ((pos (succ (succ y))) , ⋆ , (ℤ+-comm (negsucc 0) (pos (succ (succ y)))))
  ℤ-trichotomous (negsucc (succ x)) (pos 0)            = inl (negative-less-than-positive (negsucc (succ x)) (pos 0) ⋆ ⋆)
  ℤ-trichotomous (negsucc (succ x)) (pos (succ y))     = inl (negative-less-than-positive (negsucc (succ x)) (pos (succ y)) ⋆ ⋆)
  ℤ-trichotomous (negsucc 0)        (negsucc 0)        = inr (inl refl)
  ℤ-trichotomous (negsucc 0)        (negsucc (succ y)) = inr (inr ((pos (succ y)) , ⋆ , ℤ-trichotomous-lemma (succ y)))
  ℤ-trichotomous (negsucc (succ x)) (negsucc 0)        = inl ((pos (succ x)) , (⋆ , ℤ-trichotomous-lemma (succ x)))
  ℤ-trichotomous (negsucc (succ x)) (negsucc (succ y)) = tri-split (ℤ-trichotomous (negsucc x) (negsucc y))
   where
    tri-split : (negsucc x < negsucc y) ∔ (negsucc x ≡ negsucc y) ∔ (negsucc y < negsucc x)
              → (negsucc (succ x) < negsucc (succ y)) ∔ (negsucc (succ x) ≡ negsucc (succ y)) ∔ (negsucc (succ y) < negsucc (succ x))
    tri-split (inl (c , (g , p)))       = inl (c , (g , (ℤ-left-pred (negsucc x) c ∙ ap predℤ p)))
    tri-split (inr (inl z))             = inr (inl (ap predℤ z))
    tri-split (inr (inr (c , (g , p)))) = inr (inr (c , (g , (ℤ-left-pred (negsucc y) c ∙ ap predℤ p))))

  ℤ<-coarser-than-≤ : (m n : ℤ) → (m < n) → m ≤ n
  ℤ<-coarser-than-≤ m n (k , g , p) = k , greater-than-zero-is-positive k g , p

  ℤ≤-split : (x y : ℤ) → x ≤ y → (x < y) ∔ (x ≡ y)
  ℤ≤-split x y (negsucc a    , p) = 𝟘-elim (pr₁ p)
  ℤ≤-split x y (pos 0        , p) = inr (pr₂ p)
  ℤ≤-split x y (pos (succ a) , p) = inl (pos (succ a) , ⋆ , pr₂ p)

  ℤ≡-to-≤ : (x y : ℤ) → x ≡ y → x ≤ y
  ℤ≡-to-≤ x y e = (pos 0) , (⋆ , e)

  pmpo-lemma : (a b : ℤ) → (n : ℕ) → a < b →  a * pos (succ n) < b * pos (succ n)
  pmpo-lemma a b = induction base step
   where
    base : a < b
         → a * pos 1 < b * pos 1
    base z = z

    step : (k : ℕ)
         → (a < b → a * pos (succ k) < b * pos (succ k))
         → a < b
         → a * pos (succ (succ k)) < b * pos (succ (succ k))
    step k IH l = ℤ<-adding a b (a + (a * pos k)) (b + (b * pos k)) l (IH l)

  positive-multiplication-preserves-order : (a b c : ℤ) → greater-than-zero c → a < b → (a * c) < (b * c)
  positive-multiplication-preserves-order a b (negsucc x)    p l = 𝟘-elim p
  positive-multiplication-preserves-order a b (pos 0)        p l = 𝟘-elim p
  positive-multiplication-preserves-order a b (pos (succ x)) p l = pmpo-lemma a b x l

  positive-multiplication-preserves-order' : (a b c : ℤ) → greater-than-zero c → a < b → (c * a) < (c * b)
  positive-multiplication-preserves-order' a b c g l = transport₂ (λ z z' → z < z') (ℤ*-comm a c) (ℤ*-comm b c) (positive-multiplication-preserves-order a b c g l)

  nmco-lemma : (a b : ℤ) → (c : ℕ) → a < b → (b * (negsucc c)) < (a * (negsucc c))
  nmco-lemma a b = induction base step
   where
    base : a < b → (b * negsucc 0) < (a * negsucc 0)
    base (α , β , γ) = α , β , I
     where
      I : b * negsucc 0 + α ≡ a * negsucc 0
      I = (- b) + α  ≡⟨ ap (λ z → ((- z) + α)) (γ ⁻¹)       ⟩
          (- (a + α)) + α         ≡⟨ ap (_+ α) (subtraction-dist a α ⁻¹)        ⟩
          ((- a) + (- α)) + α     ≡⟨ ℤ+-assoc (- a) (- α) α                     ⟩
          (- a) + ((- α) + α)     ≡⟨ ap ((- a) +_) (ℤ+-comm (- α) α)            ⟩
          (- a) + (α + (- α))     ≡⟨ ap ((- a) +_) (ℤ-sum-of-inverse-is-zero α) ⟩
          (- a)                   ∎

    step : (k : ℕ)
         → (a < b → (b * negsucc k) < (a * negsucc k))
         →  a < b → (b * negsucc (succ k)) < (a * negsucc (succ k))
    step k IH l = ℤ<-adding (- b) (- a) (b * negsucc k) (a * negsucc k) (base l) (IH l)

  negative-multiplication-changes-order : (a b c : ℤ) → negative c → a < b → (b * c) < (a * c)
  negative-multiplication-changes-order a b (pos c)     g l = 𝟘-elim g
  negative-multiplication-changes-order a b (negsucc c) g l = nmco-lemma a b c l

  negative-multiplication-changes-order' : (a b c : ℤ) → negative c → a ≤ b → (b * c) ≤ (a * c)
  negative-multiplication-changes-order' a b (pos c)     g l = 𝟘-elim g
  negative-multiplication-changes-order' a b (negsucc c) g l = I (ℤ≤-split a b l)
   where
    I : (a < b) ∔ (a ≡ b) → (b * negsucc c) ≤ (a * negsucc c)
    I (inr z) = ℤ≡-to-≤ (b * negsucc c) (a * negsucc c) (II ⁻¹)
     where
      II : a * negsucc c ≡ b * negsucc c
      II = ap (_* negsucc c) z
    I (inl z) = ℤ<-coarser-than-≤ (b * negsucc c) (a * negsucc c) II
     where
      II : (b * negsucc c) < (a * negsucc c)
      II = negative-multiplication-changes-order a b (negsucc c) ⋆ z

  ordering-right-cancellable-lemma : (a b : ℤ) → (n : ℕ) → (a * (pos (succ n))) < (b * (pos (succ n))) → a < b
  ordering-right-cancellable-lemma a b = induction base step
   where
    base : (a * pos 1) < (b * pos 1) → a < b
    base z = z

    step : (k : ℕ)
         → (a * pos (succ k) < b * pos (succ k) → a < b)
         → a * pos (succ (succ k)) < b * pos (succ (succ k))
         → a < b
    step k IH (α , β , γ) = I (ℤ-trichotomous a b)
     where
      I : (a < b) ∔ (a ≡ b) ∔ (b < a) → a < b
      I (inl l)       = l
      I (inr (inl l)) = 𝟘-elim (zero-not-greater-than-zero (transport greater-than-zero (ℤ+-lc α (pos 0) (a + (a + (a * pos k))) i) β))
       where
        i : a + (a + a * pos k) + α ≡ a * pos (succ (succ k)) + pos 0 
        i = a + (a + a * pos k) + α        ≡⟨ γ                                                   ⟩
            b * pos (succ (succ k))        ≡⟨ ap (λ z → (z * pos (succ (succ k))) + pos 0) (l ⁻¹) ⟩
            a * pos (succ (succ k)) + pos 0 ∎
      I (inr (inr (p , q , r))) = IH (((a + α) + (- b)) , (II , III))
       where
        II : greater-than-zero ((a + α) + (- b))
        II = tri-split (ℤ-trichotomous (a + (- b)) (pos 0))
         where
          i : (a + α) + (- b) ≡ α + (a + (- b))
          i = a + α + (- b)   ≡⟨ ℤ+-assoc a α (- b)          ⟩
              a + (α + (- b)) ≡⟨ ap (a +_) (ℤ+-comm α (- b)) ⟩
              a + ((- b) + α) ≡⟨ ℤ+-assoc a (- b) α ⁻¹       ⟩
              a + (- b) + α   ≡⟨ ℤ+-comm (a + (- b)) α       ⟩
              α + (a + (- b)) ∎

          tri-split : ((a + (- b)) < pos 0) ∔ ((a + (- b)) ≡ pos 0) ∔ (pos 0 < (a + (- b))) → greater-than-zero ((a + α) + (- b))
          tri-split (inl (p' , q' , r')) = 𝟘-elim (zero-not-greater-than-zero (transport greater-than-zero δ (greater-than-zero-trans p p' q q')))
           where
            δ : p + p' ≡ pos 0
            δ = p + p'               ≡⟨ ap (λ z → (p + z) + p') (ℤ-sum-of-inverse-is-zero b ⁻¹) ⟩
                p + (b + (- b)) + p' ≡⟨ ap (_+ p') (ℤ+-assoc p b (- b) ⁻¹)                      ⟩
                p + b + (- b) + p'   ≡⟨ ap (λ z → (z + (- b)) + p') (ℤ+-comm p b)               ⟩
                b + p + (- b) + p'   ≡⟨ ap (λ z → (z + (- b)) + p') r                           ⟩
                a + (- b) + p'       ≡⟨ r'                                                      ⟩
                pos 0                ∎              
          tri-split (inr (inl c)) = transport greater-than-zero ψ β
           where
            ψ : α ≡ a + α + (- b)
            ψ = α + pos 0       ≡⟨ ap (α +_) (c ⁻¹) ⟩
                α + (a + (- b)) ≡⟨ i ⁻¹             ⟩
                a + α + (- b)   ∎  
          tri-split (inr (inr (p , q , r))) = transport greater-than-zero δ (greater-than-zero-trans α p β q)
           where
            δ : α + p ≡ a + α + (- b)
            δ = α + p           ≡⟨ ap (α +_) (ℤ+-comm p (pos 0) ∙ r) ⟩
                α + (a + (- b)) ≡⟨ i ⁻¹                              ⟩
                a + α + (- b)   ∎

        III : a * pos (succ k) + (a + α + (- b)) ≡ b * pos (succ k)
        III = a * pos (succ k) + (a + α + (- b)) ≡⟨ ℤ+-assoc (a + (a * pos k)) (a + α) (- b) ⁻¹              ⟩
              a + a * pos k + (a + α) + (- b)    ≡⟨ ap (_+ (- b)) (ℤ+-assoc (a + (a * pos k)) a α ⁻¹)        ⟩
              a + a * pos k + a + α + (- b)      ≡⟨ ap (λ z → (z + α) + (- b)) (ℤ+-comm (a + (a * pos k)) a) ⟩
              a + (a + a * pos k) + α + (- b)    ≡⟨ ap (_+ (- b)) γ                                          ⟩
              b * pos (succ (succ k)) + (- b)    ≡⟨ ap (_+ (- b)) (ℤ+-comm b (b + (b * pos k)))              ⟩
              b + b * pos k + b + (- b)          ≡⟨ ℤ+-assoc (b + (b * pos k)) b (- b)                       ⟩
              b + b * pos k + (b + (- b))        ≡⟨ ap ((b * pos (succ k)) +_) (ℤ-sum-of-inverse-is-zero b)  ⟩
              b * pos (succ k) + pos 0           ∎

  ordering-right-cancellable : (a b c : ℤ) → greater-than-zero c → (a * c) < (b * c) → a < b
  ordering-right-cancellable a b (negsucc x)    p l = 𝟘-elim p
  ordering-right-cancellable a b (pos 0)        p l = 𝟘-elim p
  ordering-right-cancellable a b (pos (succ x)) p l = ordering-right-cancellable-lemma a b x l

  ℤ-ordering-cancellable : (a b c : ℤ) → greater-than-zero c → c * a < c * b
                                                             ∔ c * a < b * c
                                                             ∔ a * c < c * b
                                                             ∔ a * c < b * c
                                                             → a < b
  ℤ-ordering-cancellable a b c p (inl l)             = ordering-right-cancellable a b c p (transport₂ (λ z z' → z < z') (ℤ*-comm c a) (ℤ*-comm c b) l)
  ℤ-ordering-cancellable a b c p (inr (inl l))       = ordering-right-cancellable a b c p (transport (_< b * c) (ℤ*-comm c a) l)
  ℤ-ordering-cancellable a b c p (inr (inr (inl l))) = ordering-right-cancellable a b c p (transport ((a * c) <_) (ℤ*-comm c b) l)
  ℤ-ordering-cancellable a b c p (inr (inr (inr l))) = ordering-right-cancellable a b c p l

  ordering-multiplication-transitive : (a b c d : ℤ) → greater-than-zero b → greater-than-zero c → a < b → c < d → (a * c) < (b * d)
  ordering-multiplication-transitive a b              (negsucc c)    d g₁ g₂     = 𝟘-elim g₂
  ordering-multiplication-transitive a (negsucc b)    (pos c)        d g₁ g₂     = 𝟘-elim g₁
  ordering-multiplication-transitive a (pos 0)        (pos c)        d g₁ g₂     = 𝟘-elim g₁
  ordering-multiplication-transitive a (pos (succ b)) (pos 0)        d g₁ g₂     = 𝟘-elim g₂
  ordering-multiplication-transitive a (pos (succ b)) (pos (succ c)) d g₁ g₂ α β = ℤ<-trans (a * pos (succ c)) (pos (succ b) * pos (succ c)) (pos (succ b) * d) I II
   where
    I : a * pos (succ c) < pos (succ b) * pos (succ c)
    I = positive-multiplication-preserves-order a (pos (succ b)) (pos (succ c)) ⋆ α

    II : pos (succ b) * pos (succ c) < pos (succ b) * d
    II = positive-multiplication-preserves-order' (pos (succ c)) d (pos (succ b)) ⋆ β

  ℤ-mult-right-cancellable : (x y z : ℤ) → not-zero z → (x * z) ≡ (y * z) → x ≡ y
  ℤ-mult-right-cancellable x y (pos 0)        notzero e = 𝟘-elim (notzero ⋆)
  ℤ-mult-right-cancellable x y (pos (succ z)) notzero e = tri-split (ℤ-trichotomous x y)
   where
    tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
    tri-split (inl α)        = 𝟘-elim (ℤ-equal-not-less-than (x * pos (succ z)) (y * (pos (succ z))) e (positive-multiplication-preserves-order x y (pos (succ z)) ⋆ α))
    tri-split (inr (inl α)) = α
    tri-split (inr (inr α)) = 𝟘-elim (ℤ-equal-not-less-than (y * pos (succ z)) (x * (pos (succ z))) (e ⁻¹) (positive-multiplication-preserves-order y x (pos (succ z)) ⋆ α))
  ℤ-mult-right-cancellable x y (negsucc z) notzero e = tri-split (ℤ-trichotomous x y)
   where
    tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
    tri-split (inl α)       = 𝟘-elim (ℤ-equal-not-less-than (y * negsucc z) (x * negsucc z) (e ⁻¹) (negative-multiplication-changes-order x y (negsucc z) ⋆ α))
    tri-split (inr (inl α)) = α
    tri-split (inr (inr α)) = 𝟘-elim (ℤ-equal-not-less-than (x * negsucc z) (y * negsucc z) e (negative-multiplication-changes-order y x (negsucc z) ⋆ α)) 

  ℤ-mult-left-cancellable : (x y z : ℤ) → not-zero z → (z * x) ≡ (z * y) → x ≡ y
  ℤ-mult-left-cancellable x y z nz e = ℤ-mult-right-cancellable x y z nz I
   where
    I : x * z ≡ y * z
    I = x * z   ≡⟨ ℤ*-comm x z ⟩
        z * x   ≡⟨ e ⟩
        z * y   ≡⟨ ℤ*-comm z y ⟩
        y * z ∎

  ℤ-set-least-element : {A : ℤ → 𝓤 ̇} → (Σ a ꞉ ℤ , ((A a) × ((m : ℤ) → (A m) → a < m))) → Σ m ꞉ ℤ , A m × ((n : ℤ) → A n → m ≤ n)
  ℤ-set-least-element (x , p , q) = x , p , λ n y → ℤ<-coarser-than-≤ x n (q n y)

  ℤ-mod-gives-positive : (z : ℤ) → positive (absℤ z)
  ℤ-mod-gives-positive (pos z) = ⋆
  ℤ-mod-gives-positive (negsucc z) = ⋆

  ℤ-between-mod : (z : ℤ) → - absℤ z ≤ z × z ≤ absℤ z
  ℤ-between-mod (pos 0)        = ℤ≤-refl (pos 0) , ℤ≤-refl (pos 0)
  ℤ-between-mod (pos (succ z)) = I , II
   where
    I : (- absℤ (pos (succ z))) ≤ pos (succ z)
    I = ℤ<-coarser-than-≤ (- absℤ (pos (succ z))) (pos (succ z)) (negative-less-than-positive (- absℤ (pos (succ z))) (pos (succ z)) (unique-to-𝟙 (negative (- absℤ (pos (succ z))))) (unique-to-𝟙 (positive (pos (succ z)))) )

    II : pos (succ z) ≤ absℤ (pos (succ z))
    II = ℤ≤-refl (pos (succ z))
  ℤ-between-mod (negsucc z) = I , II
   where
    I : (- absℤ (negsucc z)) ≤ negsucc z
    I = ℤ≤-refl (- absℤ (negsucc z))

    II : negsucc z ≤ absℤ (negsucc z)
    II = ℤ<-coarser-than-≤ (negsucc z) (absℤ (negsucc z)) (negative-less-than-positive (negsucc z) (absℤ (negsucc z)) (unique-to-𝟙 (negsucc z)) (unique-to-𝟙 (absℤ (negsucc z))))

  ℤ-between-mod-converse : (a c : ℤ) → positive c → (- c ≤ a) × (a ≤ c) → absℤ a ≤ c
  ℤ-between-mod-converse a           (negsucc c) g (α                   , β) = 𝟘-elim g
  ℤ-between-mod-converse (pos a)     (pos 0)     g (α                   , β) = β
  ℤ-between-mod-converse (negsucc a) (pos 0)     g ((negsucc c , δ , γ) , β) = 𝟘-elim δ
  ℤ-between-mod-converse (negsucc a) (pos 0)     g ((pos c     , δ , γ) , β) = 𝟘-elim (neg-not-positive (I ⁻¹))
   where
    I : pos c ≡ negsucc a
    I = pos c         ≡⟨ ℤ-zero-left-neutral (pos c) ⁻¹ ⟩
        pos 0 + pos c ≡⟨ γ ⟩
        negsucc a     ∎

  ℤ-between-mod-converse (pos a)     (pos (succ c)) g (α , β) = β
  ℤ-between-mod-converse (negsucc a) (pos (succ c)) g (α , β) = negative-multiplication-changes-order' (- pos (succ c)) (negsucc a) (negsucc 0) g α

  ℤ-triangle-inequality : (a b : ℤ) → absℤ (a + b) ≤ absℤ a + absℤ b
  ℤ-triangle-inequality a b = ℤ-between-mod-converse (a + b) (absℤ a + absℤ b) (positive-trans (absℤ a) (absℤ b) (ℤ-mod-gives-positive a) (ℤ-mod-gives-positive b)) ((IV III) , V)
   where
    I : ((- absℤ a) ≤ a) × (a ≤ absℤ a)
    I = ℤ-between-mod a

    i : (- absℤ a) ≤ a
    i = pr₁ I

    ii : a ≤ absℤ a
    ii = pr₂ I

    II : ((- absℤ b) ≤ b) × (b ≤ absℤ b) 
    II = ℤ-between-mod b

    iii : (- absℤ b) ≤ b
    iii = pr₁ II

    iv : b ≤ absℤ b
    iv = pr₂ II

    III : (- absℤ a) + (- absℤ b) ≤ a + b
    III = ℤ≤-adding (- absℤ a) a (- absℤ b) b i iii

    IV : (- absℤ a) + (- absℤ b) ≤ (a + b) → - (absℤ a + absℤ b) ≤ (a + b)
    IV = transport (λ - → - ≤ a + b) (subtraction-dist (absℤ a) (absℤ b))

    V : (a + b) ≤ (absℤ a + absℤ b)
    V = ℤ≤-adding a (absℤ a) b (absℤ b) ii iv

\end{code}

\begin{code}

 module RIntegersDivision where
  open RIntegers

  _∣_ : ℤ → ℤ → 𝓤₀ ̇
  a ∣ b = Σ x ꞉ ℤ , a * x ≡ b

  open import UF-Subsingletons --TypeTopology
  open RIntegersProperties
  open RIntegersOrder

  _ℤ∣_-is-prop : (a b : ℤ) → not-zero a → is-prop (a ∣ b)
  _ℤ∣_-is-prop a b nz (x , p) (x' , p') = to-subtype-≡ (λ _ → ℤ-is-set) (ℤ-mult-right-cancellable x x' a nz (ℤ*-comm x a ∙ (p ∙ p' ⁻¹ ∙ ℤ*-comm a x')))

  open RNaturalsDivision renaming (_∣_ to _ℕ∣_)

  div-equiv-to-pos-div : (a b : ℕ) → a ℕ∣ b → pos a ∣ pos b
  div-equiv-to-pos-div a b (x , p) = (pos x) , (pos-multiplication-equiv-to-ℕ a x ∙ ap pos p)

  sign-split : (x : ℤ) → positive x ∔ negative x
  sign-split (pos x)     = inl ⋆
  sign-split (negsucc x) = inr ⋆

  open import NaturalNumbers-Properties --TypeTopology

  pos-div-to-nat-div : (a b : ℕ) → pos a ∣ pos b → a ℕ∣ b
  pos-div-to-nat-div a b (pos x , p) = x , (pos-lc (pos-multiplication-equiv-to-ℕ a x ⁻¹ ∙ p))
  pos-div-to-nat-div a zero (negsucc x , p) = zero , refl
  pos-div-to-nat-div zero (succ b) (negsucc x , p) = 𝟘-elim (positive-not-zero b (pos-lc (ℤ-zero-left-is-zero (negsucc x) ⁻¹ ∙ p) ⁻¹))
  pos-div-to-nat-div (succ a) (succ b) (negsucc x , p) = 𝟘-elim (product-positive-negative-not-positive (succ a) x b p)

  open import UF-Base --TypeTopology
  open RMoreNaturalProperties
  open import NaturalsOrder renaming (_<_ to _ℕ<_ ; _≤_ to _ℕ≤_) --TypeTopology
  open RNaturalsOrderExtended
  open import NaturalsAddition renaming (_+_ to _ℕ+_)--TypeTopology
  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)

  ℤ-division : (a : ℤ) → (d : ℕ) → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (a ≡ (q * (pos (succ d))) + (pos r)) × (r ℕ< (succ d))
  ℤ-division (pos a) d = f (division a d)
   where
    f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q ℕ* succ d ℕ+ r) × (r ℕ< succ d)
      → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (pos a ≡ q * pos (succ d) + pos r) × (r ℕ< succ d)
    f (q , r , e , l) = (pos q) , r , (ap pos e ∙ I) , l
     where
      I : pos (q ℕ* succ d ℕ+ r) ≡ pos q * pos (succ d) + pos r
      I = pos (q ℕ* succ d ℕ+ r)    ≡⟨ pos-addition-equiv-to-ℕ (q ℕ* (succ d)) r ⁻¹               ⟩
          pos (q ℕ* succ d) + pos r ≡⟨ ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ d) ⁻¹) ⟩
          pos q * pos (succ d) + pos r ∎
  ℤ-division (negsucc a) d = f (division (succ a) d)
   where
    f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q ℕ* succ d ℕ+ r) × (r ℕ< succ d) → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (negsucc a ≡ q * pos (succ d) + pos r) × (r ℕ< succ d)
    f (zero , zero , e , l) = 𝟘-elim (positive-not-zero a I)
     where
      I : succ a ≡ zero
      I = succ a                 ≡⟨ e ⟩
          zero ℕ* succ d ℕ+ zero ≡⟨ zero-left-is-zero (succ d) ⟩
          0                       ∎
    f (succ q , zero , e , l) = negsucc q , 0 , I , l
     where
      I : negsucc a ≡ negsucc q * pos (succ d)
      I = negsucc a                       ≡⟨ refl ⟩
          - pos (succ a)                  ≡⟨ ap -_ (ap pos e) ⟩
          - (pos (succ q ℕ* succ d))      ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹) ⟩
          - (pos (succ q) * pos (succ d)) ≡⟨ subtraction-dist-over-mult' (pos (succ q)) (pos (succ d)) ⁻¹ ⟩
          (- pos (succ q)) * pos (succ d) ≡⟨ refl ⟩
          negsucc q * pos (succ d)        ∎

    f (zero , succ r , e , l) = (negsucc 0) , k , II , cosubtraction k d (r , succ-lc I)
     where
      r-lemma : Σ k ꞉ ℕ , k ℕ+ succ r ≡ succ d
      r-lemma = subtraction' (succ r) (succ d) l

      k : ℕ
      k = pr₁ r-lemma

      I : succ (r ℕ+ k) ≡ succ d
      I = succ (r ℕ+ k) ≡⟨ succ-left r k ⁻¹ ⟩ succ r ℕ+ k ≡⟨ addition-commutativity (succ r) k ⟩ k ℕ+ succ r ≡⟨ pr₂ r-lemma ⟩ succ d ∎

      III : a ≡ r
      III = succ-lc (e ∙ ap succ (ap (_ℕ+ r) (zero-left-is-zero (succ d))) ∙ ap succ (zero-left-neutral r) )

      V : negsucc 0 * pos (succ r) ≡ negsucc r
      V = mult-inverse (pos (succ r)) ⁻¹ ∙ refl

      VI : pos k + pos (succ r) ≡ pos (succ d)
      VI = pos-addition-equiv-to-ℕ k (succ r) ∙ ap pos (pr₂ r-lemma)

      II : negsucc a ≡ negsucc 0 * pos (succ d) + pos k
      II = negsucc a ≡⟨ ap negsucc III ⟩
           negsucc r                        ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹ ⟩
           pos 0 + negsucc r                ≡⟨ ap (_+ (negsucc r)) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹ ) ⟩
           pos k + (- pos k) + negsucc r    ≡⟨ ℤ+-assoc (pos k) (- pos k) (negsucc r) ⟩
           pos k + ((- pos k) + negsucc r)  ≡⟨ ℤ+-comm (pos k) ((- pos k) + negsucc r) ⟩
           ((- pos k) + negsucc r) + pos k  ≡⟨ ap (λ z → (z + negsucc r) + pos k) (mult-inverse (pos k)) ⟩
           negsucc 0 * pos k + negsucc r + pos k ≡⟨ ap (λ z →  (negsucc 0 * pos k + z) + pos k) (mult-inverse (pos (succ r))) ⟩
           negsucc 0 * pos k + (negsucc 0 * pos (succ r)) + pos k ≡⟨ ap (_+ pos k) (distributivity-mult-over-ℤ' (pos k) (pos (succ r)) (negsucc 0) ⁻¹) ⟩
           negsucc 0 * (pos k + pos (succ r)) + pos k             ≡⟨ ap (λ z → negsucc 0 * z + pos k) VI ⟩
           negsucc 0 * pos (succ d) + pos k                            ∎

    f (succ q , succ r , e , l) = (negsucc (succ q)) , k , I , cosubtraction k d (r , succ-lc V)
     where
      r-lemma' : Σ k ꞉ ℕ , k ℕ+ (succ r) ≡ succ d
      r-lemma' = subtraction (succ r) (succ d) (<-trans r d (succ d) l (<-succ d)) 

      k : ℕ
      k = pr₁ r-lemma'

      V : succ (r ℕ+ k) ≡ succ d
      V = succ (r ℕ+ k) ≡⟨ succ-left r k ⁻¹ ⟩ succ r ℕ+ k ≡⟨ addition-commutativity (succ r) k ⟩ k ℕ+ succ r ≡⟨ pr₂ r-lemma' ⟩ succ d ∎

      II : (- pos k) + (- pos (succ r)) ≡ - pos (succ d)
      II = (- pos k) + (- pos (succ r)) ≡⟨ subtraction-dist (pos k) (pos (succ r))    ⟩
           -(pos k + pos (succ r))      ≡⟨ ap -_ (pos-addition-equiv-to-ℕ k (succ r)) ⟩
           - pos (k ℕ+ succ r)          ≡⟨ ap -_ (ap pos (pr₂ r-lemma'))               ⟩
           - pos (succ d)               ∎

      III : - pos (succ r) ≡ pos k + (- pos (succ d))
      III = - pos (succ r) ≡⟨ refl ⟩
            negsucc r                              ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹                             ⟩
            pos 0 + (- pos (succ r))               ≡⟨ ap (_+ (- pos (succ r))) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹) ⟩
            pos k + (- pos k) + (- pos (succ r))   ≡⟨ ℤ+-assoc (pos k) (- pos k) (- pos (succ r))                    ⟩
            pos k + ((- pos k) + (- pos (succ r))) ≡⟨ ap (pos k +_) II                                               ⟩
            pos k + (- pos (succ d)) ∎

      IV : pos (succ q) + pos 1 ≡ pos (succ (succ q))
      IV = refl

      I : negsucc a ≡ negsucc (succ q) * pos (succ d) + pos k
      I = negsucc a                                            ≡⟨ refl                                                                                   ⟩
          - pos (succ a)                                       ≡⟨ ap -_ (ap pos e)                                                                       ⟩ 
          - (pos (succ q ℕ* succ d ℕ+ succ r))                 ≡⟨ ap -_ (pos-addition-equiv-to-ℕ (succ q ℕ* (succ d)) (succ r) ⁻¹)                      ⟩
          - (pos (succ q ℕ* succ d) + pos (succ r))            ≡⟨ subtraction-dist (pos (succ q ℕ* succ d)) (pos (succ r)) ⁻¹                            ⟩
          (- pos (succ q ℕ* succ d)) + (- pos (succ r))        ≡⟨ ap₂ (λ z z' → z + z') (ap -_ (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹)) III ⟩
          (- pos (succ q) * pos (succ d)) + (pos k + (- pos (succ d))) ≡⟨ ℤ+-rearrangement (- (pos (succ q) * pos (succ d))) (pos k) (- pos (succ d)) ⁻¹ ⟩
          (- pos (succ q) * pos (succ d)) + (- pos (succ d)) + pos k  ≡⟨ ap (λ z → (z + (- pos (succ d))) + pos k) (ap -_ (ℤ*-comm (pos (succ q)) (pos (succ d)))) ⟩ 
          (- (pos (succ d) * pos (succ q))) + (- pos (succ d)) + pos k    ≡⟨ ap (λ z → (z + (- pos (succ d))) + pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ q)) ⁻¹) ⟩
          (- pos (succ d)) * pos (succ q) + (- (pos (succ d))) + pos k    ≡⟨ ap (λ z → ((- pos (succ d)) * pos (succ q) + z) + pos k) (ℤ-mult-right-id (- pos (succ d))) ⁻¹ ⟩
          (- pos (succ d)) * pos (succ q) + (- pos (succ d)) * pos 1 + pos k ≡⟨ ap (_+ pos k) (distributivity-mult-over-ℤ' (pos (succ q)) (pos 1) (- pos (succ d)) ⁻¹)  ⟩
          (- pos (succ d)) * (pos (succ q) + pos 1) + pos k  ≡⟨ ap (λ z → (((- pos (succ d))) * z) + pos k) IV ⟩
          (- pos (succ d)) * pos (succ (succ q)) + pos k     ≡⟨ ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ (succ q)))) ⟩
          (- pos (succ d) * pos (succ (succ q))) + pos k     ≡⟨ ap (λ z → (- z) + pos k) (ℤ*-comm (pos (succ d)) (pos (succ (succ q))))  ⟩
          (- pos (succ (succ q)) * pos (succ d)) + pos k     ≡⟨ ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ (succ q))) (pos (succ d)) ⁻¹) ⟩
          negsucc (succ q) * pos (succ d) + pos k ∎

  ℤ-∣-respects-addition : (x y z : ℤ) → x ∣ y → x ∣ z → x ∣ y + z
  ℤ-∣-respects-addition x y z (α , αₚ) (β , βₚ) = α + β , I
   where
    I : x * (α + β) ≡ y + z
    I = x * (α + β)   ≡⟨ distributivity-mult-over-ℤ' α β x ⟩
        x * α + x * β ≡⟨ ap₂ _+_ αₚ βₚ ⟩
        y + z         ∎

  ℤ-∣-respects-addition-of-multiples : (x y z k l : ℤ) → x ∣ y → x ∣ z → x ∣ (y * k + z * l)
  ℤ-∣-respects-addition-of-multiples x y z k l (α , αₚ) (β , βₚ) = α * k + β * l , I
   where
    I : x * (α * k + β * l) ≡ y * k + z * l
    I = x * (α * k + β * l)       ≡⟨ distributivity-mult-over-ℤ' (α * k) (β * l) x ⟩
        x * (α * k) + x * (β * l) ≡⟨ ap₂ _+_ (ℤ*-assoc x α k) (ℤ*-assoc x β l) ⟩
        x * α * k + x * β * l     ≡⟨ ap₂ _+_ (ap (_* k) αₚ) (ap (_* l) βₚ) ⟩
        y * k + z * l             ∎


\end{code}

\begin{code}
 module RIntegersHCF where
 
  open RIntegers
  open RIntegersDivision

  ℤ-is-common-divisor : (d x y : ℤ) → 𝓤₀ ̇
  ℤ-is-common-divisor d x y = (d ∣ x) × (d ∣ y)

  open import UF-Subsingletons --TypeTopology

  ℤ-is-common-divisor-is-prop : (d x y : ℤ) → not-zero d → is-prop (ℤ-is-common-divisor d x y)
  ℤ-is-common-divisor-is-prop d x y nz p q = ×-is-prop ((d ℤ∣ x -is-prop) nz) ((d ℤ∣ y -is-prop) nz) p q

  ℤ-is-hcf : (d : ℕ) → (x y : ℤ) → 𝓤₀ ̇
  ℤ-is-hcf d x y = ℤ-is-common-divisor (pos d) x y × ((f : ℕ) → ℤ-is-common-divisor (pos f) x y → pos f ∣ pos d)

  open RHCF
  open import NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology
  open RNaturalsDivision renaming (_∣_ to _ℕ∣_)
  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)
  open import NaturalsOrder --TypeTopology
  open RIntegersProperties


  ℤ-HCF : (a b : ℕ) → Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ ((pos a) * x) + ((pos b) * y))
  ℤ-HCF = course-of-values-induction (λ a → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos a * x + pos b * y)) step 
   where
    step : (n : ℕ)
         → (((a : ℕ) → a < n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos a * x + pos b * y)))
         → (b : ℕ)
         → Σ h ꞉ ℕ , is-hcf h n b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos n * x + pos b * y)
    step 0 IH b = b , (((0 , refl) , 1 , refl) , (λ x → pr₂)) , ((pos 0) , pos 1) , ℤ+-comm (pos b) (pos 0)
    step (succ n) IH b = I (division b n)
     where
      I : (Σ q ꞉ ℕ , Σ r ꞉ ℕ , (b ≡ q ℕ* succ n ℕ+ r) × (r < succ n))
        → Σ h ꞉ ℕ , is-hcf h (succ n) b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x + pos b * y)
      I (q , r , e₀ , l) = II (IH r l (succ n)) 
       where
        II : Σ h ꞉ ℕ , is-hcf h r (succ n) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos r * x + pos (succ n) * y)
           → Σ h ꞉ ℕ , is-hcf h (succ n) b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x + pos b * y)
        II (h , (((α , αₚ) , β , βₚ) , γ) , (x , y) , e₁) = h , ((((β , βₚ) , i) , ii) , iii)
         where
          i : h ℕ∣ b
          i = (q ℕ* β ℕ+ α) , e₂
           where
            e₂ : h ℕ* (q ℕ* β ℕ+ α) ≡ b
            e₂ = h ℕ* (q ℕ* β ℕ+ α)       ≡⟨ distributivity-mult-over-nat h (q ℕ* β) α      ⟩ 
                 h ℕ* (q ℕ* β) ℕ+ h ℕ* α ≡⟨ ap (λ z → h ℕ* (q ℕ* β) ℕ+ z) αₚ                 ⟩
                 h ℕ* (q ℕ* β) ℕ+ r      ≡⟨ ap (_ℕ+ r) (mult-associativity h q β) ⁻¹       ⟩
                 h ℕ* q ℕ* β ℕ+ r        ≡⟨ ap (λ z → z ℕ* β ℕ+ r) (mult-commutativity h q) ⟩
                 q ℕ* h ℕ* β ℕ+ r        ≡⟨ ap (_ℕ+ r) (mult-associativity q h β)          ⟩
                 q ℕ* (h ℕ* β) ℕ+ r      ≡⟨ ap (λ z → q ℕ* z ℕ+ r) βₚ                       ⟩
                 q ℕ* succ n ℕ+ r        ≡⟨ e₀ ⁻¹ ⟩
                 b                        ∎

          ii : (f : ℕ) → is-common-divisor f (succ n) b → f ℕ∣ h
          ii f ((μ , μₚ) , ν , νₚ) = γ f ((hcflemma f ν (q ℕ* μ) r e₃) , μ , μₚ)
           where
            e₃ : f ℕ* ν ≡ f ℕ* (q ℕ* μ) ℕ+ r
            e₃ = f ℕ* ν              ≡⟨ νₚ                                             ⟩
                 b                   ≡⟨ e₀                                             ⟩
                 q ℕ* succ n ℕ+ r   ≡⟨ ap (λ z → q ℕ* z ℕ+ r) (μₚ ⁻¹)                  ⟩
                 q ℕ* (f ℕ* μ) ℕ+ r ≡⟨ ap (_ℕ+ r) (mult-associativity q f μ ⁻¹)       ⟩
                 q ℕ* f ℕ* μ ℕ+ r   ≡⟨ ap (λ z → z ℕ* μ ℕ+ r) (mult-commutativity q f) ⟩
                 f ℕ* q ℕ* μ ℕ+ r   ≡⟨ ap (_ℕ+ r ) (mult-associativity f q μ)         ⟩
                 f ℕ* (q ℕ* μ) ℕ+ r ∎

          iii : Σ (x' , y') ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x' + pos b * y'
          iii = (y + (- pos q * x) , x) , e₄
           where
            e₅ : pos b ≡ pos q * pos (succ n) + (pos r)
            e₅ = pos b ≡⟨ ap pos e₀ ⟩
                 pos (q ℕ* succ n ℕ+ r)     ≡⟨ pos-addition-equiv-to-ℕ (q ℕ* (succ n)) r ⁻¹ ⟩
                 pos (q ℕ* succ n) + pos r  ≡⟨ ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ n)) ⁻¹ ⟩
                 pos q * pos (succ n) + pos r ∎

            e₄ : pos h ≡ pos (succ n) * (y + (- pos q * x)) + pos b * x
            e₄ = pos h                                                                          ≡⟨ e₁ ⟩
                 pos r * x + pos (succ n) * y                                                   ≡⟨ ℤ+-comm (pos r * x) (pos (succ n) * y) ⟩
                 pos (succ n) * y + pos r * x                                                   ≡⟨ refl ⟩
                 pos (succ n) * (y + pos 0) + pos r * x                                         ≡⟨ ap (λ z → pos (succ n) * (y + z) + pos r * x) (ℤ-sum-of-inverse-is-zero (pos q * x) ⁻¹) ⟩
                 pos (succ n) * (y + (pos q * x + (- pos q * x))) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * (y + z) + pos r * x) (ℤ+-comm (pos q * x) (- pos q * x)) ⟩
                 pos (succ n) * (y + ((- pos q * x) + pos q * x)) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * z + pos r * x) (ℤ+-assoc y (- pos q * x) (pos q * x) ⁻¹) ⟩
                 pos (succ n) * (y + (- pos q * x) + (pos q) * x) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x) + z) + pos r * x) (ℤ*-comm (pos q) x) ⟩
                 pos (succ n) * (y + (- pos q * x) + x * pos q) + pos r * x                     ≡⟨ ap (_+ pos r * x) (distributivity-mult-over-ℤ' (y + (- pos q * x)) (x * pos q) (pos (succ n))) ⟩
                 pos (succ n) * (y + (- pos q * x)) + pos (succ n) * (x * pos q) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-comm (pos (succ n)) (x * pos q)) ⟩
                 pos (succ n) * (y + (- pos q * x)) + (x * pos q) * pos (succ n) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-assoc x (pos q) (pos (succ n)) ⁻¹) ⟩ 
                 pos (succ n) * (y + (- pos q * x)) + x * (pos q * pos (succ n)) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-comm x (pos q * pos (succ n))) ⟩
                 pos (succ n) * (y + (- pos q * x)) + (pos q * pos (succ n)) * x + pos r * x    ≡⟨ ℤ+-assoc (pos (succ n) * (y + (- pos q * x))) ((pos q + pos q * pos n) * x) (pos r * x) ⟩
                 pos (succ n) * (y + (- pos q * x)) + ((pos q * pos (succ n)) * x + pos r * x)  ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z) (distributivity-mult-over-ℤ (pos q * pos (succ n)) (pos r) x ⁻¹) ⟩
                 pos (succ n) * (y + (- pos q * x)) + (pos q * pos (succ n) + pos r) * x        ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z * x) (e₅ ⁻¹) ⟩
                 pos (succ n) * (y + (- pos q * x)) + pos b * x ∎

  ℤ-HCF' : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
  ℤ-HCF' a b = I (ℤ-HCF a b)
   where
    I : (Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ ((pos a) * x) + ((pos b) * y))) → Σ h ꞉ ℕ , is-hcf h a b
    I (h , is-hcf , bezout) = h , is-hcf


  coprime-bezout : (a b : ℕ) → coprime a b → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y
  coprime-bezout a b = I (ℤ-HCF a b)
   where
    I : Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ ((pos a) * x) + ((pos b) * y)) → coprime a b → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y
    I (h , is-hcf , (x , y) , bezout) h' = (x , y) , (III ⁻¹ ∙ bezout)
     where
      II : h ≡ 1
      II = hcf-unique a b (h , is-hcf) (1 , h')

      III : pos h ≡ pos 1
      III = ap pos II

  open import UF-Base --TypeTopology

  coprime-with-division : (a b c : ℕ) → coprime a b → a ℕ∣ b ℕ* c → a ℕ∣ c
  coprime-with-division a b c coprime (α , αₚ) = I (coprime-bezout a b coprime)
   where
    I : Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y → a ℕ∣ c
    I ((x , y) , e₁) = pos-div-to-nat-div a c IV
     where 
      II : pos a * (x * pos c) + (pos b * pos c) * y ≡ pos c
      II = pos a * (x * pos c) + (pos b * pos c) * y ≡⟨ ap₂ _+_ (ℤ*-assoc (pos a) x (pos c)) (ℤ*-comm (pos b * pos c) y) ⟩
           pos a * x * pos c + y * (pos b * pos c)   ≡⟨ ap (λ - → pos a * x * pos c + -) (ℤ*-assoc y (pos b) (pos c)) ⟩
           pos a * x * pos c + y * pos b * pos c     ≡⟨ distributivity-mult-over-ℤ (pos a * x) (y * pos b) (pos c) ⁻¹ ⟩
           (pos a * x + y * pos b) * pos c           ≡⟨ ap (λ - → (pos a * x + -) * pos c) (ℤ*-comm y (pos b)) ⟩
           (pos a * x + pos b * y) * pos c           ≡⟨ ap (_* pos c) (e₁ ⁻¹) ⟩
           pos 1 * pos c                             ≡⟨ ℤ-mult-left-id (pos c) ⟩
           pos c                                     ∎

      III : pos a ∣ pos a * (x * pos c) + (pos b * pos c) * y
      III = ℤ-∣-respects-addition-of-multiples (pos a) (pos a) (pos b * pos c) (x * pos c) y i ii
       where
        i : pos a ∣ pos a
        i = pos 1 , refl

        ii : pos a ∣ (pos b * pos c)
        ii = pos α , δ
         where
          δ : pos a * pos α ≡ pos b * pos c
          δ = pos a * pos α ≡⟨ pos-multiplication-equiv-to-ℕ a α ⟩
              pos (a ℕ* α)  ≡⟨ ap pos αₚ ⟩
              pos (b ℕ* c)  ≡⟨ pos-multiplication-equiv-to-ℕ b c ⁻¹ ⟩
              pos b * pos c ∎

      IV : pos a ∣ pos c
      IV = transport (pos a ∣_) II III
\end{code}

\begin{code}
 module RncRationals where
  open RIntegers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_)

  ℚₙ : 𝓤₀ ̇
  ℚₙ = ℤ × ℕ

  open import DiscreteAndSeparated --TypeTopology
  open import UF-Miscelanea --TypeTopology
  open RIntegersProperties

  ℚₙ-is-discrete : is-discrete ℚₙ
  ℚₙ-is-discrete = Σ-is-discrete ℤ-is-discrete λ _ → ℕ-is-discrete

  open import UF-Subsingletons --TypeTopology

  ℚₙ-is-set : is-set ℚₙ
  ℚₙ-is-set = discrete-types-are-sets ℚₙ-is-discrete

  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)

  _ℚₙ'+_ : ℚₙ → ℚₙ → ℚₙ
  (x , a) ℚₙ'+ (y , b) = (x ℤ* pos b) ℤ+ (y ℤ* pos a) , a ℕ* b 

  open import UF-Base --TypeTopology

  ℚₙ'+-comm : (a b : ℚₙ) → a ℚₙ'+ b ≡ b ℚₙ'+ a
  ℚₙ'+-comm (x , a) (y , b) = ap₂ (λ z z' → z , z') (ℤ+-comm (x ℤ* pos b) (y ℤ* pos a)) (mult-commutativity a b)

  ℚₙ'+-assoc : (a b c : ℚₙ) → (a ℚₙ'+ b) ℚₙ'+ c ≡ a ℚₙ'+ (b ℚₙ'+ c)
  ℚₙ'+-assoc (x , y) (x' , y') (x'' , y'') = ap₂ (λ z z' → z , z') I II
   where
    I : (((x ℤ* (pos y')) ℤ+ (x' ℤ* (pos y))) ℤ* pos y'') ℤ+ (x'' ℤ* pos (y ℕ* y')) ≡ (x ℤ* pos (y' ℕ* y'')) ℤ+ (((x' ℤ* pos y'') ℤ+ (x'' ℤ* pos y')) ℤ* pos y)
    I = (x ℤ* pos y' ℤ+ x' ℤ* pos y) ℤ* pos y'' ℤ+ x'' ℤ* pos (y ℕ* y')                  ≡⟨ ap₂ (λ z z' → z ℤ+ z') (distributivity-mult-over-ℤ (x ℤ* pos y') (x' ℤ* pos y) (pos y'')) (ap (x'' ℤ*_) (pos-multiplication-equiv-to-ℕ y y') ⁻¹)                            ⟩
        x ℤ* pos y' ℤ* pos y'' ℤ+ x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* (pos y ℤ* pos y')     ≡⟨ ℤ+-assoc ((x ℤ* pos y') ℤ* pos y'') ((x' ℤ* pos y) ℤ* pos y'') ((x'' ℤ* (pos y ℤ* pos y')))                                                                                 ⟩ 
        x ℤ* pos y' ℤ* pos y'' ℤ+ (x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* (pos y ℤ* pos y'))   ≡⟨ ap₂ (λ z z' → z ℤ+ z') (ℤ*-assoc x (pos y') (pos y'') ⁻¹) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm x' (pos y))) (ap (x'' ℤ*_) (ℤ*-comm (pos y) (pos y'))))         ⟩
        x ℤ* (pos y' ℤ* pos y'') ℤ+ (pos y ℤ* x' ℤ* pos y'' ℤ+ x'' ℤ* (pos y' ℤ* pos y)) ≡⟨ ap₂ (λ z z' → z ℤ+ z') (ap (x ℤ*_) (pos-multiplication-equiv-to-ℕ y' y'')) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm (pos y) x')) (ℤ*-assoc x'' (pos y') (pos y)))  ⟩
        x ℤ* pos (y' ℕ* y'') ℤ+ (x' ℤ* pos y ℤ* pos y'' ℤ+ x'' ℤ* pos y' ℤ* pos y)       ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (ap₂ (λ z z' → z ℤ+ z') (ap (_ℤ* pos y'') (ℤ*-comm x' (pos y))) (ℤ*-comm (x'' ℤ* pos y') (pos y)))                                          ⟩
        x ℤ* pos (y' ℕ* y'') ℤ+ (pos y ℤ* x' ℤ* pos y'' ℤ+ pos y ℤ* (x'' ℤ* pos y'))     ≡⟨ ap (λ z →  ((x ℤ* pos (y' ℕ* y'')) ℤ+ (z ℤ+ (pos y ℤ* (x'' ℤ* pos y'))))) (ℤ*-assoc (pos y) x' (pos y'') ⁻¹)                                                                ⟩
        x ℤ* pos (y' ℕ* y'') ℤ+ (pos y ℤ* (x' ℤ* pos y'') ℤ+ pos y ℤ* (x'' ℤ* pos y'))   ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (distributivity-mult-over-ℤ' (x' ℤ* pos y'') (x'' ℤ* pos y') (pos y) ⁻¹)                                                                    ⟩
        x ℤ* pos (y' ℕ* y'') ℤ+ pos y ℤ* (x' ℤ* pos y'' ℤ+ x'' ℤ* pos y')                ≡⟨ ap ((x ℤ* pos (y' ℕ* y'')) ℤ+_) (ℤ*-comm (pos y) ((x' ℤ* pos y'') ℤ+ (x'' ℤ* pos y')))                                                                                      ⟩
        x ℤ* pos (y' ℕ* y'') ℤ+ (x' ℤ* pos y'' ℤ+ x'' ℤ* pos y') ℤ* pos y                ∎ 

    II : y ℕ* y' ℕ* y'' ≡ y ℕ* (y' ℕ* y'')
    II = mult-associativity y y' y''

  open import NaturalNumbers-Properties renaming (pred to ℕpred) --TypeTopology

  _+_ : ℚₙ → ℚₙ → ℚₙ
  (x , y) + (x' , y') = f ((x , succ y) ℚₙ'+ (x' , succ y')) --(x ℤ* pos (succ y')) ℤ+ (x' ℤ* pos (succ y)) , ℕpred (succ y ℕ* succ y')
   where
    f : ℚₙ → ℚₙ
    f (a , b) = a , (ℕpred b)

  open import NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology
  open RMoreNaturalProperties 

  ℚₙ+-comm : (p q : ℚₙ) → p + q ≡ q + p
  ℚₙ+-comm (x , a) (y , b) = ap₂ _,_ (ap pr₁ e) (ap ℕpred (ap pr₂ e))
   where
    e : ((x , succ a) ℚₙ'+ (y , succ b)) ≡ ((y , succ b) ℚₙ'+ (x , succ a))
    e = ℚₙ'+-comm (x , (succ a)) (y , (succ b))

  ℚₙ+-assoc-lemma : (x y : ℕ) → Σ z ꞉ ℕ , succ z ≡ (succ x) ℕ* (succ y) 
  ℚₙ+-assoc-lemma x = induction base step
   where
    base : Σ z ꞉ ℕ , succ z ≡ succ x ℕ* 1
    base = x , refl

    step : (k : ℕ)
         → Σ z ꞉ ℕ , succ z ≡ succ x ℕ* succ k
         → Σ z ꞉ ℕ , succ z ≡ succ x ℕ* succ (succ k)
    step k (z , p) = (x ℕ+ 1) ℕ+ z , I
     where
      I : succ (x ℕ+ 1 ℕ+ z) ≡ succ x ℕ* succ (succ k)
      I = succ (x ℕ+ 1 ℕ+ z) ≡⟨ addition-right-succ (succ x) z ⁻¹ ⟩
          succ x ℕ+ succ z                     ≡⟨ ap (succ x ℕ+_) p ⟩
          succ x ℕ+ (succ x ℕ+ succ x ℕ* k)    ≡⟨ refl              ⟩
          succ x ℕ* succ (succ k)              ∎

  denom-setup : (a b : ℕ) →  pos (succ (ℕpred (succ a ℕ* succ b))) ≡ pos (succ a) ℤ* pos (succ b)
  denom-setup a b = pos (succ (ℕpred (succ a ℕ* succ b))) ≡⟨ ap pos (succ-pred-multiplication a b ⁻¹) ⟩
                    pos (succ a ℕ* succ b)               ≡⟨ pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹ ⟩
                    pos (succ a) ℤ* pos (succ b) ∎

  ℚₙ+-assoc : (a b c : ℚₙ) → (a + b) + c ≡ a + (b + c)
  ℚₙ+-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
   where
    left : ℚₙ
    left = (x , a) + (y , b)

    right : ℚₙ
    right = (y , b) + (z , c)

    α δ : ℤ
    α = pr₁ left
    δ = pr₁ right

    β γ : ℕ
    β = pr₂ left
    γ = pr₂ right

    e : (((x , succ a) ℚₙ'+ (y , succ b)) ℚₙ'+ (z , succ c)) ≡ ((x , succ a) ℚₙ'+ ((y , succ b) ℚₙ'+ (z , succ c)))
    e = (ℚₙ'+-assoc (x , (succ a)) (y , succ b) (z , succ c))

    I : α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ (ℕpred (succ a ℕ* succ b))) ≡ x ℤ* pos (succ (ℕpred (succ b ℕ* succ c))) ℤ+ δ ℤ* pos (succ a)
    I = α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ (ℕpred (succ a ℕ* succ b))) ≡⟨ ap (λ - → α ℤ* pos (succ c) ℤ+ z ℤ* pos -) ((succ-pred-multiplication a b ⁻¹)) ⟩
        α ℤ* pos (succ c) ℤ+ z ℤ* pos (succ a ℕ* succ b)                 ≡⟨ ap pr₁ e ⟩
        x ℤ* pos (succ b ℕ* succ c) ℤ+ δ ℤ* pos (succ a)                 ≡⟨ ap (λ - →  x ℤ* pos - ℤ+ δ ℤ* pos (succ a)) (succ-pred-multiplication b c) ⟩
        x ℤ* pos (succ (ℕpred (succ b ℕ* succ c))) ℤ+ δ ℤ* pos (succ a) ∎

    II : ℕpred (succ (ℕpred (succ a ℕ* (succ b))) ℕ* succ c) ≡ ℕpred (succ a ℕ* succ (ℕpred (succ b ℕ+ succ b ℕ* c)))
    II = ℕpred (succ (ℕpred (succ a ℕ* succ b)) ℕ* succ c) ≡⟨ ap (λ - → ℕpred (- ℕ* succ c)) (succ-pred-multiplication a b ⁻¹) ⟩
         ℕpred ((succ a ℕ* succ b) ℕ* succ c) ≡⟨ ap ℕpred (ap pr₂ e) ⟩
         ℕpred (succ a ℕ* (succ b ℕ* succ c)) ≡⟨ ap (λ - → ℕpred (succ a ℕ* -)) (succ-pred-multiplication b c) ⟩
         ℕpred (succ a ℕ* succ (ℕpred (succ b ℕ* succ c))) ∎

  open RIntegersOrder renaming (_<_ to _ℤ<_ ; _>_ to _ℤ>_) 

  _<_ _>_ : ℚₙ → ℚₙ → 𝓤₀ ̇
  (x , a) < (y , b) = (x ℤ* pos (succ b)) ℤ< (y ℤ* pos (succ a))
  p > q = q < p

  ℚₙ<-is-prop : (p q : ℚₙ) → is-prop (p < q)
  ℚₙ<-is-prop (x , a) (y , b) = ℤ<-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

  ℚₙ-trans : (p q r : ℚₙ) → p < q → q < r → p < r
  ℚₙ-trans (x , a) (y , b) (z , c) α β = ordering-right-cancellable (x ℤ* pos (succ c)) (z ℤ* pos (succ a)) (pos (succ b)) ⋆ I
   where
    I : ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ℤ< ((z ℤ* pos (succ a)) ℤ* pos (succ b))
    I = ℤ<-trans ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ((y ℤ* pos (succ a)) ℤ* pos (succ c)) ((z ℤ* pos (succ a)) ℤ* pos (succ b)) i ii
     where
      i : ((x ℤ* pos (succ c)) ℤ* pos (succ b)) ℤ< ((y ℤ* pos (succ a)) ℤ+ ((y ℤ* pos (succ a)) ℤ* pos c))
      i = transport (λ z → z ℤ< ((y ℤ* pos (succ a)) ℤ+ ((y ℤ* pos (succ a)) ℤ* pos c))) ϕ θ
       where
        ϕ : ((x ℤ* pos (succ b)) ℤ* pos (succ c)) ≡ ((x ℤ* pos (succ c)) ℤ* pos (succ b))
        ϕ = ℤ-mult-rearrangement x (pos (succ b)) (pos (succ c))

        θ : ((x ℤ* pos (succ b)) ℤ* pos (succ c)) ℤ< ((y ℤ* pos (succ a)) ℤ* pos (succ c))
        θ = positive-multiplication-preserves-order (x ℤ* pos (succ b)) (y ℤ* pos (succ a)) (pos (succ c)) ⋆ α
      ii : ((y ℤ* pos (succ a)) ℤ* pos (succ c)) ℤ< ((z ℤ* pos (succ a)) ℤ* pos (succ b))
      ii = transport₂ (λ s s' → s ℤ< s') γ₁ γ₂ γ₃
       where
        γ₁ : ((y ℤ* pos (succ c)) ℤ* pos (succ a)) ≡ ((y ℤ* pos (succ a)) ℤ* pos (succ c))
        γ₁ = ℤ-mult-rearrangement y (pos (succ c)) (pos (succ a))

        γ₂ : ((z ℤ* pos (succ b)) ℤ* pos (succ a)) ≡ ((z ℤ* pos (succ a)) ℤ* pos (succ b))
        γ₂ = ℤ-mult-rearrangement z (pos (succ b)) (pos (succ a))

        γ₃ : ((y ℤ* pos (succ c)) ℤ* pos (succ a)) ℤ< ((z ℤ* pos (succ b)) ℤ* pos (succ a))
        γ₃ = positive-multiplication-preserves-order (y ℤ* pos (succ c)) (z ℤ* pos (succ b)) (pos (succ a)) ⋆ β

  ℚₙ-less-than-pos-addition : (p (y , b) : ℚₙ) → greater-than-zero y → p < (p + (y , b))
  ℚₙ-less-than-pos-addition (x , a) (y , b) p = f (III) 
   where
    a' b' : ℤ
    a' = pos (succ a)
    b' = pos (succ b)

    III : Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* (a' ℤ* b') ℤ+ (y ℤ* a') ℤ* a')
    III = ℤ<-less-than-pos-addition (x ℤ* (a' ℤ* b')) ((y ℤ* a') ℤ* a') (greater-than-zero-mult-trans (y ℤ* a') (a') (greater-than-zero-mult-trans y (a') p (pos-succ-greater-than-zero a)) (pos-succ-greater-than-zero a))

    f : Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* (a' ℤ* b') ℤ+ (y ℤ* a') ℤ* a')
      → Σ c ꞉ ℤ , greater-than-zero c × (x ℤ* pos (succ (ℕpred (succ a ℕ* succ b))) ℤ+ c ≡ (x ℤ* b' ℤ+ (y ℤ* a')) ℤ* a')
    f (c , (g , p)) = c , g , transport₂ (λ z z' → z ≡ z') IV V p
     where
      VI : succ (ℕpred (succ a ℕ* succ b)) ≡ succ a ℕ* succ b
      VI = succ-pred-multiplication a b ⁻¹

      IV : x ℤ* (a' ℤ* b') ℤ+ c ≡ x ℤ* pos (succ (ℕpred (succ a ℕ* succ b))) ℤ+ c
      IV = x ℤ* (a' ℤ* b') ℤ+ c        ≡⟨ ap (λ z → x ℤ* z ℤ+ c) (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⟩
           x ℤ* pos (succ a ℕ* succ b) ℤ+ c                ≡⟨ ap (λ z → (x ℤ* z) ℤ+ c) (ap pos (VI ⁻¹)) ⟩
           x ℤ* pos (succ (ℕpred (succ a ℕ* succ b))) ℤ+ c ∎

      V : x ℤ* (a' ℤ* b') ℤ+ y ℤ* a' ℤ* a' ≡ (x ℤ* b' ℤ+ y ℤ* a') ℤ* a'
      V = x ℤ* (a' ℤ* b') ℤ+ y ℤ* a' ℤ* a' ≡⟨ ap (λ z → x ℤ* z ℤ+ y ℤ* a' ℤ* a') (ℤ*-comm (a') (b')) ⟩
          x ℤ* (b' ℤ* a') ℤ+ y ℤ* a' ℤ* a' ≡⟨  ap (_ℤ+ y ℤ* a' ℤ* a') (ℤ*-assoc x (b') (a')) ⟩
          (x ℤ* b') ℤ* a' ℤ+ y ℤ* a' ℤ* a' ≡⟨ distributivity-mult-over-ℤ (x ℤ+ x ℤ* pos b) (y ℤ+ y ℤ* pos a) (a') ⁻¹ ⟩
          (x ℤ* b' ℤ+ y ℤ* a') ℤ* a'                 ∎

  _*_ : ℚₙ → ℚₙ → ℚₙ
  (x , a) * (y , b) = (x ℤ* y) , (ℕpred (succ a ℕ* succ b))

  ℚₙ*-comm : (p q : ℚₙ) → p * q ≡ q * p
  ℚₙ*-comm (x , a) (y , b) = ap₂ _,_ I II
   where
    I : x ℤ* y ≡ y ℤ* x
    I = ℤ*-comm x y

    II : ℕpred (succ a ℕ* succ b) ≡ ℕpred (succ b ℕ* succ a)
    II = ap ℕpred (mult-commutativity (succ a) (succ b))

  ℚₙ*-assoc : (p q r : ℚₙ) → (p * q) * r ≡ p * (q * r)
  ℚₙ*-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
   where
    I : x ℤ* y ℤ* z ≡ x ℤ* (y ℤ* z)
    I = ℤ*-assoc x y z ⁻¹

    a' b' c' : ℕ
    a' = succ a
    b' = succ b
    c' = succ c

    II : ℕpred (succ (ℕpred (a' ℕ* b')) ℕ* c') ≡ ℕpred (a' ℕ* succ (ℕpred (b' ℕ* c')))
    II = ℕpred (succ (ℕpred (a' ℕ* b')) ℕ* c') ≡⟨ ap (λ - → ℕpred (- ℕ* c')) (succ-pred-multiplication a b ⁻¹) ⟩
         ℕpred ((a' ℕ* b') ℕ* c') ≡⟨ ap ℕpred (mult-associativity a' b' c') ⟩
         ℕpred (a' ℕ* (b' ℕ* c')) ≡⟨ ap (λ - → ℕpred (a' ℕ* -)) (succ-pred-multiplication b c) ⟩
         ℕpred (a' ℕ* succ (ℕpred (b' ℕ* c'))) ∎

\end{code}

\begin{code}

 module RFieldAxioms where 
  open import UF-Subsingletons

  distributive : {X : 𝓤 ̇ } → (X → X → X) → (X → X → X) → 𝓤 ̇
  distributive _⊕_ _⊙_ = ∀ x y z → x ⊙ (y ⊕ z) ≡ ((x ⊙ y) ⊕ (x ⊙ z))

  field-structure : 𝓤 ̇ → 𝓤 ̇
  field-structure F = (F → F → F) × (F → F → F)

  field-axioms : (F : 𝓤 ̇) → field-structure F → 𝓤 ̇
  field-axioms F (_⊕_ , _⊙_) = is-set F × associative _⊕_
                                         × associative _⊙_
                                         × commutative _⊕_
                                         × commutative _⊙_
                                         × distributive _⊕_ _⊙_
                                         × (Σ (e , e') ꞉ F × F , (¬ (e ≡ e') × left-neutral e _⊕_
                                                                             × ((x : F) → Σ x' ꞉ F , x ⊕ x' ≡ e) 
                                                                             × left-neutral e' _⊙_
                                                                             × ((x : F) → ¬ (x ≡ e) → Σ x' ꞉ F , x ⊙ x' ≡ e' )))

  Field-structure : 𝓤 ̇ → 𝓤 ̇
  Field-structure F = Σ fs ꞉ field-structure F , field-axioms F fs

  ordered-field-structure : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F) → (fa : field-axioms F fs) → 𝓤 ⊔ (𝓥 ⁺) ̇
  ordered-field-structure {𝓤} {𝓥} F fs fa = (F → F → 𝓥 ̇)


  ordered-field-axioms : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F) → (fa : field-axioms F fs) →  ordered-field-structure { 𝓤 } { 𝓥 } F fs fa → 𝓤 ⊔ 𝓥 ̇
  ordered-field-axioms {𝓤} {𝓥} F (_⊕_ , _⊙_) (s , a , a' , c , c' , d , (e , e') , i) _<_ = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z))
                                                                                        × ((x y : F) → e < x → e < y → e < (x ⊙ y))

  Ordered-field-structure : {𝓤 𝓥 : Universe} → (F : 𝓤 ̇) → Field-structure F → 𝓤 ⊔ (𝓥 ⁺) ̇
  Ordered-field-structure {𝓤} {𝓥} F (fs , fa) = Σ ofa ꞉ (ordered-field-structure {𝓤} {𝓥} F fs fa) , ordered-field-axioms {𝓤} {𝓥} F fs fa ofa

\end{code}

\begin{code}

 module RRationals where
  open RHCF
  open RIntegers renaming (_*_ to _ℤ*_ ; _+_ to _ℤ+_ ; -_ to ℤ-_)
  open RncRationals renaming (_+_ to _ℚₙ+_ ; _<_ to _ℚₙ<_ ; _>_ to _ℚₙ>_ ; _*_ to _ℚₙ*_)

  is-in-lowest-terms : ℚₙ → 𝓤₀ ̇
  is-in-lowest-terms (x , y) = coprime (abs x) (succ y)

  open import UF-Subsingletons --TypeTopology
  open import UF-FunExt --TypeTopology

  is-in-lowest-terms-is-prop : Fun-Ext → (q : ℚₙ) → is-prop (is-in-lowest-terms q)
  is-in-lowest-terms-is-prop fe (x , y) = coprime-is-prop fe (abs x) (succ y)

  ℚ : 𝓤₀ ̇
  ℚ = Σ q ꞉ ℚₙ , is-in-lowest-terms q

  open import DiscreteAndSeparated --TypeTopology
  open import UF-Miscelanea --TypeTopology

  ℚ-is-discrete : Fun-Ext → is-discrete ℚ
  ℚ-is-discrete fe = Σ-is-discrete ℚₙ-is-discrete λ q x y → inl (is-in-lowest-terms-is-prop fe q x y)

  ℚ-is-set : Fun-Ext → is-set ℚ
  ℚ-is-set fe = discrete-types-are-sets (ℚ-is-discrete fe)

  toℚₙ : ℚ → ℚₙ
  toℚₙ (q , ψ) = q

  open RNaturalsMultiplication renaming (_*_ to _ℕ*_)
  open import NaturalNumbers-Properties --TypeTopology
  open RIntegersProperties

  toℚlemma : ((x , a) : ℚₙ) → Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
  toℚlemma (pos a , b) = f (divbyhcf a (succ b))
   where
    f : Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ≡ a) × (h ℕ* y ≡ succ b)) × coprime x y → _
    f (h      , x , zero   , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
    f (0      , x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-is-zero (succ y)))
    f (succ h , x , succ y , (γ₁ , γ₂) , r) = (((pos x) , y) , r) , h , I , (γ₂ ⁻¹)
     where
      I : pos a ≡ pos (succ h) ℤ* pos x
      I = pos a                 ≡⟨ ap pos γ₁ ⁻¹                                 ⟩                               
          pos (succ h ℕ* x)     ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) x ⁻¹ ⟩
          pos (succ h) ℤ* pos x ∎
  toℚlemma (negsucc a , b) = f (divbyhcf (succ a) (succ b))
   where
    f : ((Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ≡ (succ a)) × (h ℕ* y ≡ succ b)) × coprime x y)) → _
    f (h      , x      , 0      , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
    f (h      , 0      , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero a (γ₁ ⁻¹))
    f (0      , succ x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-is-zero (succ y)))
    f (succ h , succ x , succ y , (γ₁ , γ₂) , r) = (((negsucc x) , y) , r) , (h , (I , (γ₂ ⁻¹)))
     where
      i : pos (succ a) ≡ (pos (succ h) ℤ* pos (succ x))
      i = pos (succ a)                 ≡⟨ ap pos γ₁ ⁻¹                                        ⟩
          pos (succ h ℕ* succ x)       ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ x) ⁻¹ ⟩
          pos (succ h) ℤ* pos (succ x) ∎

      I : negsucc a ≡ pos (succ h) ℤ* negsucc x
      I = negsucc a                        ≡⟨ ap ℤ-_ i                                                     ⟩
          ℤ- pos (succ h) ℤ* pos (succ x)   ≡⟨ subtraction-dist-over-mult (pos (succ h)) (pos (succ x)) ⁻¹ ⟩
          pos (succ h) ℤ* (ℤ- pos (succ x)) ∎

  --feed in ℚₙ
  toℚ : ℚₙ → ℚ
  toℚ q = pr₁ (toℚlemma q)

  zero-ℚ : ℚ
  zero-ℚ = toℚ ((pos zero) , zero)

  1ℚ : ℚ
  1ℚ = toℚ ((pos 1) , 0)

  -1ℚ : ℚ
  -1ℚ = toℚ ((negsucc 0) , 0)

  _+_ : ℚ → ℚ → ℚ
  (p , α) + (q , β) = toℚ (p ℚₙ+ q)

  open import UF-Base --TypeTopology

  ℚ≡-to-ℚₙ≡ : ((p , α) (q , β) : ℚ) → (p , α) ≡ (q , β) → p ≡ q
  ℚ≡-to-ℚₙ≡ (p , α) (q , β) e = pr₁ (from-Σ-≡ e)

  _ℚₙ≈_ : (p q : ℚₙ) → 𝓤₀ ̇
  (x , a) ℚₙ≈ (y , b) = x ℤ* pos (succ b) ≡ (y ℤ* pos (succ a))

  open RNaturalsDivision
  open RIntegersHCF
  open RIntegersOrder renaming (_<_ to _ℤ<_ ; _>_ to _ℤ>_)

  equiv-with-lowest-terms-is-equal : (a b : ℚₙ) -> a ℚₙ≈ b → is-in-lowest-terms a → is-in-lowest-terms b → a ≡ b
  equiv-with-lowest-terms-is-equal (x , a) (y , b) e ((m₁ , m₂) , n) ((m₁' , m₂') , n') = to-×-≡ xyequal abequal
   where
    e' : (x ℤ* pos (succ b)) ≡ (y ℤ* pos (succ a))
    e' = e

    γ : abs (x ℤ* pos (succ b)) ≡ abs (y ℤ* pos (succ a))
    γ = ap abs e'

    δ : abs x ℕ* succ b ≡ abs y ℕ* succ a
    δ = abs x ℕ* abs (pos (succ b)) ≡⟨ abs-over-mult x (pos (succ b))  ⁻¹ ⟩
        abs (x ℤ* pos (succ b))     ≡⟨ γ ⟩
        abs (y ℤ* pos (succ a))     ≡⟨ abs-over-mult y (pos (succ a)) ⟩
        abs y ℕ* abs (pos (succ a)) ∎

    s : (succ a) ∣ ((abs x) ℕ* (succ b))
    s = (abs y) , I
     where
      I : succ a ℕ* abs y ≡ abs x ℕ* succ b
      I = succ a ℕ* abs y ≡⟨ mult-commutativity (succ a) (abs y) ⟩
          abs y ℕ* succ a ≡⟨ δ ⁻¹ ⟩
          abs x ℕ* succ b ∎

    s' : (succ b) ∣ (abs y) ℕ* (succ a)
    s' = (abs x) , I
     where
      I : succ b ℕ* abs x ≡ abs y ℕ* succ a
      I = succ b ℕ* abs x ≡⟨ mult-commutativity (succ b) (abs x) ⟩
          abs x ℕ* succ b ≡⟨ δ ⟩
          abs y ℕ* succ a ∎

    a-divides-b : (succ a) ∣ (succ b)
    a-divides-b = coprime-with-division (succ a) (abs x) (succ b) ((m₂ , m₁) , λ f' (h₁ , h₂) → n f' (h₂ , h₁)) s

    b-divides-a : (succ b) ∣ (succ a)
    b-divides-a = coprime-with-division (succ b) (abs y) (succ a) ((m₂' , m₁') , λ f (h₁ , h₂) → n' f (h₂ , h₁)) s'

    abequal : a ≡ b
    abequal = succ-lc (∣-anti (succ a) (succ b) a-divides-b b-divides-a)

    e'' : x ℤ* pos (succ a) ≡ y ℤ* pos (succ a)
    e'' = ap (x ℤ*_) (ap pos (ap succ abequal)) ∙ e

    xyequal : x ≡ y
    xyequal = ℤ-mult-right-cancellable x y (pos (succ a)) (λ z → z) e''

  equiv-equality : Fun-Ext → (p q : ℚₙ) → p ℚₙ≈ q ⇔ toℚ p ≡ toℚ q
  equiv-equality fe (x , a) (y , b) = I , II
   where
    α : Σ ((x' , a') , p) ꞉ ℚ , Σ h ꞉ ℕ , (x ≡ (pos (succ h) ℤ* x')) × (succ a ≡ succ h ℕ* succ a')
    α = toℚlemma (x , a)

    β : Σ ((y' , b') , p') ꞉ ℚ , Σ h' ꞉ ℕ , (y ≡ (pos (succ h') ℤ* y')) × (succ b ≡ succ h' ℕ* succ b')
    β = toℚlemma (y , b)

    h h' : ℕ
    h = pr₁ (pr₂ α)
    h' = pr₁ (pr₂ β)

    a' b' : ℕ
    a' = pr₂ (pr₁ (pr₁ α))
    b' = pr₂ (pr₁ (pr₁ β))

    x' y' : ℤ
    x' = pr₁ (pr₁ (pr₁ α))
    y' = pr₁ (pr₁ (pr₁ β))

    p : is-in-lowest-terms (x' , a')
    p = pr₂ (pr₁ α)

    p' : is-in-lowest-terms (y' , b')
    p' = pr₂ (pr₁ β)

    αₚ₁ : x ≡ pos (succ h) ℤ* x'
    αₚ₁ = pr₁ (pr₂ (pr₂ α))

    αₚ₂ : succ a ≡ succ h ℕ* succ a'
    αₚ₂ = pr₂ (pr₂ (pr₂ α))

    αₚ₂' : pos (succ a) ≡ pos (succ h) ℤ* pos (succ a')
    αₚ₂' = pos (succ a)                  ≡⟨ ap pos αₚ₂ ⟩
          pos (succ h ℕ* succ a')       ≡⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹ ⟩
          pos (succ h) ℤ* pos (succ a') ∎

    βₚ₁ : y ≡ (pos (succ h') ℤ* y')
    βₚ₁ = pr₁ (pr₂ (pr₂ β))

    βₚ₂ : succ b ≡ succ h' ℕ* succ b'
    βₚ₂ = pr₂ (pr₂ (pr₂ β))

    βₚ₂' : pos (succ b) ≡ pos (succ h') ℤ* (pos (succ b'))
    βₚ₂' = pos (succ b)              ≡⟨ ap pos βₚ₂ ⟩
           pos (succ h' ℕ* succ b') ≡⟨ pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹ ⟩
           pos (succ h') ℤ* pos (succ b') ∎

    I : (x , a) ℚₙ≈ (y , b) → ((x' , a') , p) ≡ ((y' , b') , p')
    I e = to-subtype-≡ (λ z → is-in-lowest-terms-is-prop fe z) (equiv-with-lowest-terms-is-equal (x' , a') (y' , b') f p p')
     where
      f : x' ℤ* (pos (succ b')) ≡ y' ℤ* (pos (succ a'))
      f = ℤ-mult-left-cancellable (x' ℤ* pos (succ b')) (y' ℤ* pos (succ a')) (pos (succ h)) (pos-succ-not-zero h) g
       where
        g : pos (succ h) ℤ* (x' ℤ* (pos (succ b'))) ≡ pos (succ h) ℤ* (y' ℤ* (pos (succ a')))
        g = ℤ-mult-left-cancellable (pos (succ h) ℤ* ((x' ℤ* pos (succ b')))) (pos (succ h) ℤ* (y' ℤ* pos (succ a'))) (pos (succ h')) (pos-succ-not-zero h') k
         where
          k : pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* (pos (succ b')))) ≡ pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* (pos (succ a'))))
          k = pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* pos (succ b')))       ≡⟨ ap (pos (succ h') ℤ*_) (ℤ*-assoc (pos (succ h)) x' (pos (succ b'))) ⟩
              pos (succ h') ℤ* ((pos (succ h) ℤ* x') ℤ* pos (succ b'))       ≡⟨ ap (λ z → pos (succ h') ℤ* (z ℤ* pos (succ b'))) (αₚ₁ ⁻¹) ⟩
              pos (succ h') ℤ* (x ℤ* pos (succ b'))                          ≡⟨ ℤ-mult-rearrangement''' (pos (succ h')) x (pos (succ b')) ⟩
              x ℤ* (pos (succ h') ℤ* pos (succ b'))                          ≡⟨ ap (x ℤ*_) (βₚ₂' ⁻¹) ⟩
              x ℤ* pos (succ b)                                              ≡⟨ e ⟩
              y ℤ* pos (succ a)                                              ≡⟨ ap₂ (λ z z' → z ℤ* z') βₚ₁ αₚ₂' ⟩
              pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))         ≡⟨ ℤ*-assoc (pos (succ h')) y' (pos (succ h) ℤ* pos (succ a')) ⁻¹ ⟩
              pos (succ h') ℤ* (y' ℤ* (pos (succ h) ℤ* pos (succ a')))       ≡⟨ ap (pos (succ h') ℤ*_) (ℤ-mult-rearrangement''' y' (pos (succ h)) (pos (succ a'))) ⟩
              pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* pos (succ a')))       ∎

    II : toℚ (x , a) ≡ toℚ (y , b) → (x , a) ℚₙ≈ (y , b)
    II e = x ℤ* pos (succ b)                                              ≡⟨ ap₂ (λ z z' → z ℤ* z') αₚ₁ (ap pos βₚ₂) ⟩
           ((pos (succ h) ℤ* x') ℤ* pos (succ h' ℕ* succ b'))             ≡⟨ ap₂ (λ z z' → ((pos (succ h) ℤ* z) ℤ* pos (succ h' ℕ* succ z'))) (pr₁ iii) ((pr₂ iii) ⁻¹) ⟩
           ((pos (succ h) ℤ* y') ℤ* pos (succ h' ℕ* succ a'))             ≡⟨ ap (((pos (succ h) ℤ* y')) ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ a')) ⁻¹ ⟩
           ((pos (succ h) ℤ* y') ℤ* (pos (succ h') ℤ* pos (succ a')))     ≡⟨ ℤ-mult-rearrangement'' (pos (succ h')) (pos (succ h)) y' (pos (succ a')) ⟩
           (((pos (succ h') ℤ* y')) ℤ* (pos (succ h) ℤ* pos (succ a')))   ≡⟨ ap (((pos (succ h') ℤ* y')) ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a')) ⟩ 
           ((pos (succ h') ℤ* y')) ℤ* pos (succ h ℕ* succ a')             ≡⟨ ap₂ (λ z z' → z ℤ* z') (pr₁ (pr₂ (pr₂ β)) ⁻¹) (ap pos (pr₂ (pr₂ (pr₂ α)) ⁻¹)) ⟩
           y ℤ* pos (succ a) ∎
      where
       i : Σ δ ꞉ (x' , a') ≡ (y' , b') , transport is-in-lowest-terms δ (pr₂ (toℚ (x , a))) ≡ pr₂ (toℚ (y , b))
       i = from-Σ-≡ e

       ii : x' , a' ≡ y' , b'
       ii = pr₁ i

       iii : (x' ≡ y') × (a' ≡ b')
       iii = from-×-≡' ii

  ≈-refl : (q : ℚₙ) → q ℚₙ≈ q
  ≈-refl q = refl

  ≈-sym : (p q : ℚₙ) → p ℚₙ≈ q → q ℚₙ≈ p
  ≈-sym p q e = e ⁻¹

  ≈-trans : (p q r : ℚₙ) → p ℚₙ≈ q → q ℚₙ≈ r → p ℚₙ≈ r
  ≈-trans (x , a) (y , b) (z , c) e₁ e₂ = ℤ-mult-left-cancellable (x ℤ* pos (succ c)) (z ℤ* pos (succ a)) (pos (succ b)) (pos-succ-not-zero b) III
   where
    I : x ℤ* pos (succ b) ℤ* pos (succ c) ≡ y ℤ* pos (succ a) ℤ* pos (succ c)
    I = ap (_ℤ* pos (succ c)) e₁

    II : pos (succ a) ℤ* (y ℤ* pos (succ c)) ≡ pos (succ a) ℤ* (z ℤ* pos (succ b))
    II = ap (pos (succ a) ℤ*_) e₂

    III : pos (succ b) ℤ* (x ℤ* pos (succ c)) ≡ pos (succ b) ℤ* (z ℤ* pos (succ a))
    III = pos (succ b) ℤ* (x ℤ* pos (succ c)) ≡⟨ ℤ*-assoc (pos (succ b)) x (pos (succ c)) ⟩
          pos (succ b) ℤ* x ℤ* pos (succ c) ≡⟨ ap (_ℤ* pos (succ c)) (ℤ*-comm (pos (succ b)) x) ⟩
          x ℤ* pos (succ b) ℤ* pos (succ c) ≡⟨ I ⟩
          y ℤ* pos (succ a) ℤ* pos (succ c) ≡⟨ ap (_ℤ* pos (succ c)) (ℤ*-comm y (pos (succ a))) ⟩
          pos (succ a) ℤ* y ℤ* pos (succ c) ≡⟨ ℤ*-assoc (pos (succ a)) y (pos (succ c))  ⁻¹ ⟩
          pos (succ a) ℤ* (y ℤ* pos (succ c)) ≡⟨ II ⟩
          pos (succ a) ℤ* (z ℤ* pos (succ b)) ≡⟨ ℤ-mult-rearrangement' z (pos (succ b)) (pos (succ a)) ⟩
          pos (succ b) ℤ* (z ℤ* pos (succ a)) ∎

  ≈-addition : (p q r : ℚₙ) → p ℚₙ≈ q → (p ℚₙ+ r) ℚₙ≈ (q ℚₙ+ r)
  ≈-addition (x , a) (y , b) (z , c) e₁ = III
   where
    I :  pos (succ (pred (succ b ℕ* succ c))) ≡ pos (succ b) ℤ* pos (succ c)
    I = denom-setup b c

    II : pos (succ a) ℤ* pos (succ c) ≡ pos (succ (pred (succ a ℕ* succ c)))
    II = denom-setup a c ⁻¹

    a' b' c' : ℤ
    a' = pos (succ a)
    b' = pos (succ b)
    c' = pos (succ c)

    III : ((x , a) ℚₙ+ (z , c)) ℚₙ≈ ((y , b) ℚₙ+ (z , c))
    III = (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡⟨ ap (λ - → (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* -) I ⟩
          (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c')                             ≡⟨ distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c') ⟩
           x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                ≡⟨ ap₂ _ℤ+_ (ℤ-mult-rearrangement x (c') (b' ℤ* c')) (ℤ-mult-rearrangement z (a') (b' ℤ* c'))  ⟩
           x ℤ* (b' ℤ* c') ℤ* c' ℤ+ z ℤ* (b' ℤ* c') ℤ* a'                ≡⟨ ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ*-assoc x b' c')) (ap (_ℤ* a') (ℤ*-assoc z b' c')) ⟩
           x ℤ* b' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* c' ℤ* a'                    ≡⟨ ap₂ _ℤ+_ (ap (λ - → -  ℤ* c' ℤ* c') e₁) (ℤ*-assoc (z ℤ* b') c' a' ⁻¹) ⟩
           y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* (c' ℤ* a')                  ≡⟨ ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ-mult-rearrangement y a' c')) (ap (λ - → z ℤ* b' ℤ* -) (ℤ*-comm c' a')) ⟩
           y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                  ≡⟨ ap (_ℤ+ z ℤ* b' ℤ* (a' ℤ* c')) (ℤ*-assoc (y ℤ* c') a' c' ⁻¹) ⟩
           y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                ≡⟨ distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹ ⟩
          (y ℤ* c' ℤ+ z ℤ* b') ℤ* (a' ℤ* c')                             ≡⟨ ap (λ - → (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* -) II ⟩
          (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎

  ≈-toℚ : (p : ℚₙ) → p ℚₙ≈ toℚₙ (toℚ p)
  ≈-toℚ (x , a) = conclusion
   where
    right-l : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
    right-l = toℚlemma (x , a)

    right : ℚ
    right = toℚ (x , a)

    x' : ℤ
    x' = pr₁ (pr₁ right)
    a' : ℕ
    a' = pr₂ (pr₁ right)

    h : ℕ
    h = pr₁ (pr₂ right-l) 

    conclusion : x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
    conclusion = x ℤ* pos (succ a')                    ≡⟨ ap (_ℤ* pos (succ a')) (pr₁ (pr₂ (pr₂ right-l))) ⟩
                 (pos (succ h)) ℤ* x' ℤ* pos (succ a') ≡⟨ ap (_ℤ* pos (succ a')) (ℤ*-comm (pos (succ h)) x') ⟩
                 x' ℤ* pos (succ h) ℤ* pos (succ a')   ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ a')) ⁻¹ ⟩
                 x' ℤ* (pos (succ h) ℤ* pos (succ a')) ≡⟨ ap (x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a')) ⟩
                 x' ℤ* pos ((succ h) ℕ* succ a')       ≡⟨ ap (x' ℤ*_) (ap pos (pr₂ (pr₂ (pr₂ right-l))) ⁻¹ ) ⟩
                 x' ℤ* pos (succ a) ∎

  ℚ+-comm : (a b : ℚ) → a + b ≡ b + a
  ℚ+-comm ((x , a) , p) ((y , b) , q) = ap toℚ I
   where
    I : ((x , a) ℚₙ+ (y , b)) ≡ ((y , b) ℚₙ+ (x , a))
    I = ℚₙ+-comm (x , a) (y , b)

  toℚ-over-addition : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ+ q) ≡ toℚ p + toℚ q
  toℚ-over-addition fe (x , a) (y , b) = helper I
   where
    p' = toℚ (x , a)
    q' = toℚ (y , b)

    x' y' : ℤ
    x' = pr₁ (pr₁ p')
    y' = pr₁ (pr₁ q')

    a' b' : ℕ
    a' = pr₂ (pr₁ p')
    b' = pr₂ (pr₁ q')

    helper : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b')) → toℚ ((x , a) ℚₙ+ (y , b)) ≡ (toℚ (x , a) + toℚ (y , b))
    helper = pr₁ (equiv-equality fe ((x , a) ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y' , b')))

    aux₁ : (x , a) ℚₙ≈ (x' , a')
    aux₁ = ≈-toℚ (x , a)

    aux₂ : (y , b) ℚₙ≈ (y' , b')
    aux₂ = ≈-toℚ (y , b)

    aux₃ : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y , b))
    aux₃ = ≈-addition (x , a) (x' , a') (y , b) aux₁

    aux₄ : ((y' , b') ℚₙ+ (x' , a')) ℚₙ≈ ((y , b) ℚₙ+ (x' , a'))
    aux₄ = ≈-addition (y' , b') (y , b) (x' , a') (≈-sym (y , b) (y' , b') aux₂)

    aux₅ : ((y , b) ℚₙ+ (x' , a')) ℚₙ≈ ((y' , b') ℚₙ+ (x' , a'))
    aux₅ = ≈-sym ((y' , b') ℚₙ+ (x' , a')) ((y , b) ℚₙ+ (x' , a')) aux₄

    aux₆ : ((x' , a') ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b'))
    aux₆ = transport₂ _ℚₙ≈_ (ℚₙ+-comm (y , b) (x' , a')) (ℚₙ+-comm (y' , b') (x' , a')) aux₅

    I : ((x , a) ℚₙ+ (y , b)) ℚₙ≈ ((x' , a') ℚₙ+ (y' , b'))
    I = ≈-trans ((x , a) ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y , b)) ((x' , a') ℚₙ+ (y' , b')) aux₃ aux₆

  q-has-qn : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚₙ , q ≡ toℚ q'
  q-has-qn fe (q , p) = q , (to-subtype-≡ (is-in-lowest-terms-is-prop fe) (equiv-with-lowest-terms-is-equal q q' (≈-toℚ q) p (pr₂ right)))
   where
    right : ℚ
    right = toℚ q

    q' : ℚₙ
    q' = pr₁ right

  ℚ+-assoc : Fun-Ext → (p q r : ℚ) → (p + q) + r ≡ p + (q + r)
  ℚ+-assoc fe (x , p) (y , q) (z , r) = V
   where
    I II : ℚ
    I = toℚ (x ℚₙ+ y)
    II = toℚ (y ℚₙ+ z) 

    III : Σ r' ꞉ ℚₙ , (z , r ≡ toℚ r')
    III = q-has-qn fe ((z , r))

    IV : Σ p' ꞉ ℚₙ , (x , p ≡ toℚ p')
    IV = q-has-qn fe ((x , p))

    V : (toℚ (x ℚₙ+ y) + (z , r)) ≡ ((x , p) + ((y , q) + (z , r)))
    V = (I + (z , r))                     ≡⟨ ap (I +_) (pr₂ III) ⟩
          (I + toℚ (pr₁ III))                ≡⟨ toℚ-over-addition fe (x ℚₙ+ y) (pr₁ III) ⁻¹  ⟩
          toℚ ((x ℚₙ+ y) ℚₙ+ z)             ≡⟨ ap toℚ (ℚₙ+-assoc x y z) ⟩
          toℚ (x ℚₙ+ (y ℚₙ+ z))             ≡⟨ toℚ-over-addition fe (pr₁ IV) (y ℚₙ+ z) ⟩
          (toℚ (pr₁ IV) + II)                ≡⟨ ap (_+ II) (pr₂ IV ⁻¹) ⟩
          ((x , p) + II) ∎

  _*_ : ℚ → ℚ → ℚ
  (p , _) * (q , _) = toℚ (p ℚₙ* q)

  ≈-over-* : (p q r : ℚₙ) → p ℚₙ≈ q → (p ℚₙ* r) ℚₙ≈ (q ℚₙ* r)
  ≈-over-* (x , a) (y , b) (z , c) e = I
   where
    a' b' c' : ℤ
    a' = pos (succ a)
    b' = pos (succ b)
    c' = pos (succ c)

    I : x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡ y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c)))
    I = x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c))) ≡⟨ ap (λ - → x ℤ* z ℤ* -) (denom-setup b c) ⟩
        x ℤ* z ℤ* (b' ℤ* c')                           ≡⟨ ℤ*-assoc (x ℤ* z) b' c' ⟩
        x ℤ* z ℤ* b' ℤ* c'                             ≡⟨ ap (_ℤ* c') (ℤ-mult-rearrangement x z b') ⟩
        x ℤ* b' ℤ* z ℤ* c'                             ≡⟨ ap (λ - → - ℤ* z ℤ* c') e ⟩
        y ℤ* a' ℤ* z ℤ* c'                             ≡⟨ ap (_ℤ* c') (ℤ*-assoc y a' z ⁻¹ ) ⟩
        y ℤ* (a' ℤ* z) ℤ* c'                           ≡⟨ ap (λ - → y ℤ* - ℤ* c') (ℤ*-comm a' z) ⟩
        y ℤ* (z ℤ* a') ℤ* c'                           ≡⟨ ap (_ℤ* c') (ℤ*-assoc y z a') ⟩
        y ℤ* z ℤ* a' ℤ* c'                             ≡⟨ ℤ*-assoc (y ℤ* z) a' c' ⁻¹ ⟩ 
        y ℤ* z ℤ* (a' ℤ* c')                           ≡⟨ ap (λ - → (y ℤ* z ℤ* -)) (denom-setup a c ⁻¹) ⟩
        y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎

  toℚ-over-mult : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ* q) ≡ toℚ p * toℚ q
  toℚ-over-mult fe (x , a) (y , b) = helper I
   where
    p' = toℚ (x , a)
    q' = toℚ (y , b)

    x' y' : ℤ
    x' = pr₁ (pr₁ p')
    y' = pr₁ (pr₁ q')

    a' b' : ℕ
    a' = pr₂ (pr₁ p')
    b' = pr₂ (pr₁ q') 

    helper : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b')) → toℚ ((x , a) ℚₙ* (y , b)) ≡ toℚ ((x' , a') ℚₙ* (y' , b'))
    helper = pr₁ (equiv-equality fe ((x , a) ℚₙ* (y , b)) ((x' , a') ℚₙ* (y' , b')))

    aux₁ : (x , a) ℚₙ≈ (x' , a')
    aux₁ = ≈-toℚ (x , a)

    aux₂ : (y , b) ℚₙ≈ (y' , b')
    aux₂ = ≈-toℚ (y , b)

    aux₃ : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y , b))
    aux₃ = ≈-over-* (x , a) (x' , a') (y , b) aux₁

    aux₄ : ((y' , b') ℚₙ* (x' , a')) ℚₙ≈ ((y , b) ℚₙ* (x' , a'))
    aux₄ = ≈-over-* (y' , b') (y , b) (x' , a') (≈-sym (y , b ) (y' , b') aux₂)

    aux₅ : ((y , b) ℚₙ* (x' , a')) ℚₙ≈ ((y' , b') ℚₙ* (x' , a'))
    aux₅ = ≈-sym ((y' , b') ℚₙ* (x' , a')) ((y , b) ℚₙ* (x' , a')) aux₄

    aux₆ : ((x' , a') ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b'))
    aux₆ = transport₂ _ℚₙ≈_ (ℚₙ*-comm (y , b) (x' , a')) (ℚₙ*-comm (y' , b') (x' , a')) aux₅

    I : ((x , a) ℚₙ* (y , b)) ℚₙ≈ ((x' , a') ℚₙ* (y' , b'))
    I = ≈-trans ((x , a) ℚₙ* (y , b)) ((x' , a') ℚₙ* (y , b)) ((x' , a') ℚₙ* (y' , b')) aux₃ aux₆

  ℚ*-comm : (p q : ℚ) → p * q ≡ q * p
  ℚ*-comm (p , _) (q , _) = ap toℚ (ℚₙ*-comm p q)

  ℚ*-assoc : Fun-Ext → (p q r : ℚ) → (p * q) * r ≡ p * (q * r)
  ℚ*-assoc fe (x , p) (y , q) (z , r) = III
   where
    left : ℚ
    left = (x , p) * (y , q)

    right : ℚ
    right = (y , q) * (z , r)

    I : Σ l ꞉ ℚₙ , (z , r ≡ toℚ l)
    I = q-has-qn fe (z , r)

    II : Σ t ꞉ ℚₙ , (x , p ≡ toℚ t)
    II = q-has-qn fe (x , p)

    l t : ℚₙ
    l = pr₁ I
    t = pr₁ II

    III : toℚ (x ℚₙ* y) * (z , r) ≡ ((x , p) * toℚ (y ℚₙ* z))
    III = (left * (z , r))      ≡⟨ ap (left *_) (pr₂ I) ⟩
          left * toℚ z          ≡⟨ toℚ-over-mult fe (x ℚₙ* y) z ⁻¹ ⟩
          toℚ ((x ℚₙ* y) ℚₙ* z) ≡⟨ ap toℚ (ℚₙ*-assoc x y z) ⟩
          toℚ (x ℚₙ* (y ℚₙ* z)) ≡⟨ toℚ-over-mult fe x (y ℚₙ* z) ⟩
          (toℚ x * right)       ≡⟨ ap (_* right) (pr₂ II ⁻¹) ⟩
          ((x , p) * right) ∎

  _<_ : ℚ → ℚ → 𝓤₀ ̇
  (p , ψ) < (q , ζ) = p ℚₙ< q

  ℚ<-is-prop : (p q : ℚ) → is-prop (p < q)
  ℚ<-is-prop (p , α) (q , β) = ℚₙ<-is-prop p q

  ℚ<-trans : (p q r : ℚ) → p < q → q < r → p < r
  ℚ<-trans (p , α) (q , β) (c , γ) x y = ℚₙ-trans p q c x y

  <-lemma : (p q : ℚₙ) → p ℚₙ< q → toℚ p < toℚ q 
  <-lemma (x , a) (y , b) l = ordering-right-cancellable (x' ℤ* pos (succ b')) (y' ℤ* (pos (succ a'))) (pos (succ h ℕ* succ h')) IV V
   where
    I : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ≡ (pos (succ h)) ℤ* x') × (succ a ≡ (succ h) ℕ* succ a'))
    I = toℚlemma (x , a)

    II : Σ ((y' , b') , p) ꞉ ℚ , (Σ h' ꞉ ℕ , (y ≡ (pos (succ h')) ℤ* y') × (succ b ≡ (succ h') ℕ* succ b'))
    II = toℚlemma (y , b)

    x' y' : ℤ
    x' = pr₁ (pr₁ (pr₁ I))
    y' = pr₁ (pr₁ (pr₁ II))

    a' b' : ℕ
    a' = pr₂ (pr₁ (pr₁ I))
    b' = pr₂ (pr₁ (pr₁ II))

    h h' : ℕ
    h = pr₁ (pr₂ I)
    h' = pr₁ (pr₂ II)

    α : x ≡ (pos (succ h)) ℤ* x'
    α = pr₁ (pr₂ (pr₂ I))

    β : succ a ≡ (succ h) ℕ* succ a'
    β = pr₂ (pr₂ (pr₂ I))

    α' : y ≡ (pos (succ h')) ℤ* y'
    α' = pr₁ (pr₂ (pr₂ II))

    β' : succ b ≡ (succ h') ℕ* succ b'
    β' = pr₂ (pr₂ (pr₂ II))

    III : greater-than-zero (pos (succ h) ℤ* pos (succ h'))
    III = greater-than-zero-mult-trans (pos (succ h)) (pos (succ h')) (pos-succ-greater-than-zero h) (pos-succ-greater-than-zero h')

    IV : greater-than-zero (pos (succ h ℕ* succ h'))
    IV = transport (λ z → greater-than-zero z) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) III

    V : ((x' ℤ* pos (succ b')) ℤ* pos (succ h ℕ* succ h')) ℤ< ((y' ℤ* pos (succ a')) ℤ* pos (succ h ℕ* succ h'))
    V = transport₂ (λ z z' → z ℤ< z') VI VII l
     where
      VI : x ℤ* pos (succ b) ≡ x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h')
      VI = x ℤ* pos (succ b)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α (ap pos β') ⟩
            pos (succ h) ℤ* x' ℤ* pos (succ h' ℕ* succ b')            ≡⟨ ap (pos (succ h) ℤ* x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹) ⟩
            pos (succ h) ℤ* x' ℤ* (pos (succ h') ℤ* (pos (succ b')))  ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h)) x') (ℤ*-comm (pos (succ h')) (pos (succ b'))) ⟩
            x' ℤ* pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h'))    ≡⟨ ℤ*-assoc x' (pos (succ h)) (pos (succ b') ℤ* pos (succ h')) ⁻¹ ⟩
            x' ℤ* (pos (succ h) ℤ* (pos (succ b') ℤ* pos (succ h')))  ≡⟨ ap (x' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h)) (pos (succ b')) (pos (succ h'))) ⟩
            x' ℤ* (pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h')))  ≡⟨ ℤ*-assoc x' (pos (succ b')) (pos (succ h) ℤ* pos (succ h')) ⟩
            x' ℤ* pos (succ b') ℤ* (pos (succ h) ℤ* pos (succ h'))    ≡⟨ ap ( x' ℤ* pos (succ b') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ h')) ⟩
            x' ℤ* pos (succ b') ℤ* pos (succ h ℕ* succ h') ∎

      VII : y ℤ* pos (succ a) ≡ y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h')
      VII = y ℤ* pos (succ a)                                         ≡⟨ ap₂ (λ z z' → z ℤ* z') α' (ap pos β) ⟩
             pos (succ h') ℤ* y' ℤ* pos (succ h ℕ* succ a')            ≡⟨ ap (pos (succ h') ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹) ⟩
             pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))    ≡⟨ ap₂ (λ z z' → z ℤ* z') (ℤ*-comm (pos (succ h')) y') (ℤ*-comm (pos (succ h)) (pos (succ a'))) ⟩
             y' ℤ* pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h))    ≡⟨ ℤ*-assoc y' (pos (succ h')) (pos (succ a') ℤ* pos (succ h)) ⁻¹ ⟩
             y' ℤ* (pos (succ h') ℤ* (pos (succ a') ℤ* pos (succ h)))  ≡⟨ ap (y' ℤ*_) (ℤ-mult-rearrangement''' (pos (succ h')) (pos (succ a')) (pos (succ h))) ⟩
             y' ℤ* (pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h)))  ≡⟨ ℤ*-assoc y' (pos (succ a')) (pos (succ h') ℤ* pos (succ h)) ⟩
             y' ℤ* pos (succ a') ℤ* (pos (succ h') ℤ* pos (succ h))    ≡⟨ ap (y' ℤ* pos (succ a') ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ h)) ⟩
             y' ℤ* pos (succ a') ℤ* pos (succ h' ℕ* succ h)            ≡⟨ ap (λ z → y' ℤ* pos (succ a') ℤ* pos z) (mult-commutativity (succ h') (succ h)) ⟩
             y' ℤ* pos (succ a') ℤ* pos (succ h ℕ* succ h') ∎

  ℚ-no-max-element : (p : ℚ) → Σ q ꞉ ℚ , (p < q)
  ℚ-no-max-element ((x , a) , α) = q , III
   where
    q : ℚ 
    q = toℚ ((succℤ x) , a)

    x' : ℤ
    x' = pr₁ (pr₁ q)
    a' : ℕ
    a' = pr₂ (pr₁ q)

    I : succℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
    I = ≈-toℚ ((succℤ x) , a)

    II : (x ℤ* pos (succ a')) ℤ< (succℤ x ℤ* pos (succ a'))
    II = positive-multiplication-preserves-order x (succℤ x) (pos (succ a')) (pos-succ-greater-than-zero a') (<-incrℤ x)

    III : x ℤ* pos (succ a') ℤ< (x' ℤ* pos (succ a))
    III = transport (x ℤ* pos (succ a') ℤ<_) I II

  ℚ-no-least-element : (q : ℚ) → Σ p ꞉ ℚ , p < q
  ℚ-no-least-element ((x , a) , α) = p , III
   where
    p : ℚ
    p = toℚ ((predℤ x) , a)

    x' : ℤ
    x' = pr₁ (pr₁ p)
    a' : ℕ
    a' = pr₂ (pr₁ p)

    I : predℤ x ℤ* pos (succ a') ≡ x' ℤ* pos (succ a)
    I = ≈-toℚ ((predℤ x) , a)

    II : (predℤ x ℤ* pos (succ a')) ℤ< (x ℤ* pos (succ a'))
    II = positive-multiplication-preserves-order (predℤ x) x (pos (succ a')) (pos-succ-greater-than-zero a') (<-predℤ x)

    III : x' ℤ* pos (succ a) ℤ< (x ℤ* pos (succ a'))
    III = transport (_ℤ< x ℤ* pos (succ a')) I II

  ℚ-trichotomous-lemma : Fun-Ext → ((p , α) (q , β) : ℚ) → p ℚₙ≈ q → p , α ≡ q , β
  ℚ-trichotomous-lemma fe (p , α) (q , β) e = to-subtype-≡ (λ - → is-in-lowest-terms-is-prop fe -) (equiv-with-lowest-terms-is-equal p q e α β)

  ℚ-trichotomous : Fun-Ext → (p q : ℚ) → (p < q) ∔ (p ≡ q) ∔ (q < p)
  ℚ-trichotomous fe ((x , a) , α) ((y , b) , β) = f (ℤ-trichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a)))
   where
    f : (x ℤ* pos (succ b)) ℤ< (y ℤ* pos (succ a))
       ∔ (x ℤ* pos (succ b) ≡ y ℤ* pos (succ a))
       ∔ (y ℤ* pos (succ a)) ℤ< (x ℤ* pos (succ b))
      →  ((x , a) , α) < ((y , b) , β)
       ∔ ((x , a) , α ≡ (y , b) , β)
       ∔ ((y , b) , β) < ((x , a) , α)
    f (inl z)       = inl z
    f (inr (inl z)) = inr (inl (ℚ-trichotomous-lemma fe ((x , a) , α) ((y , b) , β) z))
    f (inr (inr z)) = inr (inr z)

  located-property : Fun-Ext → (p q x : ℚ) → p < q → (p < x) ∔ (x < q) 
  located-property fe p q x l = f (ℚ-trichotomous fe x q)
   where
    f : (x < q) ∔ (x ≡ q) ∔ (q < x) → (p < x) ∔ (x < q) 
    f (inl z)       = inr z
    f (inr (inl z)) = inl (transport (p <_) (z ⁻¹) l)
    f (inr (inr z)) = inl (ℚ<-trans p q x l z)

  half-ℚₙ : ℚₙ → ℚₙ
  half-ℚₙ (x , a) = x , (succ (2 ℕ* a))

  open RMoreNaturalProperties
  open import NaturalsAddition renaming (_+_ to _ℕ+_) --Type Topology

  rounded-lemma₀ : (a : ℕ) → succ (2 ℕ* pred (succ a)) ≡ pred (2 ℕ* (succ a))
  rounded-lemma₀ zero = refl
  rounded-lemma₀ (succ a) = succ (2 ℕ* pred (succ (succ a))) ≡⟨ ap (λ - → succ (2 ℕ* -)) (pred-succ a) ⟩
                     succ (2 ℕ* succ a)                ≡⟨ pred-succ (2 ℕ* succ a) ⁻¹ ⟩
                     pred (succ (succ (2 ℕ* succ a)))  ≡⟨ refl ⟩
                     pred (2 ℕ* succ a ℕ+ 2)           ≡⟨ refl ⟩
                     pred (2 ℕ* (succ a) ℕ+ 2 ℕ* 1)    ≡⟨ ap pred (distributivity-mult-over-nat 2 (succ a) 1 ⁻¹) ⟩
                     pred (2 ℕ+ (2 ℕ* (succ a)))       ≡⟨ refl ⟩
                     pred (2 ℕ* succ (succ a)) ∎

  rounded-lemma : (p q : ℚ) → p < q → Σ x ꞉ ℚ , (p < x) × (x < q)
  rounded-lemma ((x , a) , α) ((y , b) , β) l = midpoint , firstly , secondly
   where
    midpoint : ℚ
    midpoint = toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

    z : ℤ
    z = pr₁ (pr₁ midpoint)
    c : ℕ
    c = pr₂ (pr₁ midpoint)

    z' : ℤ
    z' = pr₁ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

    z'' : z' ≡ x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ a)
    z'' = refl

    c' : ℕ
    c' = pr₂ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

    c'' : c' ≡ succ (2 ℕ* pred (succ a ℕ* succ b))
    c'' = refl

    I : (z' , c') ℚₙ≈ (z , c)
    I = ≈-toℚ (half-ℚₙ ((x , a) ℚₙ+ (y , b)))

    II : z' ℤ* pos (succ c) ≡ z ℤ* pos (succ c')
    II = I

    III : Σ k ꞉ ℕ , succ k ≡ succ a ℕ* succ b
    III = pos-mult-is-succ a b

    k : ℕ
    k = pr₁ III

    a' b' k' c''' : ℤ
    a' = pos (succ a)
    b' = pos (succ b)
    k' = pos (succ k)
    c''' = pos (succ c')

    IV : (x : ℤ) →  x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b)))) ≡ x ℤ* a' ℤ* b' ℤ+ x ℤ* (a') ℤ* b'
    IV x = x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))    ≡⟨ ap (λ - → x ℤ* pos (succ (succ (2 ℕ* pred -)))) ((pr₂ III) ⁻¹) ⟩
         x ℤ* pos (succ (succ (2 ℕ* pred (succ k))))                ≡⟨ ap (λ - → x ℤ* pos (succ -)) (rounded-lemma₀ k) ⟩
         x ℤ* pos (succ (pred (2 ℕ* succ k)))                       ≡⟨ ap (λ - → x ℤ* pos -) (succ-pred' (2 ℕ* succ k) λ w → ℕ-positive-multiplication-not-zero 1 k w) ⟩
         x ℤ* pos (2 ℕ* succ k)                                     ≡⟨ ap (λ - → x ℤ* pos -) (mult-commutativity 2 (succ k)) ⟩
         x ℤ* pos (succ k ℕ+ succ k)                                ≡⟨ ap (λ - → x ℤ* -) (pos-addition-equiv-to-ℕ (succ k) (succ k)  ⁻¹) ⟩
         x ℤ* (k' ℤ+ k')                                            ≡⟨ distributivity-mult-over-ℤ' (k') (k') x ⟩
         x ℤ* k' ℤ+ x ℤ* k'                                         ≡⟨ ap (λ - → x ℤ* pos - ℤ+ x ℤ* pos -) (pr₂ III) ⟩
         x ℤ* pos (succ a ℕ* succ b) ℤ+ x ℤ* pos (succ a ℕ* succ b) ≡⟨ ap (λ - → (x ℤ* -) ℤ+ (x ℤ* -)) (pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹) ⟩
         x ℤ* (a' ℤ* b') ℤ+ x ℤ* (a' ℤ* b')                          ≡⟨ ap (λ - → - ℤ+ -) (ℤ*-assoc x (a') (b')) ⟩
         x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b' ∎

    V : (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡ x ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* a'
    V = (x ℤ* b' ℤ+ y ℤ* a') ℤ* a' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (a') ⟩
           x ℤ* b' ℤ* a' ℤ+ y ℤ* a' ℤ* a' ≡⟨ ap (λ - → - ℤ+ y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a'))  ⟩
           x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a' ∎

    VI : (x ℤ* a' ℤ* b' ℤ+ x ℤ* a' ℤ* b') ℤ< (x ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* a')
    VI = ℤ<-adding'' (x ℤ* a' ℤ* b') (y ℤ* a' ℤ* a') (x ℤ* a' ℤ* b') ii
     where
      i : (x ℤ* b' ℤ* a') ℤ< (y ℤ* a' ℤ* a')
      i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (a') (pos-succ-greater-than-zero a) l

      ii : (x ℤ* a' ℤ* b') ℤ< (y ℤ* a' ℤ* a')
      ii = transport (_ℤ< y ℤ* a' ℤ* a') (ℤ-mult-rearrangement x (b') (a')) i

    VII : (x ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* succ b))))) ℤ< ((x ℤ* b' ℤ+ y ℤ* a') ℤ* a')
    VII = transport₂ _ℤ<_ (IV x ⁻¹) (V ⁻¹) VI

    VIII : x ℤ* c''' ℤ< z' ℤ* a'
    VIII = VII

    IX : (x ℤ* c''' ℤ* pos (succ c)) ℤ< (z' ℤ* a' ℤ* pos (succ c)) 
    IX = positive-multiplication-preserves-order (x ℤ* c''') (z' ℤ* a') (pos (succ c)) (pos-succ-greater-than-zero c) VIII

    X : (x ℤ* pos (succ c) ℤ* c''') ℤ< (z ℤ* a' ℤ* c''')
    X = transport₂ _ℤ<_ i ii IX
     where
      i : x ℤ* c''' ℤ* pos (succ c) ≡ x ℤ* pos (succ c) ℤ* c'''
      i = ℤ-mult-rearrangement x (c''') (pos (succ c)) 

      ii : z' ℤ* a' ℤ* pos (succ c) ≡ z ℤ* a' ℤ* c'''
      ii = z' ℤ* a' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (a') (pos (succ c)) ⟩
           z' ℤ* pos (succ c) ℤ* a' ≡⟨ ap (_ℤ* a') II ⟩
           z ℤ* c''' ℤ* a' ≡⟨ ℤ-mult-rearrangement z (c''') (a') ⟩
           z ℤ* a' ℤ* c''' ∎

    firstly : (x ℤ* pos (succ c)) ℤ< (z ℤ* a')
    firstly = ordering-right-cancellable (x ℤ* pos (succ c)) (z ℤ* a') (c''') (pos-succ-greater-than-zero c') X

    XI : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡ (x ℤ* (b') ℤ+ y ℤ* a') ℤ* b'
    XI = x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ≡⟨ distributivity-mult-over-ℤ (x ℤ* b') ( y ℤ* a') (b') ⁻¹ ⟩
           (x ℤ* b' ℤ+ y ℤ* a') ℤ* b' ∎

    XII : y ℤ* a' ℤ* b' ℤ+ y ℤ* (a') ℤ* b' ≡ y ℤ* pos (succ (succ (2 ℕ* pred (succ a ℕ* (succ b)))))
    XII = IV y ⁻¹

    XIII : x ℤ* b' ℤ* b' ℤ+ y ℤ* a' ℤ* b' ℤ< y ℤ* a' ℤ* b' ℤ+ y ℤ* a' ℤ* b'
    XIII = ℤ<-adding' (x ℤ* b' ℤ* b') (y ℤ* a' ℤ* b') (y ℤ* a' ℤ* b') i
     where
      i : (x ℤ* b' ℤ* b') ℤ< (y ℤ* a' ℤ* b')
      i = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') (b') (pos-succ-greater-than-zero b) l

    XIV : (z' ℤ* b') ℤ< (y ℤ* c''')
    XIV = transport₂ _ℤ<_ XI XII XIII

    XV : (z' ℤ* b' ℤ* pos (succ c)) ℤ< (y ℤ* c''' ℤ* pos (succ c))
    XV = positive-multiplication-preserves-order (z' ℤ* b') (y ℤ* c''') (pos (succ c)) (pos-succ-greater-than-zero c') XIV

    XVI : (z ℤ* b') ℤ* c''' ℤ< (y ℤ* pos (succ c)) ℤ* c'''
    XVI = transport₂ _ℤ<_ i ii XV
     where
      i : z' ℤ* b' ℤ* pos (succ c) ≡ z ℤ* b' ℤ* c'''
      i = z' ℤ* b' ℤ* pos (succ c) ≡⟨ ℤ-mult-rearrangement z' (b') (pos (succ c)) ⟩
          z' ℤ* pos (succ c) ℤ* b' ≡⟨ ap (_ℤ* b') II ⟩
          z ℤ* c''' ℤ* b' ≡⟨ ℤ-mult-rearrangement z (c''') (b') ⟩
          z ℤ* b' ℤ* c''' ∎

      ii : y ℤ* c''' ℤ* pos (succ c) ≡ y ℤ* pos (succ c) ℤ* c'''
      ii = ℤ-mult-rearrangement y (c''') (pos (succ c))

    secondly : (z ℤ* b') ℤ< (y ℤ* pos (succ c))
    secondly = ordering-right-cancellable (z ℤ* b') (y ℤ* pos (succ c)) (c''') (pos-succ-greater-than-zero c') XVI

  -_ : ℚ → ℚ
  - ((x , a) , p) = toℚ ((ℤ- x) , a)

  {-

  ℚ-zero-not-one : ¬ (zero-ℚ ≡ 1ℚ)
  ℚ-zero-not-one e = {!!}

  ℚ-distributive : (p q r : ℚ) → p * (q + r) ≡ (p * q) + (p * r) 
  ℚ-distributive = {!!}

  ℚ-zero-left-neutral : (q : ℚ) → zero-ℚ + q ≡ q
  ℚ-zero-left-neutral = {!!}

  ℚ-zero-right-neutral : (q : ℚ) → q + zero-ℚ ≡ q
  ℚ-zero-right-neutral q = ℚ+-comm q zero-ℚ ∙ ℚ-zero-left-neutral q

  ℚ-mult-left-id : (q : ℚ) → 1ℚ * q ≡ q
  ℚ-mult-left-id q = {!!}

  ℚ-mult-right-id : (q : ℚ) → q * 1ℚ ≡ q
  ℚ-mult-right-id q = {!!}

  ℚ+-inverse : (q : ℚ) → Σ q' ꞉ ℚ , q + q' ≡ zero-ℚ
  ℚ+-inverse q = (- q) , {!!}

  ℚ+-inverse' : (q : ℚ) → Σ q' ꞉ ℚ , q' + q ≡ zero-ℚ
  ℚ+-inverse' q = f (ℚ+-inverse q)
    where
     f : Σ q' ꞉ ℚ , q + q' ≡ zero-ℚ → Σ q' ꞉ ℚ , q' + q ≡ zero-ℚ
     f (q' , e) = q' , (ℚ+-comm q' q ∙ e)
  
  ℚ-inverse-sum-to-zero : (q : ℚ) → q + (- q) ≡ zero-ℚ
  ℚ-inverse-sum-to-zero q = {!!}

  --Maybe consider implementation of division and it's properties
  *-flip : (q : ℚ) → ¬ (q ≡ zero-ℚ) → ℚ 
  *-flip ((pos zero     , a) , p) nz = 𝟘-elim (nz {!!})
  *-flip ((pos (succ x) , a) , p) nz = toℚ ((pos (succ a)) , x)
  *-flip ((negsucc x    , a) , p) nz = toℚ ((negsucc  a) , x)

  ℚ*-inverse : (q : ℚ) → ¬ (q ≡ zero-ℚ) → Σ q' ꞉ ℚ , q * q' ≡ 1ℚ
  ℚ*-inverse q nz = (*-flip q nz) , {!!}

  ℚ*-inverse-product-is-one : (q : ℚ) → (nz : ¬ (q ≡ zero-ℚ)) → q * *-flip q nz ≡ 1ℚ
  ℚ*-inverse-product-is-one = {!!}

  open import Groups --TypeTopology

  ℚ+-is-group : Fun-Ext → Group-structure ℚ
  ℚ+-is-group fe = _+_ , (ℚ-is-set fe , (ℚ+-assoc fe) , (zero-ℚ , ℚ-zero-left-neutral , ℚ-zero-right-neutral , λ x → - x , ((ℚ+-comm (- x) x ∙ ℚ-inverse-sum-to-zero x) , ℚ-inverse-sum-to-zero x)))

  ℚ*-is-group : Fun-Ext → ((q : ℚ) → ¬ (q ≡ zero-ℚ)) → Group-structure ℚ
  ℚ*-is-group fe nz = _*_ , (ℚ-is-set fe) , (ℚ*-assoc fe) , (1ℚ , ℚ-mult-left-id , ℚ-mult-right-id , λ x → (*-flip x (nz x)) , ((ℚ*-comm (*-flip x (nz x)) x ∙  ℚ*-inverse-product-is-one x (nz x)) , ℚ*-inverse-product-is-one x (nz x)))

  open RFieldAxioms

  ℚ-is-field : Fun-Ext → Field-structure ℚ
  ℚ-is-field fe = (_+_ , _*_) , ℚ-is-set fe
                              , ℚ+-assoc fe
                              , ℚ*-assoc fe
                              , ℚ+-comm
                              , ℚ*-comm
                              , ℚ-distributive
                              , (zero-ℚ , 1ℚ) , ℚ-zero-not-one
                                              , ℚ-zero-left-neutral
                                              , ℚ+-inverse
                                              , ℚ-mult-left-id
                                              , ℚ*-inverse

  ℚₙ-less-than-pos-addition' : (p q r : ℚₙ) → p ℚₙ< q → (p ℚₙ+ r) ℚₙ< (q ℚₙ+ r)
  ℚₙ-less-than-pos-addition' (x , a) (y , b) (z , c) = {!!}

  ℚ-less-than-pos-addition' : (p q r : ℚ) → p < q → (p + r) < (q + r)
  ℚ-less-than-pos-addition' (x , a) (y , b) (z , c) = {!!}

  ℚ-pos-multiplication-preserves-order : (p q : ℚ) → zero-ℚ < p → zero-ℚ < q → zero-ℚ < (p * q)
  ℚ-pos-multiplication-preserves-order = {!!}

  ℚ-is-ordered-field : (fe : Fun-Ext) → Ordered-field-structure ℚ (ℚ-is-field fe)
  ℚ-is-ordered-field fe = _<_ , ℚ-less-than-pos-addition' , ℚ-pos-multiplication-preserves-order
 
  -}
 
\end{code}

\begin{code}

 open import UF-FunExt -- TypeTopology
 open import UF-PropTrunc -- TypeTopology

 module RDedekindReals
          (pt : propositional-truncations-exist)
          (fe : Fun-Ext)
        where
        
  open import UF-Subsingletons-FunExt -- TypeTopology
  open RRationals renaming (_<_ to _ℚ<_ ; _+_ to _ℚ+_ ; _*_ to _ℚ*_ ; -_ to ℚ-_)
  open PropositionalTruncation pt

  open import UF-Subsingletons -- TypeTopology

  ℚ-subset : 𝓤₁ ̇
  ℚ-subset = Σ C ꞉ (ℚ → 𝓤₀ ̇) , ((q : ℚ) → is-prop (C q))
  {-
  ℚ-subset-is-set : is-set ℚ-subset
  ℚ-subset-is-set = {!!}
  -}
  inhabited : (L R : ℚ-subset) → 𝓤₀ ̇ --every real number is between two rationals
  inhabited (L , _) (R , _) = (∃ p ꞉ ℚ , L p) × (∃ q ꞉ ℚ , R q)

  inhabited-is-prop : (L R : ℚ-subset) → is-prop (inhabited L R)
  inhabited-is-prop L R = ×-is-prop ∃-is-prop ∃-is-prop

  rounded : (L R : ℚ-subset) → 𝓤₀ ̇ --if rational is smaller than x, then you find another rational smaller than x (and symmetric)
  rounded (L , _) (R , _) = (p q : ℚ) → (L p ⇔ (∃ p' ꞉ ℚ , (p ℚ< p') × L p')) × (R q ⇔ (∃ q' ꞉ ℚ , (q' ℚ< q) × R q'))

  rounded-is-prop : (L R : ℚ-subset) → is-prop (rounded L R)
  rounded-is-prop (L , L-is-prop) (R , R-is-prop) = Π₂-is-prop fe I
   where
    I : (x y : ℚ) → is-prop (((L x) ⇔ (∃ p' ꞉ ℚ , (x ℚ< p') × L p')) × ((R y) ⇔ (∃ q' ꞉ ℚ , (q' ℚ< y) × R q')))
    I x y = ×-is-prop (×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → L-is-prop x))) (×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → R-is-prop y)))

  disjoint : (L R : ℚ-subset) → 𝓤₀ ̇
  disjoint (L , _) (R , _) = (p q : ℚ) → L p × R q → p ℚ< q

  disjoint-is-prop : (L R : ℚ-subset) → is-prop (disjoint L R)
  disjoint-is-prop (L , _) (R , _) = Π₃-is-prop fe (λ x y _ → ℚ<-is-prop x y)

  located : (L R : ℚ-subset) → 𝓤₀ ̇
  located (L , _) (R , _) = (p q : ℚ) → p ℚ< q → L p ∨ R q

  located-is-prop : (L R : ℚ-subset) → is-prop (located L R)
  located-is-prop (L , _) (R , _) = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

  isCut : (L R : ℚ-subset) → 𝓤₀ ̇
  isCut L R = inhabited L R × rounded L R × disjoint L R × located L R

  isCut-is-prop : (L R : ℚ-subset) → is-prop (isCut L R)
  isCut-is-prop L R = ×-is-prop (inhabited-is-prop L R) (×-is-prop (rounded-is-prop L R) (×-is-prop (disjoint-is-prop L R) (located-is-prop L R)))

  ℝ : 𝓤₁ ̇
  ℝ = Σ (L , R) ꞉ ℚ-subset × ℚ-subset , isCut L R
  
  {-
  open import UF-Retracts -- TypeTopology
  
  ℝ-is-set : is-set ℝ
  ℝ-is-set = Σ-is-set (Σ-is-set ℚ-subset-is-set (λ _ → ℚ-subset-is-set)) (λ x → props-are-sets (isCut-is-prop (pr₁ x) (pr₂ x)))
  -}
  
  embeddingℚtoℝ : ℚ → ℝ
  embeddingℚtoℝ x = ((L , λ p → ℚ<-is-prop p x) , (R , λ q → ℚ<-is-prop x q )) , (inhabited' , rounded' , disjoint' , located')
    where
      L R : ℚ → 𝓤₀ ̇
      L p = p ℚ< x
      R q = x ℚ< q

      inhabited' : (∃ p ꞉ ℚ , L p) × (∃ q ꞉ ℚ , R q) --need toℚ proof
      inhabited' = ∣ ℚ-no-least-element x ∣ , ∣ ℚ-no-max-element x ∣

      rounded' : (p q : ℚ) → (L p ⇔ (∃ p' ꞉ ℚ , (p ℚ< p') × L p')) × (R q ⇔ (∃ q' ꞉ ℚ , (q' ℚ< q) × R q'))
      rounded' p q = (I , II) , (III , IV)
        where        
          I : L p → ∥ Σ p' ꞉ ℚ , (p ℚ< p') × L p' ∥ --need to average p and x, might end up needing toℚ
          I l = ∣ δ (rounded-lemma p x l ) ∣
           where
            δ : (Σ p' ꞉ ℚ , (p ℚ< p') × (p' ℚ< x)) → Σ p' ꞉ ℚ , (p ℚ< p') × L p'
            δ (p' , l' , m) =  p' , l' , m

          II : ∃ p' ꞉ ℚ , (p ℚ< p') × L p' → L p
          II l = ∥∥-rec (ℚ<-is-prop p x) i l
            where
              i : Σ p' ꞉ ℚ , (p ℚ< p') × L p' → p ℚ< x
              i (α , β , γ) = ℚ<-trans p α x β γ

          III : R q → (∃ q' ꞉ ℚ , (q' ℚ< q) × R q')
          III l = ∣ δ (rounded-lemma x q l) ∣
           where
            δ : (Σ q' ꞉ ℚ , (x ℚ< q') × (q' ℚ< q)) → Σ q' ꞉ ℚ , (q' ℚ< q) × R q'
            δ (q' , α , β) = q' , β , α

          IV : (∃ q' ꞉ ℚ , (q' ℚ< q) × R q') → R q
          IV l = ∥∥-rec (ℚ<-is-prop x q) i l
            where
              i : Σ q' ꞉ ℚ , (q' ℚ< q) × R q' → x ℚ< q
              i (α , β , γ) = ℚ<-trans x α q γ β


      disjoint' : (p q : ℚ) → (p ℚ< x) × (x ℚ< q) → p ℚ< q
      disjoint' p q (l , r) = ℚ<-trans p x q l r

      located' : (p q : ℚ) → p ℚ< q → L p ∨ R q --need ℚ-trichotomous
      located' p q l = ∣ located-property fe p q x l ∣

  zero-ℝ : ℝ
  zero-ℝ = embeddingℚtoℝ zero-ℚ

  one-ℝ : ℝ
  one-ℝ = embeddingℚtoℝ 1ℚ

  _<_ : ℝ → ℝ → 𝓤₀ ̇
  (((Lx , _) , Rx , _) , p) < (((Ly , _) , Ry , _) , q) = ∃ q ꞉ ℚ , Rx q × Ly q

  <-is-prop : (x y : ℝ) → is-prop (x < y)
  <-is-prop x y = ∃-is-prop

  _≤_ : ℝ → ℝ → 𝓤₀ ̇
  (((Lx , _) , Rx , _) , p) ≤ (((Ly , _) , Ry , _) , q) = (q : ℚ) → Lx q → Ly q

  ≤-is-prop : (x y : ℝ) → is-prop (x ≤ y)
  ≤-is-prop x (((Ly , Ly-is-prop) , Ry , _) , q) = Π₂-is-prop fe (λ q _ → Ly-is-prop q)

  {-

  _+_ : ℝ → ℝ → ℝ
  (((Lx , Lx-is-prop) , Rx , Rx-is-prop) , isCutx) + (((Ly , Ly-is-prop) , Ry , Ry-is-prop) , isCuty) = (new-left , new-right) , new-cut-is-cut
   where
    new-left : ℚ-subset
    new-left = (λ p → ∃ (r , s) ꞉ ℚ × ℚ , Lx r × Ly s × (p ≡ r ℚ+ s)) , λ _ → ∃-is-prop -- ∃ (r , s) ꞉ ℚ × ℚ , Lx r × Ly s × (p ≡ r ℚ+ s)

    new-right : ℚ-subset
    new-right = (λ q →  ∃ (r , s) ꞉ ℚ × ℚ , Ry r × Ry s × (q ≡ r ℚ+ s)) , λ _ → ∃-is-prop

    new-cut-is-cut : isCut new-left new-right
    new-cut-is-cut = (λ l r → isInhabited , isRounded , isDisjoint , isLocated) new-left new-right --isInhabited new-left new-right , isRounded new-left new-right , {!!} , {!!}
     where
      isInhabited : inhabited new-left new-right
      isInhabited = {!!}

      isRounded : (p q : ℚ) → rounded new-left new-right
      isRounded = {!!}

      isDisjoint : disjoint new-left new-right
      isDisjoint = {!!}

      isLocated : located new-left new-right
      isLocated = {!!}

  -_ : ℝ → ℝ
  - (((L , L-is-prop) , R , R-is-prop) , isCut') = (new-left , new-right) , new-cut-is-cut
   where
    new-left : ℚ-subset
    new-left = (λ p → ∃ r ꞉ ℚ , R r × (p ≡ (ℚ- r))) , λ _ → ∃-is-prop 

    new-right : ℚ-subset
    new-right = (λ q →  ∃ r ꞉ ℚ , L r × (q ≡ (ℚ- r))) , λ _ → ∃-is-prop

    new-cut-is-cut : isCut new-left new-right
    new-cut-is-cut = (λ l r → isInhabited , isRounded , isDisjoint , isLocated) new-left new-right 
     where
      isInhabited : inhabited new-left new-right
      isInhabited = {!!}

      isRounded : (p q : ℚ) → rounded new-left new-right
      isRounded = {!!}

      isDisjoint : disjoint new-left new-right
      isDisjoint = {!!}

      isLocated : located new-left new-right
      isLocated = {!!}

  ℚmin : (a b c d : ℚ) → ℚ --minimum of two, apply recursively
  ℚmin = {!!}

  ℚmax : (a b c d : ℚ) → ℚ
  ℚmax = {!!}

  _*_ : ℝ → ℝ → ℝ
  (((Lx , Lx-is-prop) , Rx , Rx-is-prop) , isCutx) * (((Ly , Ly-is-prop) , Ry , Ry-is-prop) , isCuty) = (new-left , new-right) , new-cut-is-cut
   where
    new-left : ℚ-subset
    new-left = (λ p → ∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , Lx a × Rx b × Ly c × Ry d × (p ℚ< ℚmin (a ℚ* c) (a ℚ* d) (b ℚ* d) (b ℚ* d))) , λ _ → ∃-is-prop -- ∃ (r , s) ꞉ ℚ × ℚ , Lx r × Ly s × (p ≡ r ℚ+ s)

    new-right : ℚ-subset
    new-right = (λ q →  ∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , Lx a × Rx b × Ly c × Ry d × (ℚmax (a ℚ* c) (a ℚ* d) (b ℚ* d) (b ℚ* d)) ℚ< q) , λ _ → ∃-is-prop

    new-cut-is-cut : isCut new-left new-right
    new-cut-is-cut = (λ l r → isInhabited , isRounded , isDisjoint , isLocated) new-left new-right --isInhabited new-left new-right , isRounded new-left new-right , {!!} , {!!}
     where
      isInhabited : inhabited new-left new-right
      isInhabited = {!!} , {!!}

      isRounded : (p q : ℚ) → rounded new-left new-right
      isRounded = {!!}

      isDisjoint : disjoint new-left new-right
      isDisjoint = {!!}

      isLocated : located new-left new-right
      isLocated = {!!}

  --need to define lemma11.2.2 , 11.2.3, apartness, invertibility, 

  ℝ-archimedean-principle : (x y : ℝ) → (x < y) → ∃ q ꞉ ℚ , ((λ q' → (x < q') × (q' < y)) (embeddingℚtoℝ q))
  ℝ-archimedean-principle (((Lx , Lx-is-prop) , Rx , Rx-is-prop) , isCutx) (((Ly , Ly-is-prop) , Ry , Ry-is-prop) , isCuty) l = ∥∥-induction (λ _ → ∥∥-is-prop) I l
   where
    I : Σ q ꞉ ℚ , Rx q × Ly q → ∥ Σ q ꞉ ℚ , (((((Lx , Lx-is-prop) , Rx , Rx-is-prop) , isCutx)) < embeddingℚtoℝ q) × (embeddingℚtoℝ q < ((((Ly , Ly-is-prop) , Ry , Ry-is-prop) , isCuty))) ∥
    I (q , p) = ∣ q , {!!} , {!!} ∣

  ℝ+-assoc : (x y z : ℝ) → (x + y) + z ≡ x + (y + z)
  ℝ+-assoc = {!!}

  ℝ*-assoc : (x y z : ℝ) → (x * y) * z ≡ x * (y * z)
  ℝ*-assoc = {!!}

  ℝ+-comm : (x y : ℝ) → x + y ≡ y + x
  ℝ+-comm = {!!}

  ℝ*-comm : (x y : ℝ) → x * y ≡ y * x
  ℝ*-comm = {!!}

  ℝ-distributivity : (x y z : ℝ) → x * (y + z) ≡ (x * y) + (x * z)
  ℝ-distributivity = {!!}

  ℝ-zero-not-one : ¬ (zero-ℝ ≡ one-ℝ)
  ℝ-zero-not-one = {!!}

  ℝ-zero-left-neutral : (x : ℝ) → zero-ℝ + x ≡ x
  ℝ-zero-left-neutral x = {!!}

  ℝ-zero-right-neutral : (x : ℝ) → x + zero-ℝ ≡ x
  ℝ-zero-right-neutral x = ℝ+-comm x zero-ℝ ∙ ℝ-zero-left-neutral x

  ℝ-additive-inverse : (x : ℝ) → Σ x' ꞉ ℝ , (x + x') ≡ zero-ℝ
  ℝ-additive-inverse = {!!}

  ℝ-mult-left-id : (x : ℝ) → one-ℝ * x ≡ x
  ℝ-mult-left-id x = {!!}

  ℝ-mult-right-id : (x : ℝ) → x * one-ℝ ≡ x
  ℝ-mult-right-id x = ℝ*-comm x one-ℝ ∙ ℝ-mult-left-id x

  ℝ-multiplicative-inverse : (x : ℝ) → ¬ (x ≡ zero-ℝ) → Σ x' ꞉ ℝ , x * x' ≡ one-ℝ
  ℝ-multiplicative-inverse = {!!}

  open RFieldAxioms

  ℝ-is-field : Field-structure ℝ
  ℝ-is-field = (_+_ , _*_) , (ℝ-is-set , ℝ+-assoc , ℝ*-assoc , ℝ+-comm , ℝ*-comm , ℝ-distributivity , (zero-ℝ , one-ℝ) , ℝ-zero-not-one , ℝ-zero-left-neutral , ℝ-additive-inverse , ℝ-mult-left-id , ℝ-multiplicative-inverse)

  --need to resize order, or redefine field axioms

  ℝ-addition-preserves-order : (x y z : ℝ) → x < y → (x + z) < (y + z)
  ℝ-addition-preserves-order x y z = {!!}

  ℝ-positive-multiplication-preserves-order : (x y : ℝ) → (zero-ℝ < x) → (zero-ℝ < y) → zero-ℝ < (x * y)
  ℝ-positive-multiplication-preserves-order = {!!}

  ℝ-is-ordered-field : Ordered-field-structure ℝ ℝ-is-field
  ℝ-is-ordered-field = _<_ , ℝ-addition-preserves-order , ℝ-positive-multiplication-preserves-order
  -}
  
  _#_ : (x y : ℝ) → 𝓤₀ ̇
  x # y = (x < y) ∨ (y < x)

\end{code}
