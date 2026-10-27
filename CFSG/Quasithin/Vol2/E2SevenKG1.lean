module

public import CFSG.Quasithin.Vol2.E2SevenKG

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KGBenderInnerL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → 2 ≤ n → IsPSL 2 2 n ↥K →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ∧
      ∀ x ∈ T ⊓ K, x ^ 2 = 1 → x ∈ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G)

@[expose] def KGBenderInnerSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → 2 ≤ n → IsSz n ↥K →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ∧
      ∀ x ∈ T ⊓ K, x ^ 2 = 1 → x ∈ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G)

@[expose] def KGBenderInnerU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → 2 ≤ n → IsPSU 3 2 n ↥K →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ∧
      ∀ x ∈ T ⊓ K, x ^ 2 = 1 → x ∈ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G)

theorem kgBenderInner_of_parts (hL2 : KGBenderInnerL2) (hSz : KGBenderInnerSz)
    (hU3 : KGBenderInnerU3) : KGBenderInner := by
  intro G _ _ X T M K n hP hJ hKX hXN hC hKT hBen hMK
  obtain ⟨hn, hK | hK | hK⟩ := hBen
  · exact hL2 G X T M K n hP hJ hKX hXN hC hKT hn hK hMK
  · exact hSz G X T M K n hP hJ hKX hXN hC hKT hn hK hMK
  · exact hU3 G X T M K n hP hJ hKX hXN hC hKT hn hK hMK

@[expose] def KGBenderInnerTwoL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (t : G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → t ∈ T → K ≤ X → cjSub t K ≠ K →
    X ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G) →
    X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥ →
    K ⊓ cjSub t K = ⊥ → ⁅K, cjSub t K⁆ = ⊥ → K ⊔ T = X → 2 ≤ n → IsPSL 2 2 n ↥K →
    M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ⊔ cjSub t K ∧
      ∀ x ∈ T ⊓ (K ⊔ cjSub t K), x ^ 2 = 1 →
        x ∈ Subgroup.centralizer ((T ⊓ (K ⊔ cjSub t K) : Subgroup G) : Set G)

@[expose] def KGBenderInnerTwoSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K : Subgroup G) (t : G) (n : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → t ∈ T → K ≤ X → cjSub t K ≠ K →
    X ≤ Subgroup.normalizer ((K ⊔ cjSub t K : Subgroup G) : Set G) →
    X ⊓ Subgroup.centralizer ((K ⊔ cjSub t K : Subgroup G) : Set G) = ⊥ →
    K ⊓ cjSub t K = ⊥ → ⁅K, cjSub t K⁆ = ⊥ → K ⊔ T = X → 2 ≤ n → IsSz n ↥K →
    M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T →
    M ⊓ K = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) →
    pCoreOf 2 M ≤ K ⊔ cjSub t K ∧
      ∀ x ∈ T ⊓ (K ⊔ cjSub t K), x ^ 2 = 1 →
        x ∈ Subgroup.centralizer ((T ⊓ (K ⊔ cjSub t K) : Subgroup G) : Set G)

theorem kgBenderInnerTwo_of_parts (hL2 : KGBenderInnerTwoL2) (hSz : KGBenderInnerTwoSz) :
    KGBenderInnerTwo := by
  intro G _ _ X T M K t n hP hJ ht hKX htK hXN hC hKK hcomm hKT hn hK hM hMK
  rcases hK with hK | hK
  · exact hL2 G X T M K t n hP hJ ht hKX htK hXN hC hKK hcomm hKT hn hK hM hMK
  · exact hSz G X T M K t n hP hJ ht hKX htK hXN hC hKK hcomm hKT hn hK hM hMK

end CFSG.Quasithin.E2
