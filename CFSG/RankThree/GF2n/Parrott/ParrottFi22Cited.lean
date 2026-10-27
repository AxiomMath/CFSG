module

public import CFSG.RankThree.GF2n.Parrott.ParrottFi22Inputs
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma34Instance

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

section Certified


theorem parrottFi22Statement_of_theorem1_exports_cited
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (hL32 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∀ j ∈ J w, orderOf j = 2 → j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hT3 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X)) ∧
        K₁ ⊓ H w ≤ ⁅H w, H w⁆)
    (hL345 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ E K' : Subgroup K,
        E ≤ H w ∧ E ≤ ⁅H w, H w⁆ ⊔ J w ∧ w ∈ E ∧
        Nat.card E = 2 ^ 9 ∧ Nat.card ↥(E ⊓ J w) = 2 ^ 5 ∧
        E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K) ∧
        E.relIndex (normalizer (E : Set K) ⊓ H w) = 1920 ∧
        (∀ x ∈ E, x ∈ Subgroup.closure
          {y : K | ∃ n ∈ normalizer (E : Set K), y = n * w * n⁻¹}) ∧
        E ≤ K' ∧ K'.relIndex (normalizer (E : Set K)) = 2 ∧
        normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤ K' ∧ ¬ (normalizer (E : Set K) ⊓ H w ≤ K') ∧
        ((E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
           ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) ∧
        ∃ t j₀ : K, t ∈ E ∧ t ∉ J w ∧ orderOf t = 2 ∧ IsConj w t ∧
          j₀ ∈ J w ∧ j₀ ∉ Subgroup.zpowers w ∧ IsConj (t * w) j₀)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22) :
    Tim79a.ParrottFi22Statement :=
  parrottFi22Statement_of_theorem1_exports_lemma34 hThm1 hL32 hT3 hL345
    (fun _ _ _ _ h hZ _ D hIII =>
      hB6_of_lemma34 D h hZ hIII) h5

end Certified

end CFSG.RankThree.GF2n.Parrott
