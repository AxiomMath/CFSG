module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4ExportsHB6
public import CFSG.RankThree.GF2n.Parrott.ParrottFi22Assembly
public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1Assembly

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

section Certified


theorem parrottFi22Statement_of_theorem1_exports_lemma34
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
    (hB6 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z),
      centerIn (J z) = centerIn (H z) →
      ∀ (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ¬ ParrottEqualityBranch (z := z) (D := D) h →
      ∀ E : Subgroup G, IsParrottE z E →
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
          (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
          (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
          ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
            ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
            (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
              ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22) :
    Tim79a.ParrottFi22Statement := by
  refine Tim79a.parrottFi22Statement_of_theorem4_theorem5 ?_ h5
  intro G _ _ z h hZ hne
  obtain ⟨hN, ⟨D⟩⟩ := parrottQuotientDataExists h
  by_cases hEq : ParrottEqualityBranch (z := z) (D := D) h
  · exact absurd (hThm1 G z h hN D hEq) hne
  · exact parrott_theorem4_of_exports_hB6 D h hZ hne hEq hL32 hT3 hL345 (hB6 G z h hZ hN D hEq)

end Certified

end CFSG.RankThree.GF2n.Parrott
