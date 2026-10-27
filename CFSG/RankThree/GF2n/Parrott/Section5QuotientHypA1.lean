module

public import CFSG.RankThree.GF2n.Parrott.Section5QuotientCJ
public import CFSG.RankThree.GF2n.Parrott.Section5QuotientPSp
public import CFSG.RankThree.GF2n.Parrott.Section4G0TheoremA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G] [Finite G] {z z₁ : G}

theorem parrottHypA1_quotient_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Tim79a.ParrottHypA1 (quotW hzC) :=
  ⟨isExtraspecial2_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC,
    card_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC, commutator_J_quotW_of_ne h hZ hz₁ hz₁z hz₁2 hzC,
    centralizer_J_quotW_le_of_ne h hZ hz₁ hz₁z hz₁2 hzC,
    nonempty_quotientDataPSp_quotW h hZ hz₁ hz₁z hz₁2 hzC⟩

theorem hT2_of_theoremA_one
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
        CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) :
    ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G),
          g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) →
        ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
          (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
              (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X) := by
  intro z₁ hz₁ hz₁z hz₁2 hfuse
  have hzC : z ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h))
  refine ⟨inferInstance, QuotC z₁, inferInstance, ?_, ⟨MulEquiv.refl _⟩⟩
  rcases hA1 (QuotC z₁) (quotW hzC) (parrottHypA1_quotient_of_ne h hZ hz₁ hz₁z hz₁2 hzC) with
    hsup | hLie
  · obtain ⟨g, hcomm, hne⟩ := exists_conj_quotW_ne_of_ne h hZ hz₁ hz₁z hz₁2 hzC hfuse
    exact absurd (eq_of_commute_of_sup_pPrimeCore_eq_top (orderOf_quotW h hz₁z hz₁2 hzC) hsup g
      hcomm) hne
  · exact hLie

end CFSG.RankThree.GF2n.Parrott
