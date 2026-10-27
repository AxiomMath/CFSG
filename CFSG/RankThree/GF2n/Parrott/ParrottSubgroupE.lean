module

public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupEGenerated
public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupEConjugates
public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupEInvolutions
public import CFSG.RankThree.GF2n.Parrott.SpinSubgroupEOrbits
public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Local

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_parrottE_hypA (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ∃ E : Subgroup G,
      E ≤ H z ∧ E ≤ ⁅H z, H z⁆ ⊔ J z ∧ z ∈ E ∧
      Nat.card E = 2 ^ 9 ∧ Nat.card ↥(E ⊓ J z) = 2 ^ 5 ∧
      E = H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) ∧
      E.relIndex (Subgroup.normalizer (E : Set G) ⊓ H z) = 1920 ∧
      IsElemAbelian 2 (E ⊓ J z) ∧ J z ≤ Subgroup.normalizer (E : Set G) ∧
      (∀ e ∈ E, e ∉ J z →
        Subgroup.closure ({z} ∪ {y : G | ∃ n ∈ Subgroup.normalizer (E : Set G) ⊓ H z,
          y = n * e * n⁻¹}) = E) ∧
      (∀ e ∈ E, e ∉ J z → ∃ j ∈ J z, j * e * j⁻¹ ≠ e ∧ j * e * j⁻¹ ≠ e * z) ∧
      (∀ E' : Subgroup G, E' ≤ H z → IsElemAbelian 2 E' → Nat.card E' = 2 ^ 9 →
        ∃ x ∈ H z, E' = CFSG.conjugate E x) ∧
      (IsElemAbelian 2 E → ∀ y ∈ H z, y * y = 1 → y ∉ J z → y ∈ ⁅H z, H z⁆ →
        ∃ x ∈ H z, x * y * x⁻¹ ∈ E) ∧
      (∀ e ∈ E, e ∉ J z → 20 ≤ Set.ncard {y : G |
        ∃ m ∈ Subgroup.normalizer (E : Set G) ⊓ H z, y = m * e * m⁻¹}) := by
  obtain ⟨κ, hκ⟩ := exists_isSpinCoord_A h D hIII
  refine ⟨spinFixE hκ, spinFixE_le_H hκ, (spinFixE_le_commutator D h hIII hκ).trans le_sup_left,
    z_mem_spinFixE h hκ, card_spinFixE D h hκ, ?_, spinFixE_eq_inf_centralizer h hκ,
    relIndex_spinFixE D h hκ, isElemAbelian_spinFixE_inf_J h hκ, J_le_normalizer_spinFixE h hκ,
    fun e he heJ => spinFixE_generated D h hκ he heJ,
    fun e he heJ => exists_j_conj_ne D h hκ he heJ,
    fun E' hE'H hE'ab hE'card =>
      exists_conjugate_spinFixE_of_isElemAbelian D h hκ hE'H hE'ab hE'card,
    fun hE2 y hy hyy hyJ hyc =>
      exists_conj_mem_spinFixE_of_involution D h hκ hE2 hy hyy hyJ hyc,
    fun e he heJ => twenty_le_ncard_orbit_of_mem_spinFixE D h hκ he heJ⟩
  rw [spinFixE_inf_J hκ (z_ne_one_A h)]
  exact card_spinFixF h hκ

end CFSG.RankThree.GF2n.Parrott
