module

public import CFSG.Quasithin.H13.NQCoreRadicalAction
public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem configuration_four_group_obstruction {G : Type} [Group G]
    [Finite G] {T L M : Subgroup G} (h : QTNQ T L M) (B : Subgroup G) (hBM : B ≤ M)
    (hB2 : CFSG.IsElementaryAbelian 2 B) (hB4 : Nat.card B = 4) :
    ∃ b ∈ B, b ≠ 1 ∧ ∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype := by
  classical
  have hSQT := NQBlock.isStronglyQuasithin_L_of_qtnq h
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hBN : B ≤ normalizer (L : Set G) := h.eq_normalizer ▸ hBM
  let φ : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hninj := (nq_SQT_component_radical_action_bound hSQT hLC h.not_quasisimple).2 ↥B hB2 hB4 φ
  by_contra hcon
  apply hninj
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  apply hcon
  refine ⟨x, x.2, fun h1 => hx1 (Subtype.ext h1), fun l hl => ?_⟩
  have h1 := (autQuotient_eq_one_iff (CFSG.solvableRadical ↥L) (φ x)).mp hx ⟨l⁻¹, L.inv_mem hl⟩
  refine ⟨_, h1, ?_⟩
  change l⁻¹⁻¹ * ((x : G) * l⁻¹ * (x : G)⁻¹) = ⁅l, (x : G)⁆
  rw [inv_inv, commutatorElement_def]
  group

end CFSG.Quasithin.H13.NQCore
