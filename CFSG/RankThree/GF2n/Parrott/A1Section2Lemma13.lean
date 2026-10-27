module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Core
import CFSG.RankThree.GF2n.Parrott.A1Section2CJ
import all CFSG.RankThree.GF2n.Parrott.A1LocalData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open A1Section2Local
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lemma13_A1_of
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hstar : ∀ g : G,
      CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) g ≤ H z →
      ∃ k ∈ H z, CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) g =
        CFSG.conjugate (Subgroup.zpowers ((sHP (quotientDataA1 h) : ↥(H z)) : G)) k) :
    ∀ x : G, (∃ j ∈ J z, x = (tHP (quotientDataA1 h) : G) * j) → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x := by
  set D := quotientDataA1 h with hD
  have hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G) :=
    { hA1 := h
      s1_mem := (s1HP D).2
      s2_mem := (s2HP D).2
      orderOf_s1 := by rw [Subgroup.orderOf_coe, orderOf_s1HP]
      orderOf_s2 := by rw [Subgroup.orderOf_coe, orderOf_s2HP]
      comm12 := congrArg Subtype.val (commute_s1HP_s2HP D).eq
      heq := heq
      card_J0 := card_CJ_s1HP_A1 h
      sup1 := CJ_s1HP_sup_commutator_eq_J_A1 h
      inf1 := CJ_s1HP_inf_commutator_eq_A1 h
      comm1 := commute_CJ_s1HP_commutator_A1 h
      card_Cs := card_CJ_sHP_A1 h heq
      card_C12 := card_CJ_s1HP_mul_s2HP_A1 h heq
      supS := CJ_sHP_sup_commutator_eq_J_A1 h
      infS := CJ_sHP_inf_commutator_eq_A1 h
      commS := commute_CJ_sHP_commutator_A1 h }
  have hσ : ((sHP D : ↥(H z)) : G) = ((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹ := rfl
  rw [hσ] at hstar
  refine lemma13_core D hy ?_ ?_ hstar
  · rw [← hσ, Subgroup.orderOf_coe, orderOf_sHP]
  · rw [← hσ]
    exact congrArg Subtype.val (uHP_conj_sHP D)

end CFSG.RankThree.GF2n.Parrott
