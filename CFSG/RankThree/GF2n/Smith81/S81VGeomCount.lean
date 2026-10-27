module

public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

variable {F : Type} [Field F] [Finite F]

private theorem gcFinrankMap (W : Submodule F (Fin 6 → F)) (H : Submodule F W) :
    finrank F ↥(H.map W.subtype) = finrank F H :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective W.subtype Subtype.val_injective H)).symm

private def gcSubPointsEquiv (W : Submodule F (Fin 6 → F)) :
    {r : Submodule F (Fin 6 → F) // r ≤ W ∧ finrank F r = 1} ≃
      {H : Submodule F W // finrank F H = 1} where
  toFun r := ⟨r.1.comap W.subtype, by
    have h := gcFinrankMap W (r.1.comap W.subtype)
    rw [Submodule.map_comap_subtype, inf_eq_right.2 r.2.1, r.2.2] at h
    exact h.symm⟩
  invFun H := ⟨H.1.map W.subtype, Submodule.map_subtype_le W H.1, by
    rw [gcFinrankMap W H.1]
    exact H.2⟩
  left_inv r := by
    refine Subtype.ext ?_
    dsimp only
    rw [Submodule.map_comap_subtype, inf_eq_right.2 r.2.1]
  right_inv H := by
    refine Subtype.ext ?_
    dsimp only
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective H.1

private theorem gcCardPoints (W : Submodule F (Fin 6 → F)) :
    Nat.card {r : Submodule F (Fin 6 → F) // r ≤ W ∧ finrank F r = 1} =
      ∑ i ∈ Finset.range (finrank F W), Nat.card F ^ i :=
  (Nat.card_congr ((gcSubPointsEquiv W).trans (Projectivization.equivSubmodule F ↥W).symm)).trans
    (Projectivization.card_of_finrank F ↥W rfl)

private theorem gcExistsCompl {U : Submodule F (Fin 6 → F)} {z : Fin 6 → F} (hzU : z ∈ U)
    (hz0 : z ≠ 0) :
    ∃ C : Submodule F (Fin 6 → F), C ≤ U ∧ Submodule.span F {z} ⊔ C = U ∧
      Submodule.span F {z} ⊓ C = ⊥ ∧ finrank F C + 1 = finrank F U := by
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (Submodule.span F {z})
  have hspan : Submodule.span F {z} ≤ U := (Submodule.span_singleton_le_iff_mem z U).2 hzU
  have hsup : Submodule.span F {z} ⊔ (C' ⊓ U) = U := by
    rw [← sup_inf_assoc_of_le C' hspan, hC'.sup_eq_top, top_inf_eq]
  have hinf : Submodule.span F {z} ⊓ (C' ⊓ U) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left _ inf_le_left).trans hC'.inf_eq_bot.le)
  refine ⟨C' ⊓ U, inf_le_right, hsup, hinf, ?_⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {z}) (C' ⊓ U)
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hz0] at h
  omega

private theorem gcSupSpanInf {U C L : Submodule F (Fin 6 → F)} {z : Fin 6 → F}
    (hsup : Submodule.span F {z} ⊔ C = U) (hLU : L ≤ U) (hzL : z ∈ L) :
    Submodule.span F {z} ⊔ (L ⊓ C) = L := by
  have h1 : (Submodule.span F {z} ⊔ C) ⊓ L = Submodule.span F {z} ⊔ (C ⊓ L) :=
    sup_inf_assoc_of_le C ((Submodule.span_singleton_le_iff_mem z L).2 hzL)
  rw [hsup, inf_eq_right.2 hLU] at h1
  rw [inf_comm L C]
  exact h1.symm

private theorem gcFinrankInfCompl {L C : Submodule F (Fin 6 → F)} {z : Fin 6 → F}
    (hz0 : z ≠ 0) (hinf : Submodule.span F {z} ⊓ C = ⊥)
    (hL : Submodule.span F {z} ⊔ (L ⊓ C) = L) (hfin : finrank F L = 2) :
    finrank F ↥(L ⊓ C) = 1 := by
  have hbot : Submodule.span F {z} ⊓ (L ⊓ C) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left _ inf_le_right).trans hinf.le)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {z}) (L ⊓ C)
  rw [hL, hbot, finrank_bot, finrank_span_singleton hz0, hfin] at h
  omega

private theorem gcFinrankSupSpan {r C : Submodule F (Fin 6 → F)} {z : Fin 6 → F}
    (hz0 : z ≠ 0) (hinf : Submodule.span F {z} ⊓ C = ⊥) (hrC : r ≤ C)
    (hfin : finrank F r = 1) :
    finrank F ↥(r ⊔ Submodule.span F {z}) = 2 := by
  have hbot : r ⊓ Submodule.span F {z} = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ hrC).trans
      ((inf_comm C (Submodule.span F {z})).trans hinf).le)
  have h := Submodule.finrank_sup_add_finrank_inf_eq r (Submodule.span F {z})
  rw [hbot, finrank_bot, finrank_span_singleton hz0, hfin] at h
  omega

private def gcLinesEquiv {U C : Submodule F (Fin 6 → F)} {z : Fin 6 → F} (hz0 : z ≠ 0)
    (hzU : z ∈ U) (hCU : C ≤ U) (hsup : Submodule.span F {z} ⊔ C = U)
    (hinf : Submodule.span F {z} ⊓ C = ⊥) :
    {L : Submodule F (Fin 6 → F) // L ≤ U ∧ z ∈ L ∧ finrank F L = 2} ≃
      {r : Submodule F (Fin 6 → F) // r ≤ C ∧ finrank F r = 1} where
  toFun L := ⟨L.1 ⊓ C, inf_le_right,
    gcFinrankInfCompl hz0 hinf (gcSupSpanInf hsup L.2.1 L.2.2.1) L.2.2.2⟩
  invFun r := ⟨r.1 ⊔ Submodule.span F {z},
    sup_le (r.2.1.trans hCU) ((Submodule.span_singleton_le_iff_mem z U).2 hzU),
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z),
    gcFinrankSupSpan hz0 hinf r.2.1 r.2.2⟩
  left_inv L := by
    refine Subtype.ext ?_
    dsimp only
    rw [sup_comm]
    exact gcSupSpanInf hsup L.2.1 L.2.2.1
  right_inv r := by
    refine Subtype.ext ?_
    dsimp only
    rw [sup_inf_assoc_of_le _ r.2.1, hinf, sup_bot_eq]

theorem card_lines_through_three {U : Submodule F (Fin 6 → F)} (hU : finrank F U = 3)
    {z : Fin 6 → F} (hzU : z ∈ U) (hz0 : z ≠ 0) :
    Nat.card {L : Submodule F (Fin 6 → F) // L ≤ U ∧ z ∈ L ∧ finrank F L = 2} =
      Nat.card F + 1 := by
  obtain ⟨C, hCU, hsup, hinf, hfin⟩ := gcExistsCompl hzU hz0
  have hC : finrank F C = 2 := by omega
  rw [Nat.card_congr (gcLinesEquiv hz0 hzU hCU hsup hinf), gcCardPoints C, hC]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem card_lines_through_four {U : Submodule F (Fin 6 → F)} (hU : finrank F U = 4)
    {z : Fin 6 → F} (hzU : z ∈ U) (hz0 : z ≠ 0) :
    Nat.card {L : Submodule F (Fin 6 → F) // L ≤ U ∧ z ∈ L ∧ finrank F L = 2} =
      Nat.card F ^ 2 + Nat.card F + 1 := by
  obtain ⟨C, hCU, hsup, hinf, hfin⟩ := gcExistsCompl hzU hz0
  have hC : finrank F C = 3 := by omega
  rw [Nat.card_congr (gcLinesEquiv hz0 hzU hCU hsup hinf), gcCardPoints C, hC]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end CFSG.RankThree.GF2n.Smith81.S81V
