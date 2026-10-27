module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverBounds
public import CFSG.Sporadic.Bridge.J3Surj

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer
open CFSG.Sporadic.J3 (a b J closure_ab)
open CFSG.Sporadic.J3.Native (j3Data)

theorem gen_zero : gen 0 = a j3Data := by
  simp [gen, genWords, ab, img2, FreeGroup.lift_mk]

theorem gen_two : gen 2 = b j3Data := by
  simp [gen, genWords, ab, img2, FreeGroup.lift_mk]

theorem closure_gen : Subgroup.closure (Set.range gen) = ⊤ :=
  closure_range_eq_top (gen := gen) (closure_ab j3Data) (sA := [(0, true)]) (sB := [(2, true)])
    (by simp [FreeGroup.lift_mk, gen_zero]) (by simp [FreeGroup.lift_mk, gen_two])

theorem card_J : Nat.card (J j3Data) = 50232960 := by
  rw [← Nat.card_congr CFSG.Sporadic.Bridge.J3.nativeEquiv.toEquiv, CFSG.Sporadic.J3.card_J3]

section Words

variable (h : ∀ w ∈ checkWords, FreeGroup.lift gen (FreeGroup.mk w) = 1)
include h

theorem lift_gen_rels : ∀ r ∈ rels, FreeGroup.lift gen (FreeGroup.mk r) = 1 := fun _ hr =>
  h _ (List.mem_append_left _ hr)

theorem lift_gen_commWord (i : Fin 3) :
    FreeGroup.lift gen (FreeGroup.mk (commWord i)) = gen i := by
  have h1 : FreeGroup.lift gen (FreeGroup.mk ((i, false) :: commWord i)) = 1 :=
    h _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  rw [show FreeGroup.mk ((i, false) :: commWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (commWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

end Words

theorem mem_cover_of_mem_coverS {w : List (Fin 3 × Bool)} (hw : w ∈ coverS) :
    w ∈ coverWords rels commWord :=
  (List.mergeSort_perm _ _).mem_iff.1 hw

theorem mem_coverS_commWord (i : Fin 3) : (i, false) :: commWord i ∈ coverS := by
  refine (List.mergeSort_perm _ _).mem_iff.2 ?_
  simp only [coverWords, List.mem_append, List.mem_map, List.mem_finRange, true_and]
  exact Or.inr ⟨i, rfl⟩

theorem mk_commWord_mem (i : Fin 3) :
    FreeGroup.mk (commWord i) ∈ commutator (FreeGroup (Fin 3)) :=
  mk_commWords_mem_commutator _

theorem walkWord_mem : walkWord ∈ rels := by decide

theorem card_hopfMultiplier_J
    (h : ∀ w ∈ checkWords, FreeGroup.lift gen (FreeGroup.mk w) = 1)
    (hP : Finite (PG 3 coverS) ∧ Nat.card (PG 3 coverS) ≤ 150698880)
    (hord : 3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}
      (FreeGroup.mk walkWord))) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (J j3Data)) = 3 := by
  obtain ⟨hfin, hle⟩ := hP
  have hcard : Nat.card (PG 3 coverS) ≤ 3 * Nat.card (J j3Data) := by
    rw [card_J]; exact hle
  have hR := lift_gen_rels h
  have hwg := lift_gen_commWord h
  obtain ⟨hpos, hup⟩ := card_hopfMultiplier_le_of_cover closure_gen hR mk_commWord_mem hwg
    (fun w hw => mem_cover_of_mem_coverS hw) mem_coverS_commWord hfin hcard
  have hdvd := dvd_card_hopfMultiplier_of_cover closure_gen hR mk_commWord_mem hwg
    (fun w hw => mem_cover_of_mem_coverS hw) mem_coverS_commWord hfin hcard
    (lift_gen_rels h _ walkWord_mem) hord
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover
