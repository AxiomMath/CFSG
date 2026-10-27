module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Family
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.Open.StatedZModTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.SeitzReduction.F4PilotAmalgam

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Chevalley (subsystemGroup rootSpan_eq_closure)
open CFSG.RankThree.Chevalley (F4A2Kind f4A2Equiv)

local instance am6NeZeroRankLv : NeZero Tag.F4.rank := ⟨by decide⟩

section Model

open CFSG.Open CFSG.Open.StatedAPI
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

theorem statedClassicalModel_psl_three_two_of_sl {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 := by
  have hadm : StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  have proj : StatedSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    ((QuotientGroup.quotientMulEquivOfEq (by
        rw [statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf])).trans
      QuotientGroup.quotientBot).symm
  exact ⟨hadm, K, inferInstance, inferInstance, by rw [hK, pow_one],
    ⟨(e.trans (specialLinearGroupEquivStatedSL 3 K)).trans proj⟩⟩

end Model

section Lv


variable {K : Type} [Field K]

theorem map_Lv_eq_subsystemGroup (J : Finset (Fin (Tag.rank .F4))) :
    (Lv K J).map (adjointGroup .F4 K).subtype =
      subsystemGroup .F4 K (↑J : Set (Fin (Tag.rank .F4))) := by
  rw [Lv, map_subtype_levi_f4Datum, rootSpan_eq_closure, subsystemGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨α, ⟨j, hj, rfl | rfl⟩, c, rfl⟩
    · exact ⟨j, hj, c, Or.inl (pinnedX_single _ _ j c)⟩
    · exact ⟨j, hj, c, Or.inr (pinnedX_neg_single _ _ j c)⟩
  · rintro ⟨j, hj, c, rfl | rfl⟩
    · exact ⟨Pi.single j 1, ⟨j, hj, Or.inl rfl⟩, c, pinnedX_single _ _ j c⟩
    · exact ⟨-Pi.single j 1, ⟨j, hj, Or.inr rfl⟩, c, pinnedX_neg_single _ _ j c⟩

noncomputable def Lv_equiv_subsystemGroup (J : Finset (Fin (Tag.rank .F4))) :
    ↥(Lv K J) ≃* ↥(subsystemGroup .F4 K (↑J : Set (Fin (Tag.rank .F4)))) :=
  (Subgroup.equivMapOfInjective _ _ (adjointGroup .F4 K).subtype_injective).trans
    (MulEquiv.subgroupCongr (map_Lv_eq_subsystemGroup J))

noncomputable def LvA2Equiv (κ : F4A2Kind) :
    ↥(Lv K {κ.i, κ.j}) ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  (Lv_equiv_subsystemGroup {κ.i, κ.j}).trans
    ((MulEquiv.subgroupCongr (by simp [Finset.coe_insert])).trans (f4A2Equiv K κ))

theorem statedClassicalModel_Lv_zero_one [Finite K] (hK : Nat.card K = 2) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(Lv K {0, 1}) .PSL 3 2 1 :=
  statedClassicalModel_psl_three_two_of_sl hK (LvA2Equiv (K := K) .long)

theorem f4_root_support_zero_two_check :
    ∀ γ ∈ rootFinset .F4, γ 1 = 0 → γ 3 = 0 → γ 0 = 0 ∨ γ 2 = 0 := by
  decide +kernel

theorem commute_rootGroup_zero_two {s t : Fin (Tag.rank .F4) → ℤ}
    (hs : s = Pi.single 0 1 ∨ s = -Pi.single 0 1) (ht : t = Pi.single 2 1 ∨ t = -Pi.single 2 1)
    {x y : adjointGroup .F4 K} (hx : x ∈ (Adjoint.f4Datum K).rootGroup s)
    (hy : y ∈ (Adjoint.f4Datum K).rootGroup t) : Commute x y := by
  have hroot : ∀ v, v ∈ (Adjoint.f4Datum K).roots ↔ IsRoot .F4 v := fun v =>
    Adjoint.mem_adjDatum_roots
  have h10 : (1 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h20 : (2 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h30 : (3 : Fin (Tag.rank .F4)) ≠ 0 := by decide
  have h12 : (1 : Fin (Tag.rank .F4)) ≠ 2 := by decide
  have h13 : (1 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  have h23 : (2 : Fin (Tag.rank .F4)) ≠ 3 := by decide
  refine commute_of_forall_not_mem_roots (Adjoint.f4_steinbergExtras K) ?_ ?_ ?_ ?_ hx hy
  · rw [hroot]
    rcases hs with rfl | rfl
    exacts [isRoot_single _ 0, isRoot_neg_single _ 0]
  · rw [hroot]
    rcases ht with rfl | rfl
    exacts [isRoot_single _ 2, isRoot_neg_single _ 2]
  · intro a b hab
    have h0 := congrFun hab 0
    have h2 := congrFun hab 2
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h20, h20.symm] at h0 h2 <;> exact ⟨h0, h2⟩
  · intro a b ha hb hmem
    rw [hroot, ← mem_rootFinset] at hmem
    have h := f4_root_support_zero_two_check _ hmem
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [h10, h20, h30, h12, h13, h23, h20.symm] at h <;> omega

theorem commute_levi_zero_two :
    ∀ x ∈ Lv K {0}, ∀ y ∈ Lv K {2}, Commute x y := by
  unfold Lv
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.levi_singleton,
    CFSG.LieType.CurtisTits.rankOne, CFSG.LieType.CurtisTits.rankOne]
  refine forall_commute_sup_left (forall_commute_sup_right ?_ ?_)
    (forall_commute_sup_right ?_ ?_)
  · exact fun x hx y hy => commute_rootGroup_zero_two (Or.inl rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_two (Or.inl rfl) (Or.inr rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_two (Or.inr rfl) (Or.inl rfl) hx hy
  · exact fun x hx y hy => commute_rootGroup_zero_two (Or.inr rfl) (Or.inr rfl) hx hy

end Lv


end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
