module

public import CFSG.Quasithin.H13.GoldschmidtC137SQRk
public import CFSG.GH74.KGroups.U33
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

theorem statedClassicalModel_of_lieModel_psu {Y : Type} [Group Y] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel Y .PSU n p f) : StatedClassicalModel Y .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem exists_mulEquiv_statedSU_of_lieModel {Y : Type} [Group Y] (h : LieModel Y .PSU 3 3 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧
      Nonempty (Y ≃* StatedSU 3 3 F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psu (by norm_num) h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have hbot := statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e' : StatedProj (StatedSU 3 (3 ^ 1) F) ≃* StatedSU 3 3 F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨F, inferInstance, inferInstance, hF9, ⟨e.trans e'⟩⟩

theorem simple_card_of_lieModel_psu_three_three {Y : Type} [Group Y]
    (h : LieModel Y .PSU 3 3 1) : IsSimpleGroup Y ∧ Nat.card Y = 6048 := by
  have hm := statedClassicalModel_of_lieModel_psu (by norm_num) h
  refine ⟨(CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 3 1 hm).2, ?_⟩
  obtain ⟨F, _, _, hF9, ⟨e⟩⟩ := exists_mulEquiv_statedSU_of_lieModel h
  rw [Nat.card_congr e.toEquiv]
  exact card_statedSU hF9

theorem center_eq_bot_of_simple {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hp : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    let _ : CommGroup Y :=
      { ‹Group Y› with
        mul_comm := fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) }
    exact hp IsSimpleGroup.prime_card

theorem rankLeTwo_of_lieModel_psu_three_three
    {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSU 3 3 1) : RankLeTwo Y := by
  obtain ⟨hs, hcard⟩ := simple_card_of_lieModel_psu_three_three h
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  refine rankLeTwo_of_three (Or.inr (Or.inr (Or.inr hcard))) fun E hE => ?_
  have hcen : Subgroup.center Y = ⊥ := center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro k
      have := DFunLike.congr_fun hg k
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rwa [hcen, Subgroup.mem_bot] at this
  have hR : CFSG.GH74.KGroups.ElemAb 3 (E.map (MulAut.conj : Y →* MulAut Y)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  have := CFSG.GH74.KGroups.U33.autRank3_le_two e _ hR
  rwa [Subgroup.card_map_of_injective hinj] at this

end CFSG.Quasithin.H13.U3.GC137.SQ
