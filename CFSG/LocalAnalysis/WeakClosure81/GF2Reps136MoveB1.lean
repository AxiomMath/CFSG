module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveA
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SectTransfer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_mQuot_eq_rk_section (I Z : Subgroup W) :
    E3.mQuot I Z = rk ↥(⊤ : Subgroup (Sect I Z)) := by
  rw [CFSG.Quasithin.rk_top]
  rfl

private theorem w1369_commutator_eq_self_of_quasisimple {G : Type*} [Group G]
    {L : Subgroup G} (h : CFSG.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1.commutator_eq_top] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

theorem move_gl3 (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    secSub I (Cd L) L = ⊤ ∧ Nat.card (Sect I (Cd L)) = 2 ^ 3 := by
  have hCd : Cd L = I ⊓ fixV L := (move_C hw2 S).1
  have hCI : Cd L ≤ I := by rw [hCd]; exact inf_le_left
  have hmQuot : E3.mQuot I (Cd L) = 3 := by
    rw [hCd]
    exact (move_rank hw2 S).1
  have hStab : StabPair L I (Cd L) := by
    intro l hl
    refine ⟨S.hI.2.2.1 l hl, ?_⟩
    rw [hCd]
    exact S.hI.2.2.2.1 l hl
  have hnt : ¬ ∀ l ∈ L, ∀ u ∈ I, l u * u⁻¹ ∈ Cd L := by
    intro h
    have hle : commSub I L ≤ Cd L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, u, hu, rfl⟩
      exact h l hl u hu
    rw [S.hI.1, hCd] at hle
    exact (ne_of_lt S.hI.2.1) (le_antisymm hle inf_le_left).symm
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.Quasithin.B1Red.isQuasisimple_of_open S.ctx.comp.2.2
  have hqH : CFSG.IsQuasisimple ↥(secSub I (Cd L) L) :=
    isQuasisimple_secSub hStab hLq hnt
  have hperf : ⁅secSub I (Cd L) L, secSub I (Cd L) L⁆ = secSub I (Cd L) L :=
    w1369_commutator_eq_self_of_quasisimple hqH
  have hrk : rk ↥(⊤ : Subgroup (Sect I (Cd L))) ≤ 3 := by
    rw [← w1369_mQuot_eq_rk_section I (Cd L)]
    exact le_of_eq hmQuot
  have hne : secSub I (Cd L) L ≠ ⊥ := by
    intro hbot
    exact hnt ((w1369_secSub_eq_bot_iff hCI hStab).mp hbot)
  obtain ⟨hrk3, htop⟩ :=
    w16f_perfect_gl_three (W := Sect I (Cd L)) (sect_exp_two hw2 I (Cd L)) hrk
      (secSub I (Cd L) L) hperf hne
  refine ⟨htop, ?_⟩
  have hfin : IsPGroup 2 (Sect I (Cd L)) :=
    isPGroup_two_of_sq_eq_one (sect_exp_two hw2 I (Cd L))
  have hrk3' : rk (Sect I (Cd L)) = 3 := by
    rw [← CFSG.Quasithin.rk_top]
    exact hrk3
  rw [card_eq_two_pow_of_isPGroup hfin, hrk3']

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
