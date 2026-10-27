module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Dict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Nf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Split

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1e3_r2_le_r1 (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    s16c4v1_r2 V g ≤ s16c4v1_r1 V g := by
  obtain ⟨hEN, hE2, hcard⟩ := s16c4v1e3_dict_E S hstd.r1217 hg
  have hfix := s16c4v1e3_dict_fix S hstd hg hg'
  have hle := S.F.s16c4v1e3_card_mul_le hEN hE2
  rw [hcard, ← hfix] at hle
  have hpos : 0 < Nat.card (fixV (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g))) :=
    Nat.card_pos
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (Nat.le_of_mul_le_mul_right hle hpos)

theorem s16c4v1e3_eq_false (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹)
    (h : s16c4v1_r1 V g ≤ s16c4v1_r2 V g) : False := by
  have hr : s16c4v1_r2 V g = s16c4v1_r1 V g := le_antisymm (s16c4v1e3_r2_le_r1 S hstd hg hg') h
  obtain ⟨hEN, hE2, hcard⟩ := s16c4v1e3_dict_E S hstd.r1217 hg
  have heq := s16c4v1e3_dict_fix S hstd hg hg'
  rw [← hr, ← hcard] at heq
  obtain ⟨hc16, φ, hφ, hgen⟩ :=
    S.F.s16c4v1e3_eq_case hEN hE2 (s16c4v1e3_dict_ne_bot S hstd.r1217 hg) heq
  have hVle := s16c4v1e3_card_V_le S hstd.r1217 hg.1 hφ hgen
  rw [← s16c4v1e3_dict_comm S hstd hg hg'] at hc16
  rw [hc16, s16c4v1_card_V S] at hVle
  have h1 : 1 < Nat.card (v1Sub D.M ⊥ V hV L) := (Subgroup.one_lt_card_iff_ne_bot _).2 S.ne_bot
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
