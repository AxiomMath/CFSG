module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16NineOpp
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78At3
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Cent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Tensor
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4TI
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)

variable {G : Type} [Group G] [Finite G]

theorem s16t_false_of_case2_l4_v0 (D : Data G) (hin : In10 D) (h119 : F11.R119 D)
    (h78 : R7_8At3 D) (h96 : UC9R96.R9_6At7 D) (h921 : R9_21Opp D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h2 : Case168_2L4 D V₀ V hV L) (hV₀ : V₀ ≠ ⊥) : False := by
  have hS : S16tL4Setting D V₀ V L hV := s16t_l4_setting_of_case168_2L4 hc h2 hV₀
  have hMst : D.M ≤ stabTil V₀ V := s16t_l4_le_stabTil hS
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h3σ : 3 ∈ D.sig := by rw [hS.shape.2.2]; simp
  have hSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    UC6S846.sp_of_mem_sig hin.hSg (s16t_l4_not_solvable hS) h3σ
  obtain ⟨Y, hY⟩ := s16t_l4_exists_Y hin.h127 h119 hS
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp3 (H := D.M) (k := 3)
      (hin.hx.three_le 3 h3σ)
  refine s16t_l4_false_of_fix_or_uniqueMax D hin.h61 hin.h127 (hV := hV) hc.setting.hyp16 hMst
    hp3 le_rfl h3σ hEM hEel hEcard fun w hw hwV₀ => ?_
  have hw1 : tilOf V₀ V hV w hw ≠ 1 := by
    intro h1
    rw [tilOf, ← map_one (mkTil V₀ V hV), mkTil_eq_iff] at h1
    have h3 : (IntMod.mk hV ⟨w, hw⟩).val ∈ V₀ := by simpa using h1
    exact hwV₀ h3
  obtain ⟨hK, ⟨L₀, -, -, hL, hsum⟩, -⟩ := hS.shape
  rcases s16t_l4_tensor_dichotomy hK hL (s16t_l4_lbar_simple hS)
      (by rw [s16t_l4_card_lbar hS]; norm_num) (s16t_l4_mbar_direct hS) hsum hw1 with
    ⟨F, hFM, hFel, hFcard, hFfix⟩ | ⟨τ, hτM, hτ1, hτL, hτw⟩
  · obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_map_le (barHom V₀ V hV hMst) hp3
      (Eb := F) (by rw [range_barHom]; exact hFM) hFel.isPGroup
      (s16c1610_not_isCyclic_of_isElemAbelian hp3 hFel (by rw [hFcard]; norm_num))
    exact Or.inl ⟨B, hBp, hBc, fun b hb => hFfix _ (hB b hb)⟩
  · have hτK : τ ∈ kBar D.M V₀ V hV L :=
      Subgroup.mem_inf.2 ⟨hτM, Subgroup.mem_centralizer_iff.2 fun h hh => (hτL h hh).symm⟩
    exact Or.inr (s16t_l4_uniqueMax_of_ptStab hS hSP hin.h61 h921 h96 h78 hV₀ hY hw
      (s16t_l4_ptStab_of_fix hS hw hwV₀ hτK hτ1 hτw))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
