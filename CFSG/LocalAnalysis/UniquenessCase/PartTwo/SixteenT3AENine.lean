module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineAbs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_calABar_eq_empty_of_case168_9 (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hv1 : v1Sub D.M ⊥ V hV L = ⊥) (h9 : Case168_9 D ⊥ V hV L) :
    calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅ := by
  obtain ⟨Z, hZ, hZnorm, hZL, hZJ, hZf, -⟩ := s16t_case9_frame D h1217 hV hc hv1 h9
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar ⊥ V hV L)
      (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (lBar ⊥ V hV L)) ⊥ 3 := hsum
  obtain ⟨hind, hsup⟩ := s16t_case9_directSum D h1217 hV hc.setting.hyp151 hv1 hc.ne_bot
  have hrk0 : rk ↥(wTil ⊥ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hc.setting.hyp151 hv1 hc.ne_bot hs15 hsum
  have hn2 : (conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
  have habs := s16c167_cfg9_abstract (X := Mbar D.M ⊥ V hV) (L := lBar ⊥ V hV L) hW hL hsum'
    hcls hn2 hind hsup
  have hm3 : 3 ≤ mBar D.M ⊥ V hV := habs.2.2.2
  have hempty := s16t_aSet_three_eq_empty_of_case9 (X := Mbar D.M ⊥ V hV)
    (L := lBar ⊥ V hV L) hW hL hsum' hcls hn2 hind hsup hZ hZnorm hZL hZJ hZf
  have h3 := E3.aSet_anti hm3 (Mbar D.M ⊥ V hV)
  rw [hempty] at h3
  exact Set.subset_empty_iff.1 h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
