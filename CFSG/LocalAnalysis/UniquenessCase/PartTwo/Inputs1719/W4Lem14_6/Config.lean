module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleAltTwoHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Structure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ASetSummands
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
public import CFSG.Quasithin.Background.HLUBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem commV_eq_of_rk_lt_dMinDeg {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    {I : Subgroup W} (hI : I ∈ irrSet L) (hrk : rk ↥(commV L) < rk ↥I + dMinDeg ↥L) :
    commV L = I := by
  have : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hIle : I ≤ commSub (⊤ : Subgroup W) L := by
    calc I = commSub I L := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl
  have hSK : StableUnder L (commSub (⊤ : Subgroup W) L) :=
    fun x hx u hu => CFSG.Quasithin.Asc81c.commSub_stable' hx hu
  have hle : commSub (commSub (⊤ : Subgroup W) L) L ≤ I :=
    Inputs1719.commSub_le_of_rk_lt_dMinDeg hW hIle hSK hI.2.2.1 (by
      rw [← CFSG.Quasithin.commV_eq_commSub]
      omega)
  have hperfS := CFSG.Quasithin.RonanF918.commSub_commSub_eq_of_perfect (L := L)
    (S := (⊤ : Subgroup W)) (fun _ _ _ _ => Subgroup.mem_top _)
  rw [hperfS] at hle
  rw [CFSG.Quasithin.commV_eq_commSub]
  exact le_antisymm hle hIle

theorem exists_involution_of_autSub {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hs : IsSimpleGroup ↥L)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
      (fun X => commV (autQuot X (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet L) (hLI : commV L = I)
    {t : MulAut ↥I} (ht : t ∈ autSub L I) (ht2 : orderOf t = 2) :
    ∃ s ∈ L, orderOf s = 2 ∧
      rkIdx (fixV (Subgroup.zpowers s)) = rkIdx (fixV (Subgroup.zpowers t)) := by
  have hLs := Thm14_5.le_stabSub_of_mem_irrSet hI
  have hinj : Function.Injective (Thm14_5.resTo hLs) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Thm14_5.resTo hLs).ker with h | h
    · exact h
    · exfalso
      apply CFSG.LocalAnalysis.WeakClosure81.not_le_fixV_of_mem_irrSet hI
      intro u hu
      rw [mem_fixV]
      intro l hl
      have hk : (⟨l, hl⟩ : ↥L) ∈ (Thm14_5.resTo hLs).ker := h ▸ Subgroup.mem_top _
      exact (Thm14_5.resTo_eq_one_iff hLs _).mp hk u hu
  obtain ⟨⟨s, hsL⟩, hst⟩ := Thm14_5.resTo_surjective hLs ⟨t, ht⟩
  refine ⟨s, hsL, ?_, ?_⟩
  · have h1 : orderOf (⟨s, hsL⟩ : ↥L) = orderOf (⟨t, ht⟩ : ↥(autSub L I)) := by
      rw [← hst]
      exact (orderOf_injective _ hinj _).symm
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    rw [h1, ht2]
  · have htop : I ⊔ fixV L = ⊤ := hLI ▸ commV_sup_fixV_eq_top_of_isDirSumOver hL hsum
    refine rkIdx_fixV_zpowers_eq_of_fix_sup htop
      (fun u hu => (mem_stabSub.mp (hLs hsL) u).mpr hu) (fun x hx => mem_fixV.mp hx s hsL)
      (MulEquiv.refl ↥I) t ?_
    intro u
    apply Subtype.ext
    have h := congrArg (fun φ : ↥(autSub L I) => (((φ : MulAut ↥I) u : ↥I) : W)) hst
    simp only [Thm14_5.resTo_apply] at h
    simpa using h.symm

theorem aParam_le_one_of_summand {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV)
    {I : Subgroup W} (hLI : commV L = I) (ha : E3.aParam (autSub Y I) ≤ 1) :
    E3.aParam Y ≤ 1 := by
  refine Thm14_5.aParam_le_of_permutes hW
    (Wf := fun X : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y =>
      commV (X : Subgroup (MulAut W))) hsum.1 hsum.2 ?_ le_rfl ?_
  · rintro y hy ⟨X', g, hg, rfl⟩
    refine ⟨⟨L.map (MulAut.conj (y * g)).toMonoidHom, y * g, Y.mul_mem hy hg, rfl⟩, ?_⟩
    simp only
    rw [CFSG.Quasithin.commV_map_conj_eq, CFSG.Quasithin.commV_map_conj_eq, Subgroup.map_map]
    rfl
  · rintro ⟨X', g, hg, rfl⟩
    simp only
    rw [CFSG.Quasithin.commV_map_conj_eq, hLI]
    have hU : ∀ v, v ∈ I ↔ g v ∈ I.map g.toMonoidHom := fun v =>
      (Subgroup.mem_map_iff_mem (f := g.toMonoidHom) g.injective).symm
    have hc : H.congrHom g = (MulAut.conj g).toMonoidHom := by
      ext φ x
      rfl
    have hYg : Y.map (H.congrHom g) = Y := by
      rw [hc]
      apply le_antisymm
      · rintro _ ⟨φ, hφ, rfl⟩
        exact Y.mul_mem (Y.mul_mem hg hφ) (Y.inv_mem hg)
      · intro φ hφ
        refine ⟨g⁻¹ * φ * g, Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hφ) hg, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    have hmap := H.LU.autSub_map g Y hU
    rw [hYg] at hmap
    rw [hmap, H.aParam_map_congrHom]
    exact ha

theorem setup_of_case2 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV X = ⊥)
    (hsum0 : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
      (fun X' => commV (autQuot X' (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet L)
    (hIm : (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
      E3.mParam Y) :
    autSub L I ≤ autSub Y I ∧ ((autSub L I).subgroupOf (autSub Y I)).Normal ∧
      IsIrrOn (autSub L I) ⊤ ⊥ ∧ rk ↥I ≤ rk ↥(commV L) ∧
      E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I ∧
      E3.mParam (autSub Y I) ≤ E3.mParam Y := by
  have hsum := Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
  have hIle : I ≤ commV L := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    calc I = commSub I L := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl
  have hIfix : I ⊓ fixV L = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hIle)
  have hrk : rk ↥I ≤ rk ↥(commV L) := rk_mono hIle
  have hIpos : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hW).mp h0)
        (CFSG.LocalAnalysis.WeakClosure81.ne_bot_of_mem_irrSet hI)
    · exact h0
  have hmul : E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I := by
    have hpos : (0 : ℚ) < rk ↥I := by exact_mod_cast hIpos
    have h := hIm
    rw [mul_div_assoc', div_le_iff₀ hpos] at h
    exact_mod_cast h
  refine ⟨autSub_mono hL.1 I,
    Thm14_5.normal_autSub_of_normalizes
      (fun y hy hyI => Thm14_5.mem_normalizer_of_mem_stabSub hsum hI hy hyI),
    Thm14_5.isIrrOn_autSub_of_mem_irrSet hI hIfix, hrk, hmul, ?_⟩
  have h2 : E3.mParam (autSub Y I) * rk ↥I ≤ E3.mParam Y * rk ↥I :=
    (Nat.mul_le_mul_left _ hrk).trans hmul
  exact Nat.le_of_mul_le_mul_right h2 hIpos

theorem lieModel_autSub {W : Type} [CommGroup W] [Finite W] {Y L X : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (hfix : fixV X = ⊥)
    (hsum0 : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
      (fun X' => commV (autQuot X' (⊥ : Subgroup W))))
    (hs : IsSimpleGroup ↥L) {I : Subgroup W} (hI : I ∈ irrSet L)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ}
    (h : CFSG.Blueprint.LieModel ↥L t m p f) : CFSG.Blueprint.LieModel ↥(autSub L I) t m p f := by
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
  have hIle : I ≤ commV L := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    calc I = commSub I L := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl
  have hIfix : I ⊓ fixV L = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf_right _ hIle)
  have hLI := Thm14_5.le_stabSub_of_mem_irrSet hI
  have hne := Thm14_5.not_le_centSub_of_mem_irrSet hI hIfix
  exact UC22.lieModel_of_surjective_of_isSimple hs (Thm14_5.resTo hLI)
    (Thm14_5.resTo_surjective hLI) (Thm14_5.nontrivial_autSub hLI hne) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
