module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.Quasithin.Background.B1Coprime

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem f4d2_component_le_commSub (hW : ∀ w : W, w * w = 1)
    {z : MulAut W} (hz : orderOf z = 7) {E : Subgroup (MulAut W)} {M : Subgroup W}
    (hMstab : StableUnder E M) (hMfix : M ⊓ fixV E = ⊥)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hzE : z ∈ E)
    {D : Subgroup (MulAut W)}
    (hD : D ∈ CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E)
    (hzhyp : Subgroup.zpowers z ∈
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes 7 E)
    (hDz : D ≠ Subgroup.zpowers z) :
    M ⊓ fixV D ≤ commSub ⊤ (Subgroup.zpowers z) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hZodd : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz]
    norm_num
  have hsup : D ⊔ Subgroup.zpowers z = E :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.sup_eq_of_hyperplanes hD hzhyp hDz
  have hUstab : StableUnder (Subgroup.zpowers z) (M ⊓ fixV D) := by
    intro y hy m hm
    rw [Subgroup.mem_inf] at hm ⊢
    refine ⟨hMstab y (Subgroup.zpowers_le.mpr hzE hy) m hm.1, ?_⟩
    rw [mem_fixV] at hm ⊢
    intro d hd
    have hcomm : d * y = y * d :=
      hEcomm d (hD.1 hd) y (Subgroup.zpowers_le.mpr hzE hy)
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hm.2 d hd]
  have hfix : (M ⊓ fixV D) ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [inf_assoc, ← w16g_fixV_sup D (Subgroup.zpowers z), hsup, hMfix]
  have hdec := CFSG.Quasithin.B1.coprime_decomp hW2 hZodd hUstab
  have hEq : M ⊓ fixV D = commSub (M ⊓ fixV D) (Subgroup.zpowers z) := by
    have h := hdec.1
    rw [hfix, bot_sup_eq] at h
    exact h.symm
  calc M ⊓ fixV D = commSub (M ⊓ fixV D) (Subgroup.zpowers z) := hEq
    _ ≤ commSub ⊤ (Subgroup.zpowers z) := commSub_mono le_top le_rfl

theorem f4d2_rk_iSup_hypPart_eq_sum {p : ℕ} {E : Subgroup (MulAut W)}
    (hdec : iSupIndep (fun D : hyperplanes p E => hypPart E D))
    (T : Finset (Subgroup (MulAut W))) (hT : ∀ D ∈ T, D ∈ hyperplanes p E) :
    rk ↥(⨆ D ∈ T, hypPart E D) = ∑ D ∈ T, rk ↥(hypPart E D) := by
  classical
  have hmap : (T.subtype (fun D => D ∈ hyperplanes p E)).map
      (Function.Embedding.subtype (fun D => D ∈ hyperplanes p E)) = T := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem hT]
  have hsup : (⨆ D ∈ T, hypPart E D) =
      ⨆ D ∈ T.subtype (fun D => D ∈ hyperplanes p E), hypPart E D := by
    conv_lhs => rw [← hmap]
    rw [← Finset.sup_eq_iSup, Finset.sup_map, Finset.sup_eq_iSup]
    rfl
  have hsum : (∑ D ∈ T, rk ↥(hypPart E D)) =
      ∑ D ∈ T.subtype (fun D => D ∈ hyperplanes p E), rk ↥(hypPart E D) := by
    conv_lhs => rw [← hmap]
    rw [Finset.sum_map]
    rfl
  rw [hsup, hsum,
    rk_iSup_biSup_eq_sum (fun D : hyperplanes p E => hypPart E D) hdec
      (T.subtype (fun D => D ∈ hyperplanes p E))]

theorem f4d2_sum_rk_le_commSub_ne (hW : ∀ w : W, w * w = 1)
    {E : Subgroup (MulAut W)}
    (hdec : iSupIndep (fun D : hyperplanes 7 E => hypPart E D))
    (hMstab : StableUnder E (commSub ⊤ E)) (hMfix : commSub ⊤ E ⊓ fixV E = ⊥)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {z : MulAut W} (hz : orderOf z = 7) (hzE : z ∈ E)
    (hzhyp : Subgroup.zpowers z ∈ hyperplanes 7 E)
    (T : Finset (Subgroup (MulAut W))) (hT : ∀ D ∈ T, D ∈ hyperplanes 7 E)
    (hTz : ∀ D ∈ T, D ≠ Subgroup.zpowers z) :
    ∑ D ∈ T, rk ↥(hypPart E D) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers z)) := by
  classical
  have hsum := f4d2_rk_iSup_hypPart_eq_sum hdec T hT
  have hle : (⨆ D ∈ T, hypPart E D) ≤ commSub ⊤ (Subgroup.zpowers z) := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    exact f4d2_component_le_commSub hW hz hMstab hMfix hEcomm hzE (hT D hD) hzhyp (hTz D hD)
  calc ∑ D ∈ T, rk ↥(hypPart E D) = rk ↥(⨆ D ∈ T, hypPart E D) := hsum.symm
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers z)) := rk_mono hle

end CFSG.LocalAnalysis.WeakClosure81
