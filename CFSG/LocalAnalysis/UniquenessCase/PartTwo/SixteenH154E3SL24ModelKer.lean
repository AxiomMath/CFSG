module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelKerA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup

theorem s16h_orth3_kernel_Z {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3)))
    (hnZ : ∀ z ∈ orth3Z, n z = z) : n ∈ orth3L := by
  have hZ : ∀ z : GF4, Multiplicative.ofAdd (0, 0, z) ∈ orth3Z := by
    intro z
    exact ⟨rfl, rfl⟩
  rcases s16h_orth3_normalizer_form hn with ⟨μ, hμ, γ, hform⟩ | ⟨μ, hμ, γ, hform⟩
  · have hμ1 : μ = 1 := by
      have h := hform (Multiplicative.ofAdd (0, 0, (1 : GF4)))
      rw [s16h_orth3Scal_act_radical μ hμ γ 1] at h
      have h2 := hnZ _ (hZ 1)
      have h4 := congrArg (fun w : Orth3 => (Multiplicative.toAdd w).2.2) (h.symm.trans h2)
      simpa using h4
    subst μ
    refine Subgroup.subset_closure ⟨(γ : Matrix.GeneralLinearGroup (Fin 2) GF4), γ.2, ?_⟩
    intro v
    rw [hform v]
    exact s16h_orth3Scal_one_apply hμ _
  · have hμ1 : μ = 1 := by
      have h := hform (Multiplicative.ofAdd (0, 0, (1 : GF4)))
      rw [s16h_orth3Scal_act_phi_radical μ hμ γ 1] at h
      have h2 := hnZ _ (hZ 1)
      have h4 := congrArg (fun w : Orth3 => (Multiplicative.toAdd w).2.2) (h.symm.trans h2)
      simpa using h4
    subst μ
    have h2 := hform (Multiplicative.ofAdd (0, 0, GF4.ofNat' 2))
    rw [s16h_orth3Scal_act_phi_radical 1 hμ γ (GF4.ofNat' 2)] at h2
    have h3 := hnZ _ (hZ (GF4.ofNat' 2))
    have h5 := congrArg (fun w : Orth3 => (Multiplicative.toAdd w).2.2) (h2.symm.trans h3)
    rw [one_mul] at h5
    exact absurd h5 (by decide : ¬ ((GF4.ofNat' 2) ^ 2 = GF4.ofNat' 2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
