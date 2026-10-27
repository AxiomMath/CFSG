module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier CFSG.Blueprint

theorem pv_exists_inv_heis
    (α : MulAut Pv)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  by_cases hout : α ∈ (MulAut.conj : Pv →* MulAut Pv).range
  · obtain ⟨t, ht⟩ := hout
    rw [← ht] at hα2 hα1 ⊢
    have hconj : MulAut.conj (t * t) = 1 := by
      rw [map_mul, hα2]
    have hmem : t * t ∈ Subgroup.center Pv := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : t * (t * g * t⁻¹) * t⁻¹ = g := by
        have := congrArg (fun f : MulAut Pv => f g) hα2
        simpa [MulAut.conj_apply] using this
      calc
        g * (t * t) = ((t * (t * g * t⁻¹) * t⁻¹) * t) * t := by rw [h2]; group
        _ = (t * t) * g := by group
    have hZ : Subgroup.center Pv = ⊥ := by
      have hS : IsSimpleGroup Pv :=
        @MulEquiv.isSimpleGroup Pv _ Blueprint.NativeSporadic.ON _
          CFSG.Sporadic.ON.isSimpleGroup_ON CFSG.ONSchreier.onEquivPv.symm
      exact @CFSG.Sporadic.ONOddCore.center_eq_bot_of_simple' Pv _ hS
        CFSG.Sporadic.ONOddCore.pv_not_comm
    have htt : t * t = 1 := by
      rw [hZ] at hmem
      simpa using hmem
    have ht1 : t ≠ 1 := by
      intro h
      apply hα1
      rw [h, map_one]
    obtain ⟨z, hz, hzt⟩ := on_exists_inv_of_inner htt ht1
    exact ⟨z, hz, by rw [MulAut.conj_apply]; exact hzt⟩
  · exact on_exists_inv_of_outer hout hα2

theorem on_exists_inv_heis
    (σ : MulAut (NativeSporadic.Carrier .ONan)) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ z : NativeSporadic.Carrier .ONan, IsHeisCenter7 z ∧ σ z = z⁻¹ := by
  let e : NativeSporadic.Carrier .ONan ≃* Pv := CFSG.ONSchreier.onEquivPv
  let α : MulAut Pv := MulAut.congr e σ
  have hα2 : α * α = 1 := by
    change MulAut.congr e σ * MulAut.congr e σ = 1
    rw [← map_mul, hσ2, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply hσ1
    exact (MulAut.congr e).injective (by simpa only [map_one] using h)
  obtain ⟨z, hz, hzα⟩ := pv_exists_inv_heis α hα2 hα1
  refine ⟨e.symm z, hz.map e.symm.toMonoidHom e.symm.injective, ?_⟩
  have hc : σ (e.symm z) = e.symm (MulAut.congr e σ z) := by
    simp [MulAut.congr_apply]
  rw [hc, hzα, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
