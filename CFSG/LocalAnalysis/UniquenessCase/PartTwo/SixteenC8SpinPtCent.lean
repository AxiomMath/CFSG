module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem nonempty_ptCent_mulEquiv_of_orbit {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {w w' : W} (h : ∃ g ∈ H, g w = w') :
    Nonempty (↥(ptCent H w) ≃* ↥(ptCent H w')) := by
  obtain ⟨g, hgH, hgw⟩ := h
  have hg' : g⁻¹ w' = w := by rw [← hgw, MulAut.inv_apply_self]
  have hmem_to (x : ↥(ptCent H w)) : MulAut.conj g (x : MulAut W) ∈ ptCent H w' := by
    obtain ⟨hxH, hxstab⟩ := Subgroup.mem_inf.mp x.2
    have hxw : (x : MulAut W) w = w := by
      simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.mp hxstab
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH)
    · rw [MulAction.mem_stabilizer_iff]
      change (MulAut.conj g (x : MulAut W)) w' = w'
      rw [MulAut.conj_apply]
      calc (g * (x : MulAut W) * g⁻¹) w' = g ((x : MulAut W) (g⁻¹ w')) := rfl
        _ = g ((x : MulAut W) w) := by rw [hg']
        _ = g w := by rw [hxw]
        _ = w' := hgw
  have hmem_inv (y : ↥(ptCent H w')) : (MulAut.conj g).symm (y : MulAut W) ∈ ptCent H w := by
    obtain ⟨hyH, hystab⟩ := Subgroup.mem_inf.mp y.2
    have hyw : (y : MulAut W) w' = w' := by
      simpa only [MulAut.smul_def] using MulAction.mem_stabilizer_iff.mp hystab
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAut.conj_symm_apply]
      exact H.mul_mem (H.mul_mem (H.inv_mem hgH) hyH) hgH
    · rw [MulAction.mem_stabilizer_iff]
      change ((MulAut.conj g).symm (y : MulAut W)) w = w
      rw [MulAut.conj_symm_apply]
      calc (g⁻¹ * (y : MulAut W) * g) w = g⁻¹ ((y : MulAut W) (g w)) := rfl
        _ = g⁻¹ ((y : MulAut W) w') := by rw [hgw]
        _ = g⁻¹ w' := by rw [hyw]
        _ = w := hg'
  refine ⟨{ toFun := fun x => ⟨MulAut.conj g (x : MulAut W), hmem_to x⟩,
            invFun := fun y => ⟨(MulAut.conj g).symm (y : MulAut W), hmem_inv y⟩,
            left_inv := fun x => Subtype.ext ((MulAut.conj g).symm_apply_apply (x : MulAut W)),
            right_inv := fun y => Subtype.ext ((MulAut.conj g).apply_symm_apply (y : MulAut W)),
            map_mul' := fun x y => by
              apply Subtype.ext
              exact (MulAut.conj g).map_mul (x : MulAut W) (y : MulAut W) }⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
