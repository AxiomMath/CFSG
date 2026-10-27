module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.SpinGeom CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private theorem sixteenC8H1Index_card_singular_spinW :
    Nat.card {w : SpinW // w ≠ 1 ∧ spinQ w = 0} = 135 := by
  have e : {w : SpinW // w ≠ 1 ∧ spinQ w = 0} ≃
      {v : Fin (2 * 4) → ZMod 2 //
        v ≠ 0 ∧ coordinateQuadPlus 4 (ZMod 2) v = 0} :=
    Equiv.subtypeEquiv
      (show SpinW ≃ (Fin (2 * 4) → ZMod 2) from
        { toFun := Multiplicative.toAdd
          invFun := Multiplicative.ofAdd
          left_inv := fun w => by simp
          right_inv := fun v => by simp })
      (fun w => by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by simpa [toAdd_eq_zero] using h1, by simpa [spinQ] using h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by simpa [toAdd_eq_zero] using h1, by simpa [spinQ] using h2⟩)
  rw [Nat.card_congr e, card_nonzero_singular_eight (K := ZMod 2), Nat.card_zmod]
  norm_num

theorem index_stabilizer_E0 :
    (MulAction.stabilizer ↥spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0))).index = 135 := by
  let w₀ : SpinW := Multiplicative.ofAdd (frameE (ZMod 2) 0)
  have hw0 : w₀ = Multiplicative.ofAdd (frameE (ZMod 2) 0) := rfl
  have hw0ne : w₀ ≠ 1 := by
    rw [hw0]
    simpa [ofAdd_eq_one] using frameE_ne_zero (K := ZMod 2)
  have hQw0 : spinQ w₀ = 0 := by
    rw [hw0, spinQ, toAdd_ofAdd]
    exact quad_frameE 0
  have hXorbit : MulAction.orbit ↥spinH w₀ = {w : SpinW | w ≠ 1 ∧ spinQ w = 0} := by
    ext w'
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      rw [show w' = g • w₀ from hg.symm]
      change (g : MulAut SpinW) w₀ ≠ 1 ∧ spinQ ((g : MulAut SpinW) w₀) = 0
      refine ⟨?_, ?_⟩
      · intro h1
        have h2 : (g : MulAut SpinW) w₀ = (g : MulAut SpinW) 1 := by
          rw [h1, map_one]
        exact hw0ne ((g : MulAut SpinW).injective h2)
      · rw [spinQ_spinH g.2, hQw0]
    · rintro ⟨hw'1, hw'0⟩
      have hv : Multiplicative.toAdd w' ≠ 0 := by
        simpa [toAdd_eq_zero] using hw'1
      have hQ : coordinateQuadPlus 4 (ZMod 2) (Multiplicative.toAdd w') = 0 := by
        simpa [spinQ] using hw'0
      obtain ⟨h, hh, hact⟩ := spinSeven_transitive (ZMod 2) (Multiplicative.toAdd w') hv hQ
      refine ⟨⟨spinHom h, (mem_spinH_iff (spinHom h)).mpr ⟨h, hh, rfl⟩⟩, ?_⟩
      change (spinHom h) w₀ = w'
      rw [spinHom_apply,
        show Multiplicative.toAdd w₀ = frameE (ZMod 2) 0 from rfl, hact]
      rfl
  have hcardX : ({w : SpinW | w ≠ 1 ∧ spinQ w = 0} : Set SpinW).ncard = 135 := by
    rw [← Nat.card_coe_set_eq]
    exact sixteenC8H1Index_card_singular_spinW
  have hidx := MulAction.index_stabilizer (↥spinH) w₀
  change (MulAction.stabilizer ↥spinH w₀).index = 135
  rw [hidx, hXorbit, hcardX]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
