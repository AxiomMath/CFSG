module

public import CFSG.LieType.SpinGeom.Elt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType.Triality CFSG.LieType.SpinGeom
open scoped Matrix

@[expose] noncomputable def fcoord (v : Fin (2 * 4) → ZMod 2) : Fin 8 → ZMod 2 :=
  ![coordX (ZMod 2) v 0, coordX (ZMod 2) v 1, coordX (ZMod 2) v 2, coordX (ZMod 2) v 3,
    coordY (ZMod 2) v 1, coordY (ZMod 2) v 2, coordY (ZMod 2) v 3, coordY (ZMod 2) v 0]

@[expose] noncomputable def fvec (u : Fin 8 → ZMod 2) : Fin (2 * 4) → ZMod 2 :=
  frameVec (ZMod 2) (u 0) ![u 1, u 2, u 3] ![u 4, u 5, u 6] (u 7)

theorem fcoord_fvec (u : Fin 8 → ZMod 2) : fcoord (fvec u) = u := by
  funext i
  fin_cases i
  · show coordX (ZMod 2) (fvec u) 0 = u 0
    rw [fvec, coordX_frameVec_zero]
  · show coordX (ZMod 2) (fvec u) (Fin.succ 0) = u 1
    rw [fvec, coordX_frameVec_succ]
    rfl
  · show coordX (ZMod 2) (fvec u) (Fin.succ 1) = u 2
    rw [fvec, coordX_frameVec_succ]
    rfl
  · show coordX (ZMod 2) (fvec u) (Fin.succ 2) = u 3
    rw [fvec, coordX_frameVec_succ]
    rfl
  · show coordY (ZMod 2) (fvec u) (Fin.succ 0) = u 4
    rw [fvec, coordY_frameVec_succ]
    rfl
  · show coordY (ZMod 2) (fvec u) (Fin.succ 1) = u 5
    rw [fvec, coordY_frameVec_succ]
    rfl
  · show coordY (ZMod 2) (fvec u) (Fin.succ 2) = u 6
    rw [fvec, coordY_frameVec_succ]
    rfl
  · show coordY (ZMod 2) (fvec u) 0 = u 7
    rw [fvec, coordY_frameVec_zero]

private theorem sixteenC8H1Coords_fcoord_frameVec (x₀ : ZMod 2) (x y : Fin 3 → ZMod 2)
    (y₀ : ZMod 2) :
    fcoord (frameVec (ZMod 2) x₀ x y y₀) =
      ![x₀, x 0, x 1, x 2, y 0, y 1, y 2, y₀] := by
  funext i
  fin_cases i
  · show coordX (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) 0 = x₀
    rw [coordX_frameVec_zero]
  · show coordX (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 0) = x 0
    rw [coordX_frameVec_succ]
  · show coordX (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 1) = x 1
    rw [coordX_frameVec_succ]
  · show coordX (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 2) = x 2
    rw [coordX_frameVec_succ]
  · show coordY (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 0) = y 0
    rw [coordY_frameVec_succ]
  · show coordY (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 1) = y 1
    rw [coordY_frameVec_succ]
  · show coordY (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) (Fin.succ 2) = y 2
    rw [coordY_frameVec_succ]
  · show coordY (ZMod 2) (frameVec (ZMod 2) x₀ x y y₀) 0 = y₀
    rw [coordY_frameVec_zero]

theorem fvec_fcoord (v : Fin (2 * 4) → ZMod 2) : fvec (fcoord v) = v := by
  have hx : (![coordX (ZMod 2) v 1, coordX (ZMod 2) v 2, coordX (ZMod 2) v 3] :
      Fin 3 → ZMod 2) = fun j => coordX (ZMod 2) v j.succ := by
    funext j
    fin_cases j <;> rfl
  have hy : (![coordY (ZMod 2) v 1, coordY (ZMod 2) v 2, coordY (ZMod 2) v 3] :
      Fin 3 → ZMod 2) = fun j => coordY (ZMod 2) v j.succ := by
    funext j
    fin_cases j <;> rfl
  rw [fvec]
  change frameVec (ZMod 2) (coordX (ZMod 2) v 0)
      ![coordX (ZMod 2) v 1, coordX (ZMod 2) v 2, coordX (ZMod 2) v 3]
      ![coordY (ZMod 2) v 1, coordY (ZMod 2) v 2, coordY (ZMod 2) v 3]
      (coordY (ZMod 2) v 0) = v
  rw [hx, hy]
  exact frameVec_coords v

private theorem sixteenC8H1Coords_fcoord_zero :
    fcoord (0 : Fin (2 * 4) → ZMod 2) = 0 := by
  funext i
  fin_cases i <;> simp [fcoord, coordX_zero, coordY_zero]

theorem fcoord_add (v w : Fin (2 * 4) → ZMod 2) : fcoord (v + w) = fcoord v + fcoord w := by
  funext i
  fin_cases i
  · show coordX (ZMod 2) (v + w) 0 = coordX (ZMod 2) v 0 + coordX (ZMod 2) w 0
    exact coordX_add v w 0
  · show coordX (ZMod 2) (v + w) (Fin.succ 0) =
        coordX (ZMod 2) v (Fin.succ 0) + coordX (ZMod 2) w (Fin.succ 0)
    exact coordX_add v w (Fin.succ 0)
  · show coordX (ZMod 2) (v + w) (Fin.succ 1) =
        coordX (ZMod 2) v (Fin.succ 1) + coordX (ZMod 2) w (Fin.succ 1)
    exact coordX_add v w (Fin.succ 1)
  · show coordX (ZMod 2) (v + w) (Fin.succ 2) =
        coordX (ZMod 2) v (Fin.succ 2) + coordX (ZMod 2) w (Fin.succ 2)
    exact coordX_add v w (Fin.succ 2)
  · show coordY (ZMod 2) (v + w) (Fin.succ 0) =
        coordY (ZMod 2) v (Fin.succ 0) + coordY (ZMod 2) w (Fin.succ 0)
    exact coordY_add v w (Fin.succ 0)
  · show coordY (ZMod 2) (v + w) (Fin.succ 1) =
        coordY (ZMod 2) v (Fin.succ 1) + coordY (ZMod 2) w (Fin.succ 1)
    exact coordY_add v w (Fin.succ 1)
  · show coordY (ZMod 2) (v + w) (Fin.succ 2) =
        coordY (ZMod 2) v (Fin.succ 2) + coordY (ZMod 2) w (Fin.succ 2)
    exact coordY_add v w (Fin.succ 2)
  · show coordY (ZMod 2) (v + w) 0 = coordY (ZMod 2) v 0 + coordY (ZMod 2) w 0
    exact coordY_add v w 0

private theorem sixteenC8H1Coords_vec3_add (a b c a' b' c' : ZMod 2) :
    (![a, b, c] + ![a', b', c'] : Fin 3 → ZMod 2) = ![a + a', b + b', c + c'] := by
  funext j
  fin_cases j <;> rfl

theorem fvec_add (u u' : Fin 8 → ZMod 2) : fvec (u + u') = fvec u + fvec u' := by
  simp only [fvec, Pi.add_apply]
  rw [frameVec_add, sixteenC8H1Coords_vec3_add, sixteenC8H1Coords_vec3_add]

@[expose] noncomputable def spinMu : ↥spinH →* AddMonoid.End (Fin 8 → ZMod 2) where
  toFun h :=
    { toFun := fun u => fcoord (Multiplicative.toAdd
        ((h : MulAut SpinW) (Multiplicative.ofAdd (fvec u))))
      map_zero' := by
        have h0 : fvec (0 : Fin 8 → ZMod 2) = 0 := by
          simp only [fvec, Pi.zero_apply]
          rw [show (![0, 0, 0] : Fin 3 → ZMod 2) = 0 from by
            funext j; fin_cases j <;> rfl, frameVec_zero]
        rw [h0, ofAdd_zero, map_one, toAdd_one, sixteenC8H1Coords_fcoord_zero]
      map_add' := by
        intro u u'
        rw [fvec_add, ofAdd_add, map_mul, toAdd_mul, fcoord_add] }
  map_one' := by
    apply AddMonoidHom.ext
    intro u
    show fcoord (Multiplicative.toAdd (((1 : ↥spinH) : MulAut SpinW)
      (Multiplicative.ofAdd (fvec u)))) = u
    rw [show ((1 : ↥spinH) : MulAut SpinW) = 1 from rfl, MulAut.one_apply, toAdd_ofAdd,
      fcoord_fvec]
  map_mul' h h' := by
    apply AddMonoidHom.ext
    intro u
    show fcoord (Multiplicative.toAdd (((h * h' : ↥spinH) : MulAut SpinW)
        (Multiplicative.ofAdd (fvec u)))) =
      fcoord (Multiplicative.toAdd ((h : MulAut SpinW) (Multiplicative.ofAdd
        (fvec (fcoord (Multiplicative.toAdd ((h' : MulAut SpinW)
          (Multiplicative.ofAdd (fvec u)))))))))
    rw [show ((h * h' : ↥spinH) : MulAut SpinW) = (h : MulAut SpinW) * (h' : MulAut SpinW)
        from rfl,
      MulAut.mul_apply, fvec_fcoord, ofAdd_toAdd]

theorem spinMu_apply (h : ↥spinH) (u : Fin 8 → ZMod 2) :
    spinMu h u = fcoord (Multiplicative.toAdd
      ((h : MulAut SpinW) (Multiplicative.ofAdd (fvec u)))) :=
  rfl

theorem spinMu_injective : Function.Injective spinMu := by
  intro h h' hh
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  change (h : MulAut SpinW) w = (h' : MulAut SpinW) w
  have hf : ∀ u, spinMu h u = spinMu h' u := fun u =>
    congrArg (fun f : AddMonoid.End (Fin 8 → ZMod 2) => f u) hh
  have hfw := hf (fcoord (Multiplicative.toAdd w))
  rw [spinMu_apply, spinMu_apply, fvec_fcoord, ofAdd_toAdd] at hfw
  have hinj : Function.Injective fcoord := fun a b hab => by
    rw [← fvec_fcoord a, ← fvec_fcoord b, hab]
  have h3 : Multiplicative.toAdd ((h : MulAut SpinW) w) =
      Multiplicative.toAdd ((h' : MulAut SpinW) w) := hinj hfw
  have h4 := congrArg Multiplicative.ofAdd h3
  simpa using h4

@[expose] noncomputable def sEH (c m : Fin 3 → ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : ↥spinH :=
  ⟨spinHom (sE c m g), Subgroup.mem_map_of_mem spinHom (sE_mem c m g)⟩

@[expose] def stabMat (c m : Fin 3 → ZMod 2) (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  let a := CFSG.LieType.SpinGeom.altMat (ZMod 2) m * g
  let i := g.adjugate
  !![1, (gᵀ *ᵥ c) 0, (gᵀ *ᵥ c) 1, (gᵀ *ᵥ c) 2, (i *ᵥ m) 0, (i *ᵥ m) 1, (i *ᵥ m) 2, c ⬝ᵥ m;
    0, g 0 0, g 0 1, g 0 2, 0, 0, 0, m 0;
    0, g 1 0, g 1 1, g 1 2, 0, 0, 0, m 1;
    0, g 2 0, g 2 1, g 2 2, 0, 0, 0, m 2;
    0, a 0 0, a 0 1, a 0 2, i 0 0, i 1 0, i 2 0, c 0;
    0, a 1 0, a 1 1, a 1 2, i 0 1, i 1 1, i 2 1, c 1;
    0, a 2 0, a 2 1, a 2 2, i 0 2, i 1 2, i 2 2, c 2;
    0, 0, 0, 0, 0, 0, 0, 1]

private theorem sixteenC8H1Coords_dot_mulVec (c x : Fin 3 → ZMod 2)
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    c ⬝ᵥ (g *ᵥ x) = (gᵀ *ᵥ c) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

private theorem sixteenC8H1Coords_dot_adjugate_transpose (m y : Fin 3 → ZMod 2)
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) = (g.adjugate *ᵥ m) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem spinMu_sEH (c m : Fin 3 → ZMod 2) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (u : Fin 8 → ZMod 2) :
    spinMu (sEH c m g) u = stabMat c m (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u := by
  rw [spinMu_apply]
  rw [show ((sEH c m g : ↥spinH) : MulAut SpinW) = spinHom (sE c m g) from rfl, spinHom_apply]
  simp only [toAdd_ofAdd]
  rw [sE_act c m g (fvec u)]
  rw [show fvec u = frameVec (ZMod 2) (u 0) ![u 1, u 2, u 3] ![u 4, u 5, u 6] (u 7) from rfl]
  rw [spinElt_frameVec, sixteenC8H1Coords_fcoord_frameVec]
  rw [sixteenC8H1Coords_dot_mulVec, sixteenC8H1Coords_dot_adjugate_transpose]
  funext i
  fin_cases i <;>
    simp [stabMat, Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.transpose_apply, Matrix.mulVec_mulVec, Pi.smul_apply,
      smul_eq_mul] <;>
    ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
