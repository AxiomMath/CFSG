module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transport of a semilinear conjugation equation

Conjugating a semilinear fixed-point equation by `g` changes the projective
coefficient to `g * z * σ̃(g)⁻¹`.  This is the small algebraic bridge used when
moving an abstract PSL₂ torus to a concrete split or nonsplit model.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- Transport `z · σ̃(x) · z⁻¹ = x` through projective conjugation by `g`. -/
public theorem pgl2_semilinear_conjugate_transport
    {K : Type u} [Field K]
    (sigma : K ≃+* K) (g z x : PGL2 K)
    (h : z * pgl2FieldAut K sigma x * z⁻¹ = x) :
    let z' := g * z * (pgl2FieldAut K sigma g)⁻¹
    z' * pgl2FieldAut K sigma (g * x * g⁻¹) * z'⁻¹ = g * x * g⁻¹ := by
  dsimp
  simp only [map_mul, map_inv]
  group
  have h' : z * pgl2FieldAut K sigma x * z ^ (-(1 : ℤ)) = x := by
    simpa [zpow_neg] using h
  calc
    g * z * pgl2FieldAut K sigma x * z ^ (-(1 : ℤ)) * g ^ (-(1 : ℤ)) =
        g * (z * pgl2FieldAut K sigma x * z ^ (-(1 : ℤ))) *
          g ^ (-(1 : ℤ)) := by group
    _ = g * x * g ^ (-(1 : ℤ)) := by rw [h']

end CFSG.GorensteinWalter
