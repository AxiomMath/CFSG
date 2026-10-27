module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The canonical `PSL₂` layer is self-centralizing in `PΓL₂`

The semilinear action on `PSL₂` is faithful.  This turns the elementary
centralizer calculation into a reusable subgroup endpoint.
-/

noncomputable section

open Matrix

namespace CFSG.GorensteinWalter

universe u

private theorem pGammaL2_action_eq_of_commuting_psl
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (x : PGammaL2 K)
    (hx : x ∈ Subgroup.centralizer
      (pGammaL2PSLRange K : Set (PGammaL2 K)))
    (y : PSL2 K) :
    pGammaL2ToMulAutPSL2 K hK hcard x y = y := by
  let z : PGammaL2 K := SemidirectProduct.inl
    (Matrix.ProjectiveSpecialLinearGroup.toPGL y)
  have hcomm : x * z = z * x := by
    exact ((Subgroup.mem_centralizer_iff.mp hx) z (by
      exact mem_pGammaL2PSLRange_iff K z |>.2 ⟨y, rfl⟩)).symm
  have hleft := congrArg (fun a : PGammaL2 K => a.left) hcomm
  have hleft' : x.left * (pgl2FieldAut K x.right)
      (Matrix.ProjectiveSpecialLinearGroup.toPGL y) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL y * x.left := by
    change (x * z).left = (z * x).left at hleft
    rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at hleft
    simpa [z] using hleft
  have hxdec := SemidirectProduct.inl_left_mul_inr_right x
  change (pGammaL2ToMulAutPSL2 K hK hcard) x y = y
  rw [← hxdec, map_mul, pGammaL2ToMulAutPSL2_inl,
    pGammaL2ToMulAutPSL2_inr]
  change pgl2InnerAutPSL2 K hK hcard x.left
      (psl2FieldAut K x.right y) = y
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply, psl2FieldAut_toPGL]
  calc
    x.left * (pgl2FieldAut K x.right)
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y) * x.left⁻¹ =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y * x.left) * x.left⁻¹ := by
          rw [hleft']
    _ = Matrix.ProjectiveSpecialLinearGroup.toPGL y := by group

/-- The canonical `PSL₂(K)` subgroup has trivial centralizer in
`PΓL₂(K)` for `|K| > 3`. -/
public theorem pGammaL2_pslRange_centralizer_eq_bot
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Subgroup.centralizer
      (pGammaL2PSLRange K : Set (PGammaL2 K)) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hact : pGammaL2ToMulAutPSL2 K hK hcard x = 1 := by
    ext y
    exact pGammaL2_action_eq_of_commuting_psl K hK hcard x hx y
  exact pGammaL2ToMulAutPSL2_injective K hK hcard (by simpa using hact)

end CFSG.GorensteinWalter
