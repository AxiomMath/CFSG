module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Two-subgroups of an odd-field semilinear layer are projective-linear

If the field-automorphism image of a semilinear subgroup has odd order, its
Sylow `2`-subgroups lie in the canonical `PGL₂` layer.  This is the finite
index argument used when transferring the Section-4 ambient Sylow to the
`PGL₂` model.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- A Sylow `2`-subgroup of a subgroup of `PΓL₂(K)` with odd field image is
contained in the canonical `PGL₂(K)` layer. -/
public theorem pGammaL2_sylow_two_le_pgl_range
    (K : Type u) [Field K] [Finite K]
    (A : Subgroup (PGammaL2 K))
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range))
    (P : Sylow 2 A) :
    (P : Subgroup A).map A.subtype ≤ pGammaL2PGLRange K := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  letI : Finite A := inferInstance
  let L : Subgroup A := pGammaL2LinearKernel K A
  have hLnormal : L.Normal := inferInstance
  have hLindex : Odd L.index :=
    pGammaL2LinearKernel_index_odd K A hodd
  have hPleL : (P : Subgroup A) ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex
      (P : Subgroup A) P.isPGroup'
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
  have hpL : p ∈ L := hPleL hp
  change (A.subtype p : PGammaL2 K) ∈ pGammaL2PGLRange K
  rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
  have hpL' : pGammaL2FieldProjection K A p = 1 :=
    (mem_pGammaL2LinearKernel_iff K A p).mp hpL
  simpa [pGammaL2FieldProjection] using hpL'

end CFSG.GorensteinWalter
