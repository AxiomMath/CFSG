module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

namespace CFSG
end CFSG
open CFSG

/-!
# Fusion of inner involutions in odd PGL₂

The derived subgroup of odd `PGL₂(K)` is `PSL₂(K)`.  Therefore the unique
involution class in odd `PSL₂(K)` gives fusion of all involutions lying in
the derived subgroup, with a conjugator in that subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- For an odd finite field of order greater than three, two involutions in
`PGL₂(K)'` are conjugate by an element of `PGL₂(K)'`. -/
public theorem pgl2_inner_involutions_conjugate
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {x y : PGL2 K}
    (hxJ : x ∈ commutator (PGL2 K)) (hxI : IsInvolution x)
    (hyJ : y ∈ commutator (PGL2 K)) (hyI : IsInvolution y) :
    ∃ g : PGL2 K, g ∈ commutator (PGL2 K) ∧ g * x * g⁻¹ = y := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let eJ : J ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK hcard (MulEquiv.refl (PGL2 K))).some
  let xJ : J := ⟨x, hxJ⟩
  let yJ : J := ⟨y, hyJ⟩
  have hxI' : IsInvolution (eJ xJ) := by
    constructor
    · intro h
      apply hxI.1
      have hxJ1 : xJ = 1 := eJ.injective (by simpa using h)
      exact congrArg Subtype.val hxJ1
    · have hxJpow : xJ ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hxI.2
      change (eJ xJ) ^ 2 = 1
      simpa using congrArg eJ hxJpow
  have hyI' : IsInvolution (eJ yJ) := by
    constructor
    · intro h
      apply hyI.1
      have hyJ1 : yJ = 1 := eJ.injective (by simpa using h)
      exact congrArg Subtype.val hyJ1
    · have hyJpow : yJ ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hyI.2
      change (eJ yJ) ^ 2 = 1
      simpa using congrArg eJ hyJpow
  obtain ⟨g, hg⟩ :=
    psl2_involutions_conjugate_of_odd_prime_power K hK
      (eJ xJ) (eJ yJ) hxI' hyI'
  refine ⟨(eJ.symm g : PGL2 K), (eJ.symm g : J).2, ?_⟩
  have hg' : (eJ.symm g : J) * xJ * (eJ.symm g : J)⁻¹ = yJ := by
    apply eJ.injective
    change eJ ((eJ.symm g : J) * xJ * (eJ.symm g : J)⁻¹) = eJ yJ
    simpa using hg
  exact congrArg Subtype.val hg'

end CFSG.GorensteinWalter
