module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount

namespace CFSG
end CFSG
open CFSG

/-!
# Transporting the `A₇` involution count
-/

namespace CFSG.GorensteinWalter

universe u

/-- Any finite group isomorphic to `A₇` has exactly `105` involutions. -/
public theorem involutions_card_eq_105_of_mulEquiv_aSeven
    {G : Type u} [Group G] [Finite G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 7))) :
    Nat.card {x : G // IsInvolution x} = 105 := by
  let f : G ≃* alternatingGroup (Fin 7) := e.some
  let ef : {x : G // IsInvolution x} ≃
      {y : alternatingGroup (Fin 7) // IsInvolution y} :=
    { toFun := fun x =>
        ⟨f x.1, by
          constructor
          · intro h1
            apply x.2.1
            apply f.injective
            simpa using h1
          · simpa [map_pow] using congrArg f x.2.2⟩
      invFun := fun y =>
        ⟨f.symm y.1, by
          constructor
          · intro h1
            apply y.2.1
            apply f.symm.injective
            simpa using h1
          · simpa [map_pow] using congrArg f.symm y.2.2⟩
      left_inv := by intro x; apply Subtype.ext; simp [f]
      right_inv := by intro y; apply Subtype.ext; simp [f] }
  calc
    Nat.card {x : G // IsInvolution x} =
        Nat.card {y : alternatingGroup (Fin 7) // IsInvolution y} :=
      Nat.card_congr ef
    _ = 105 := aSeven_involutions_card

end CFSG.GorensteinWalter
