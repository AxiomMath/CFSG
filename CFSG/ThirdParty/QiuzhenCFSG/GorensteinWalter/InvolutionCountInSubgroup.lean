module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountOfFusion

namespace CFSG
end CFSG
open CFSG

/-!
# Counting involutions inside a subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If all involutions of a finite subgroup `M` are conjugate inside `M` to
`t`, then the ambient subtype of involutions in `M` has cardinality equal to
the index of `C_M(t)`. -/
public theorem involutions_in_subgroup_card_eq_centralizer_index
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (t : G) (htM : t ∈ M) (ht : IsInvolution t)
    (hfuse : ∀ x : M, IsInvolution x →
      ∃ g : M, g * x * g⁻¹ = ⟨t, htM⟩) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ M} =
      (Subgroup.centralizer
        ({⟨t, htM⟩} : Set M)).index := by
  classical
  let tM : M := ⟨t, htM⟩
  have htM_inv : IsInvolution tM := by
    constructor
    · intro h1
      apply ht.1
      simpa [tM] using congrArg Subtype.val h1
    · simpa [tM, pow_two] using ht.2
  have hfuse' : ∀ x : M, IsInvolution x →
      ∃ g : M, g * x * g⁻¹ = tM := by
    intro x hx
    simpa [tM] using hfuse x hx
  have hsub := involutions_card_eq_centralizer_index_of_fusion
    tM htM_inv hfuse'
  let eI : {x : G // IsInvolution x ∧ x ∈ M} ≃
      {x : M // IsInvolution x} :=
    { toFun := fun x =>
        ⟨⟨x.1, x.2.2⟩, by
          have hxI : IsInvolution (x.1 : G) := x.2.1
          constructor
          · intro h1
            apply hxI.1
            simpa using congrArg Subtype.val h1
          · simpa [pow_two] using hxI.2⟩
      invFun := fun x =>
        ⟨x.1, by
          have hxI : IsInvolution (x.1 : G) := by
            constructor
            · intro h1
              apply x.2.1
              apply Subtype.ext
              simpa using h1
            · simpa [pow_two] using congrArg Subtype.val x.2.2
          constructor
          · intro h1
            apply hxI.1
            exact h1
          · simpa [pow_two] using hxI.2, x.1.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  simpa [tM] using (Nat.card_congr eI).trans hsub

end CFSG.GorensteinWalter
