module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCover

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.PerfectOddCover

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

theorem perfect_odd_cover_linear
    {k : Type} [Field k] [Finite k] (f : ℕ) (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) {L : Type u} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* PSL2MatrixGroup k) (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card η.ker)) :
    η.ker = ⊥ ∧ ∃ e : L ≃* PSL2MatrixGroup k, ∀ x, e x = η x := by
  let e : PSL2MatrixGroup k ≃* PSL2BinaryMatrixGroup f :=
    pslFieldEquiv (binaryFieldEquiv f (by omega) hk)
  have : Finite (PSL2MatrixGroup k) := Finite.of_equiv _ e.symm.toEquiv
  exact perfect_odd_cover_exact_isomorphism η hη hcen hodd
    (lemma114_psl2_oddSylow_isCyclic_of_equiv hf e)

theorem perfect_odd_cover_linear_scalarQuotient
    {k : Type} [Field k] [Finite k] (f : ℕ)
    (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) {L : Type u} [Group L] [Finite L]
    [Group.IsPerfect L] (η : L →* GLAProj (GLASLGroup (Fin 2) k)) (hη : Function.Surjective η)
    (hcen : η.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card η.ker)) :
    η.ker = ⊥ ∧ ∃ e : L ≃* GLAProj (GLASLGroup (Fin 2) k), ∀ x, e x = η x := by
  let e : GLAProj (GLASLGroup (Fin 2) k) ≃* PSL2BinaryMatrixGroup f := glaSL2EquivNative f hf hk
  have : Finite (GLAProj (GLASLGroup (Fin 2) k)) := Finite.of_equiv _ e.symm.toEquiv
  exact perfect_odd_cover_exact_isomorphism η hη hcen hodd
    (lemma114_psl2_oddSylow_isCyclic_of_equiv hf e)

end CFSG.ShultStronglyClosedTI.PerfectOddCover
