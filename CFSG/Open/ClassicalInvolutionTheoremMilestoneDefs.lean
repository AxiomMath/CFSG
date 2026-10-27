module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.Defs

public section

namespace CFSG.Open
open CFSG.Open

open scoped MatrixGroups

@[expose] def classicalInvolutionOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance classicalInvolutionOddCore_normal (H : Type*) [Group H] :
    (classicalInvolutionOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def classicalInvolutionM12 : Subgroup (Equiv.Perm (Fin 12)) :=
  CFSG.Blueprint.NativeSporadic.M12

@[expose] def classicalInvolutionWitness {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
    Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, GaloisField p n))) ∨
  (IsQuasisimple (J ⧸ classicalInvolutionOddCore J) ∧
    Nat.card (Subgroup.center (J ⧸ classicalInvolutionOddCore J)) = 2 ∧
    Nonempty ((J ⧸ classicalInvolutionOddCore J) ⧸
        Subgroup.center (J ⧸ classicalInvolutionOddCore J) ≃* alternatingGroup (Fin 7)))

@[expose] def classicalInvolutionTightlyEmbedded {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (J : Set G) →
    Odd (Nat.card (J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G))

end CFSG.Open
