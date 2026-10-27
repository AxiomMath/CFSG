module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def OutAbelian (L : Type) [Group L] : Prop :=
  ∀ φ ψ : MulAut L, ⁅φ, ψ⁆ ∈ (MulAut.conj : L →* MulAut L).range

@[expose] def AsB42Ident : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → ∀ A, IsFFStarOffender G A →
      (B42Case5 G A ∨ ffJ G ≠ L) →
      ffJ G ≠ L ∧ G = ffJ G ∧ L = ⁅G, G⁆ ∧
        ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥G ≃* Equiv.Perm (Fin n))) ∨
          ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
            Nonempty (↥G ≃* ↥(CFSG.Open.quasithinG2 K)))

@[expose] def AsSp4S6 : Prop :=
  ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V),
    BinaryNaturalSp4 H U Z 1 → SymmetricNatural H U Z 6

@[expose] def AsS8D8 : Prop :=
  ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V),
    Nonempty (↥H ≃* Equiv.Perm (Fin 8)) → SLExteriorTwo ⁅H, H⁆ U Z 4 →
    (∀ h ∈ H, ∀ u ∈ U, h u ∈ U) → (∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) → SymmetricNatural H U Z 8

@[expose] def AsOutAbelian : Prop :=
  ∀ (V : Type) [CommGroup V] (M : Subgroup (MulAut V)),
    ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥M ≃* Equiv.Perm (Fin n))) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
        Nonempty (↥M ≃* ↥(CFSG.Open.quasithinG2 K))) →
    OutAbelian ↥⁅M, M⁆

@[expose] def AsI16Cover : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ L : Subgroup (MulAut V),
    commV L ∈ IrrPlus L ⊤ →
      ((∃ n, 1 < n ∧ BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 n) ∨
        BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 4 1 ∨
        BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 5 1) →
      fixV L ⊓ commV L = ⊥

@[expose] def AsB51NonsplitOff : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L T : Subgroup (MulAut V), B51Hyp G L → commV L ∈ IrrPlus L ⊤ → IsSylowTwoOf T G →
      fixV L ⊓ commV L ≠ ⊥ →
      (BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1 ∨
        ∃ n, BinaryNaturalSp4 L (commV L) (fixV L ⊓ commV L) n) →
      ∀ A, IsFFStarOffenderOn T A (commV L) → A ≤ L

end CFSG.Quasithin
