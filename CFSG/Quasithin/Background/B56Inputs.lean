module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section B56Lemmas

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B56Cases (G : Subgroup (MulAut V)) : Prop :=
  B56Case1 G ∨ B56Case2 G ∨ B56Case3 G ∨ B56Case4 G ∨ B56Case5 G

structure B56Counterex (G : Subgroup (MulAut V)) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  ne_bot : G ≠ ⊥
  hyp : B53Hyp G
  not_cases : ¬ B56Cases G
  minimal : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
    ∀ G' : Subgroup (MulAut V'), G' ≠ ⊥ → B53Hyp G' → Nat.card ↥G' < Nat.card ↥G → B56Cases G'

@[expose] def B482Module (L : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  Nat.card ↥W = 2 ^ 4 ∧ BinaryNaturalSL L W (fixV L ⊓ W) 3 1 ∧
    ¬ ∃ A' B' : Subgroup V, ⊥ < A' ∧ ⊥ < B' ∧ XMod.IsInv ↥L A' ∧ XMod.IsInv ↥L B' ∧
      A' ⊔ B' = W ∧ A' ⊓ B' = ⊥

@[expose] def B59Case1 (A L : Subgroup (MulAut V)) : Prop :=
  (∃ n, BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n) ∧ IsSylowTwoOf A L ∧
    commV L ⊔ fixV A = ⊤

@[expose] def B59Case2 (A L : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥(L ⊔ A) ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥A = 2 ∧
    SymmetricNatural (L ⊔ A) (commV L) ⊥ 5 ∧ commV L ⊔ fixV A = ⊤

@[expose] def B59Case3 (A L : Subgroup (MulAut V)) : Prop :=
  (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Odd m ∧ Nat.card K = 2 ^ m ∧
    DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 K)) 2) ∧ A ≤ L ∧ commV L ⊔ fixV A = ⊤

@[expose] def B59Case4 (A L : Subgroup (MulAut V)) : Prop :=
  (∃ m, Odd m ∧ BinaryNaturalSL L (commV L) ⊥ 3 m) ∧
    ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹

@[expose] def B59Case5 (A L : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2))) ∧ A ≤ L ∧ Nat.card ↥A = 4 ∧ B482Module L (commV L) ∧
    commV L ⊔ fixV A = ⊤

@[expose] def B59Conclusion (A L : Subgroup (MulAut V)) : Prop :=
  B59Case1 A L ∨ B59Case2 A L ∨ B59Case3 A L ∨ B59Case4 A L ∨ B59Case5 A L

end B56Lemmas

@[expose] def AsB58 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A, IsFFStarMin G A → A ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V))

@[expose] def AsB59 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L, IsFFStarMin G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L → B59Conclusion A L

@[expose] def AsB5610 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L, IsFFStarMin G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L → B59Conclusion A L → False

end CFSG.Quasithin
