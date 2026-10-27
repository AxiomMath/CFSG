module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def IsModel82 {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) : Prop :=
  BinaryNineTensor H ⊤ ⊥ 1 ∨ MathieuCode22 H ⊤ ⊥ ∨ MathieuCode24 H ⊤ ⊥ ∨ MathieuCocode24 H ⊤ ⊥

@[expose] def HSimple82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)), IsModel82 H →
    IsSimpleGroup ↥H ∧ ∃ a b : ↥H, a * b ≠ b * a

@[expose] def HCent82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)), IsModel82 H →
    Subgroup.centralizer (H : Set (MulAut V)) = ⊥

@[expose] def HType82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
    (BinaryNineTensor H ⊤ ⊥ 1 → IsPSL 3 2 2 ↥H) ∧
      (MathieuCode22 H ⊤ ⊥ → IsSporadic .M22 ↥H) ∧
      (MathieuCode24 H ⊤ ⊥ ∨ MathieuCocode24 H ⊤ ⊥ → IsSporadic .M24 ↥H)

@[expose] def HParab82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    (BinaryNineTensor H ⊤ ⊥ 1 ∧ Nat.card ↥X = 2 ^ 4 ∨ MathieuCode22 H ⊤ ⊥ ∧ Nat.card ↥X = 2 ^ 5) →
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian 2 X →
    Nat.card ↥(fixV X) = 2 ^ 4 →
      Nat.card ↥(perfectCore (H ⊓ stabSub (fixV X))) = 960 ∧
      pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))) ≤
        ⁅X, perfectCore (H ⊓ stabSub (fixV X))⁆ ∧
      (MathieuCode22 H ⊤ ⊥ → ∃ K : Subgroup (MulAut V),
        perfectCore (H ⊓ stabSub (fixV X)) ≤ K ∧ K ≤ H ∧ IsPSL 3 2 2 ↥K)

end CFSG.Quasithin.H13
