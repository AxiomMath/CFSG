module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {V : Type*} [CommGroup V]

@[expose] def IsModel82e (H : Subgroup (MulAut V)) (e : ℕ) : Prop :=
  BinaryNineTensor H ⊤ ⊥ 1 ∧ e = 4 ∨ MathieuCode22 H ⊤ ⊥ ∧ e = 4 ∨
    MathieuCocode24 H ⊤ ⊥ ∧ e = 6

@[expose] def IsSylowVec82 (H : Subgroup (MulAut V)) (z : V) : Prop :=
  ∃ S : Subgroup (MulAut V), S ≤ H ∧ Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2 ∧
    z ∈ fixV S

@[expose] def parz82 (H : Subgroup (MulAut V)) (z : V) : Subgroup (MulAut V) :=
  perfectCore (H ⊓ centSub (Subgroup.zpowers z))

@[expose] def radz82 (H : Subgroup (MulAut V)) (z : V) : Subgroup (MulAut V) :=
  pCoreOf 2 (parz82 H z)

@[expose] def vz82 (H : Subgroup (MulAut V)) (z : V) : Subgroup V := commV (radz82 H z)

@[expose] def HZ82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (e : ℕ) (z : V),
    IsModel82e H e → z ≠ 1 → IsSylowVec82 H z →
      Nat.card ↥(vz82 H z) = 2 ^ (e + 1) ∧ Nat.card ↥(radz82 H z) = 2 ^ e ∧
      ⁅radz82 H z, parz82 H z⁆ = radz82 H z ∧
      (∀ N : Subgroup (MulAut V), N ≤ radz82 H z → N ≠ ⊥ →
        parz82 H z ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = radz82 H z) ∧
      (∀ Y : Subgroup V, Subgroup.zpowers z < Y → Y ≤ vz82 H z → parz82 H z ≤ stabSub Y →
        Y = vz82 H z) ∧
      vz82 H z ⊓ fixV (radz82 H z) = Subgroup.zpowers z ∧
      commV (parz82 H z) = ⊤

@[expose] def HB82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)) (z : V),
    (BinaryNineTensor H ⊤ ⊥ 1 ∧ Nat.card ↥X = 2 ^ 4 ∧ Nat.card ↥(fixV X) = 2 ^ 4 ∨
      MathieuCode22 H ⊤ ⊥ ∧ Nat.card ↥X = 2 ^ 5 ∧ Nat.card ↥(fixV X) = 2 ^ 4 ∨
      MathieuCocode24 H ⊤ ⊥ ∧ Nat.card ↥X = 2 ^ 6 ∧ Nat.card ↥(fixV X) = 2 ^ 3) →
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian 2 X → z ≠ 1 →
    (∃ S : Subgroup (MulAut V), S ≤ H ⊓ stabSub (fixV X) ∧
      Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2 ∧ z ∈ fixV S) →
      vz82 H z ≤ commV (perfectCore (H ⊓ stabSub (fixV X))) ∧ ¬ vz82 H z ≤ fixV X

@[expose] def HCoc82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (e : ℕ) (z : V),
    IsModel82e H e → z ≠ 1 → IsSylowVec82 H z →
    ∀ δ : MulAut V → V, (∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k)) →
      (∀ r ∈ radz82 H z, δ r ∈ Subgroup.zpowers z) →
      ∃ w ∈ vz82 H z, ∀ g ∈ H, δ g = w * (g w)⁻¹

@[expose] def HFus82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V),
    MathieuCocode24 H ⊤ ⊥ → z ≠ 1 → IsSylowVec82 H z →
      ∃ φ ∈ H, φ z ≠ z ∧ φ z ∈ vz82 H z

end CFSG.Quasithin.H13
