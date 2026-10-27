module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane

variable {n r ε p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def splitEntries (ζ : K) (t : Fin r → ZMod p) : HypIndex r ε → K
  | .inl i => ζ ^ (t i).val
  | .inr (.inl _) => 1
  | .inr (.inr i) => (ζ ^ (t i).val)⁻¹

@[expose] def IsSplitTorus (h : UnitaryFieldData 2 n K) (ζ : K)
    (τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε) : Prop :=
  ∀ t : Fin r → ZMod p, (((τ (Multiplicative.ofAdd t) : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (splitEntries ζ t)

@[expose] def IsHypBlockOn (T : Set (HypIndex r ε)) (M : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    Prop :=
  ∀ a b, (a ∉ T ∨ b ∉ T) → M a b = (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) a b

section Block

variable {T : Set (HypIndex r ε)} {M N : Matrix (HypIndex r ε) (HypIndex r ε) K}

theorem IsHypBlockOn.one : IsHypBlockOn T (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  fun _ _ _ => rfl

theorem IsHypBlockOn.mul_apply_left (hM : IsHypBlockOn T M) {a : HypIndex r ε} (ha : a ∉ T)
    (b : HypIndex r ε) : (M * N) a b = N a b := by
  have h1 : (M * N) a b = ((1 : Matrix (HypIndex r ε) (HypIndex r ε) K) * N) a b := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [hM a c (Or.inl ha)]
  rw [h1, Matrix.one_mul]

theorem IsHypBlockOn.mul_apply_right (hN : IsHypBlockOn T N) (a : HypIndex r ε)
    {b : HypIndex r ε} (hb : b ∉ T) : (M * N) a b = M a b := by
  have h1 : (M * N) a b = (M * (1 : Matrix (HypIndex r ε) (HypIndex r ε) K)) a b := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [hN c b (Or.inr hb)]
  rw [h1, Matrix.mul_one]

theorem IsHypBlockOn.mul (hM : IsHypBlockOn T M) (hN : IsHypBlockOn T N) :
    IsHypBlockOn T (M * N) := by
  rintro a b (ha | hb)
  · rw [hM.mul_apply_left (N := N) ha, hN a b (Or.inl ha)]
  · rw [hN.mul_apply_right (M := M) a hb, hM a b (Or.inr hb)]

theorem IsHypBlockOn.of_inv (hM : IsHypBlockOn T M) (h1 : M * N = 1) (h2 : N * M = 1) :
    IsHypBlockOn T N := by
  rintro a b (ha | hb)
  · rw [← hM.mul_apply_left (N := N) ha, h1]
  · rw [← hM.mul_apply_right (M := N) a hb, h2]

end Block

@[expose] def hypBlock (h : UnitaryFieldData 2 n K) (T : Set (HypIndex r ε)) :
    Subgroup (hypSU h r ε) where
  carrier := {g | IsHypBlockOn T (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K)}
  one_mem' := IsHypBlockOn.one
  mul_mem' {g g'} hg hg' := by
    change IsHypBlockOn T ((((g : GL (HypIndex r ε) K) * g' : GL (HypIndex r ε) K)) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [Units.val_mul]
    exact IsHypBlockOn.mul hg hg'
  inv_mem' {g} hg := by
    change IsHypBlockOn T ((((g : GL (HypIndex r ε) K))⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)
    refine IsHypBlockOn.of_inv hg ?_ ?_
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem mem_hypBlock {h : UnitaryFieldData 2 n K} {T : Set (HypIndex r ε)} {g : hypSU h r ε} :
    g ∈ hypBlock h T ↔ IsHypBlockOn T (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  Iff.rfl

@[expose] def lineCoords (m : Fin r) : Set (HypIndex r ε) :=
  {a | a = .inl m ∨ (∃ k, a = .inr (.inl k)) ∨ a = .inr (.inr m)}

@[expose] def lineBlock (h : UnitaryFieldData 2 n K) (m : Fin r) : Subgroup (hypSU h r ε) :=
  hypBlock h (lineCoords m)

@[expose] noncomputable def pairBlock (h : UnitaryFieldData 2 n K) (ε : ℕ) (i j : Fin r) :
    Subgroup (hypSU h r ε) :=
  (coordBlockSL K ({i, j} : Finset (Fin r))).map (leviSU h ε)

theorem one_mem_traceZero (h : UnitaryFieldData 2 n K) : (1 : K) ∈ h.traceZero := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
  exact CharTwo.add_self_eq_zero 1

@[expose] noncomputable def lineWeyl (h : UnitaryFieldData 2 n K) (ε : ℕ) (m : Fin r) :
    hypSU h r ε :=
  weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl {m})

@[expose] noncomputable def pairWeyl (h : UnitaryFieldData 2 n K) (ε : ℕ) (i j : Fin r) :
    hypSU h r ε :=
  weylElt h (one_mem_traceZero h) one_ne_zero (sumCongr_mem_hypWeyl (Equiv.swap i j))

@[expose] def torusFix {H : Type} [Group H] {s : ℕ} (τ : Multiplicative (Fin s → ZMod p) →* H)
    (f : (Fin s → ZMod p) → Fin s → ZMod p) : Set H :=
  τ '' {t | f (Multiplicative.toAdd t) = Multiplicative.toAdd t}

@[expose] def IsCoverTorusModel {H L' : Type} [Group H] [Group L'] (φ : H →* L') {s : ℕ}
    (τ : Multiplicative (Fin s → ZMod p) →* H) (A : Subgroup (MulAut L')) : Prop :=
  ∀ a : MulAut L', a ∈ A ↔ ∃ t, a = MulAut.conj (φ (τ t))

end CFSG.StandardType.SuSplitRootGen

end
