module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace F1

instance instNormalPCoreTwo (H : Type*) [Group H] : (pCore 2 H).Normal := pCore_normal 2

end F1

abbrev oTwoQuot (H : Type*) [Group H] : Type _ := H ⧸ pCore 2 H

@[expose] def IsRankOneListed (K : Type*) [Group K] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* PSL(2, GaloisField 2 n))) ∨
  (∃ a : ℕ, Nonempty (K ≃* Sz a)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    Nonempty (K ≃* StatedSU 3 (2 ^ n) F)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    Nonempty (K ≃* StatedProj (StatedSU 3 (2 ^ n) F))) ∨
  Nonempty (K ≃* DihedralGroup 5)

theorem IsRankOneListed.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : IsRankOneListed K) : IsRankOneListed K' := by
  rcases h with h | h | h | h | h
  · obtain ⟨n, hn, ⟨f⟩⟩ := h
    exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · obtain ⟨a, ⟨f⟩⟩ := h
    exact Or.inr (Or.inl ⟨a, ⟨e.symm.trans f⟩⟩)
  · obtain ⟨n, hn, F, i1, i2, hF, ⟨f⟩⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨n, hn, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩))
  · obtain ⟨n, hn, F, i1, i2, hF, ⟨f⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, F, i1, i2, hF, ⟨e.symm.trans f⟩⟩)))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩)))

end CFSG.Quasithin
