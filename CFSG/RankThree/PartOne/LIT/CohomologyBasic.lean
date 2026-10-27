module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix Module

theorem additive_eq_mul {p : ℕ} [Fact p.Prime] (c : ZMod p → ZMod p)
    (h : ∀ s r, c (s + r) = c s + c r) (s : ZMod p) : c s = s * c 1 := by
  let f : ZMod p →+ ZMod p := AddMonoidHom.mk' c h
  have h1 : f ((s.val : ℕ) • (1 : ZMod p)) = (s.val : ℕ) • f 1 := map_nsmul f _ _
  have e : ((s.val : ℕ) • (1 : ZMod p)) = s := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [e] at h1
  rw [show c s = f s from rfl, h1, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rfl

theorem exists_fixed_vector_of_index {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (B : Submodule K V)
    (hq : ∀ g v, ρ g v - v ∈ B) (H : Subgroup G) (hH : (H.index : K) ≠ 0)
    {v₁ : V} (hv₁ : ∀ h ∈ H, ρ h v₁ = v₁) :
    ∃ v : V, v - v₁ ∈ B ∧ ∀ g, ρ g v = v := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let W : G ⧸ H → V := Quotient.lift (fun g : G => ρ g v₁) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    show ρ a v₁ = ρ b v₁
    have : b = a * (a⁻¹ * b) := by group
    rw [this, map_mul]
    show ρ a v₁ = ρ a (ρ (a⁻¹ * b) v₁)
    rw [hv₁ _ hab'])
  have hW : ∀ g : G, W (g : G ⧸ H) = ρ g v₁ := fun g => rfl
  refine ⟨(H.index : K)⁻¹ • ∑ x : G ⧸ H, W x, ?_, ?_⟩
  ·
    have hc : Fintype.card (G ⧸ H) = H.index := by
      rw [Nat.card_eq_fintype_card.symm]; rfl
    have h2 : (H.index : K)⁻¹ • (Fintype.card (G ⧸ H) • v₁) = v₁ := by
      rw [hc, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hH, one_smul]
    have h1 : (H.index : K)⁻¹ • ∑ x : G ⧸ H, W x - v₁ =
        (H.index : K)⁻¹ • ∑ x : G ⧸ H, (W x - v₁) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, h2]
    rw [h1]
    refine B.smul_mem _ (B.sum_mem fun x _ => ?_)
    induction x using Quotient.inductionOn with
    | h g => exact hq g v₁
  · intro g
    rw [map_smul, map_sum]
    congr 1
    have hshift : ∀ x : G ⧸ H, ρ g (W x) = W (g • x) := by
      intro x
      induction x using Quotient.inductionOn with
      | h a =>
        show ρ g (ρ a v₁) = W (((g * a : G)) : G ⧸ H)
        rw [hW, map_mul]
        rfl
    simp_rw [hshift]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun x => rfl)

end CFSG.RankThree.PartOne.LIT
