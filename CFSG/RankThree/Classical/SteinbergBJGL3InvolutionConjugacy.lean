module

public import CFSG.RankThree.Classical.SteinbergBJGL3AlternatingZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.Classical.GL3

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_one_of_ne_zero_zmod_two {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert a
  decide

omit [AddCommGroup W] [Module (ZMod 2) W] in
theorem basisInvolution_apply_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}
    (e : Module.Basis (Fin n) (ZMod 2) V) (f : Fin n → V)
    (hf : ∀ i, e.constr (ZMod 2) f (f i) = e i) (x : V) :
    basisInvolution e f hf (basisInvolution e f hf x) = x := by
  have h : (e.constr (ZMod 2) f) ∘ₗ (e.constr (ZMod 2) f) = LinearMap.id :=
    e.ext fun i => by rw [LinearMap.comp_apply, e.constr_basis, hf, LinearMap.id_apply]
  exact LinearMap.congr_fun h x

theorem exists_basis_of_involution (hW : Module.finrank (ZMod 2) W = 3)
    {α : W ≃ₗ[ZMod 2] W} (hα : orderOf α = 2) :
    ((α : W →ₗ[ZMod 2] W) - LinearMap.id) ∘ₗ ((α : W →ₗ[ZMod 2] W) - LinearMap.id) = 0 ∧
    Module.finrank (ZMod 2) (LinearMap.range ((α : W →ₗ[ZMod 2] W) - LinearMap.id)) = 1 ∧
    ∃ v : Module.Basis (Fin 3) (ZMod 2) W, α (v 0) = v 0 ∧ α (v 1) = v 1 ∧ α (v 2) = v 2 + v 1 := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  have hαα : ∀ x, α (α x) = x := fun x => by
    have h := pow_orderOf_eq_one α
    rw [hα, pow_two] at h
    exact DFunLike.congr_fun h x
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    exact absurd hα (by decide)
  set N : W →ₗ[ZMod 2] W := (α : W →ₗ[ZMod 2] W) - LinearMap.id with hNdef
  have hN : ∀ x, N x = α x - x := fun x => rfl
  have hNN : N ∘ₗ N = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hN, hN, map_sub, hαα, LinearMap.zero_apply]
    calc x - α x - (α x - x) = (x + x) - (α x + α x) := by abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_zero]
  have hrk : LinearMap.range N ≤ LinearMap.ker N := LinearMap.range_le_ker_iff.2 hNN
  have hsum := LinearMap.finrank_range_add_finrank_ker N
  have hle := Submodule.finrank_mono hrk
  have hN0 : N ≠ 0 := fun h => hα1 (LinearEquiv.ext fun x => by
    have := LinearMap.congr_fun h x
    rw [hN, LinearMap.zero_apply, sub_eq_zero] at this
    exact this)
  have hpos : Module.finrank (ZMod 2) (LinearMap.range N) ≠ 0 := fun h =>
    hN0 (LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h))
  have hr1 : Module.finrank (ZMod 2) (LinearMap.range N) = 1 := by omega
  have hk2 : Module.finrank (ZMod 2) (LinearMap.ker N) = 2 := by omega
  refine ⟨hNN, hr1, ?_⟩
  have hne : LinearMap.range N ≠ ⊥ := fun h => hpos (by rw [h, finrank_bot])
  obtain ⟨v₂, hv₂, hv₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v₃, hv₃⟩ := LinearMap.mem_range.1 hv₂
  have hv₂k : v₂ ∈ LinearMap.ker N := hrk hv₂
  have hspan : Submodule.span (ZMod 2) {v₂} < LinearMap.ker N := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hv₂k
    · rw [finrank_span_singleton hv₂0, hk2]
      omega
  obtain ⟨v₁, hv₁, hv₁s⟩ := IsConcreteLE.exists_of_lt hspan
  have hNv₁ : N v₁ = 0 := hv₁
  have hNv₂ : N v₂ = 0 := hv₂k
  have hli : LinearIndependent (ZMod 2) ![v₁, v₂, v₃] := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h2 : g 2 = 0 := by
      have h := congrArg N hg
      rw [map_add, map_add, map_smul, map_smul, map_smul, hNv₁, hNv₂, hv₃, smul_zero,
        smul_zero, zero_add, zero_add, map_zero, smul_eq_zero] at h
      exact h.resolve_right hv₂0
    rw [h2, zero_smul, add_zero] at hg
    have h0 : g 0 = 0 := by
      by_contra h0
      rw [eq_one_of_ne_zero_zmod_two h0, one_smul] at hg
      apply hv₁s
      rw [eq_neg_of_add_eq_zero_left hg]
      exact neg_mem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₂))
    rw [h0, zero_smul, zero_add, smul_eq_zero] at hg
    have h1 : g 1 = 0 := hg.resolve_right hv₂0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  set v := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hW])
  have hv : ∀ i, v i = ![v₁, v₂, v₃] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hv]
    exact (sub_eq_zero.1 hNv₁)
  · rw [hv]
    exact (sub_eq_zero.1 hNv₂)
  · rw [hv 2, hv 1]
    have h : α v₃ - v₃ = v₂ := hv₃
    change α v₃ = v₃ + v₂
    rw [← h, add_sub_cancel]

theorem gl3_two_involution_conjugacy (hW : Module.finrank (ZMod 2) W = 3) :
    (∀ α : W ≃ₗ[ZMod 2] W, orderOf α = 2 →
      ((α : W →ₗ[ZMod 2] W) - LinearMap.id) ∘ₗ ((α : W →ₗ[ZMod 2] W) - LinearMap.id) = 0 ∧
      Module.finrank (ZMod 2) (LinearMap.range ((α : W →ₗ[ZMod 2] W) - LinearMap.id)) = 1 ∧
      ∃ v : Module.Basis (Fin 3) (ZMod 2) W,
        α (v 0) = v 0 ∧ α (v 1) = v 1 ∧ α (v 2) = v 2 + v 1) ∧
    (∃ α : W ≃ₗ[ZMod 2] W, orderOf α = 2) ∧
    ∀ α β : W ≃ₗ[ZMod 2] W, orderOf α = 2 → orderOf β = 2 → IsConj α β := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  refine ⟨fun α hα => exists_basis_of_involution hW hα, ?_, fun α β hα hβ => ?_⟩
  ·
    set v := Module.finBasisOfFinrankEq (ZMod 2) W hW
    have hf : ∀ i, v.constr (ZMod 2) ![v 0, v 1, v 2 + v 1] (![v 0, v 1, v 2 + v 1] i) = v i := by
      intro i
      fin_cases i
      · simp [v.constr_basis]
      · simp [v.constr_basis]
      · simp only [Fin.reduceFinMk, Matrix.cons_val, map_add, v.constr_basis]
        rw [add_assoc, ZModModule.add_self, add_zero]
    have h2 := basisInvolution_apply_basis v _ hf 2
    have hinv := basisInvolution_apply_apply v _ hf
    refine ⟨basisInvolution v _ hf, orderOf_eq_prime ?_ fun h => ?_⟩
    · exact LinearEquiv.ext fun x => by rw [pow_two]; exact hinv x
    · rw [h] at h2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
      change v 2 = v 2 + v 1 at h2
      exact v.ne_zero 1 (by
        have h3 : v 2 + v 1 - v 2 = 0 := by rw [← h2, sub_self]
        rwa [add_sub_cancel_left] at h3)
  ·
    obtain ⟨-, -, v, hv0, hv1, hv2⟩ := exists_basis_of_involution hW hα
    obtain ⟨-, -, w, hw0, hw1, hw2⟩ := exists_basis_of_involution hW hβ
    set c : W ≃ₗ[ZMod 2] W := v.equiv w (Equiv.refl (Fin 3))
    have hc : ∀ i, c (v i) = w i := fun i => by rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    have hcinv : ∀ i, c.symm (w i) = v i := fun i => by rw [← hc, LinearEquiv.symm_apply_apply]
    rw [isConj_iff]
    refine ⟨c, LinearEquiv.toLinearMap_injective (w.ext fun i => ?_)⟩
    change c (α (c.symm (w i))) = β (w i)
    rw [hcinv]
    fin_cases i
    · simp only [Fin.zero_eta]
      rw [hv0, hc, hw0]
    · simp only [Fin.mk_one]
      rw [hv1, hc, hw1]
    · simp only [Fin.reduceFinMk]
      rw [hv2, map_add, hc, hc, hw2]

end CFSG.RankThree.Classical.GL3
