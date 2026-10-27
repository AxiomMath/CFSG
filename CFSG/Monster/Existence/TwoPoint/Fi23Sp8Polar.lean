module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.ZMod
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.Existence.Fi23Sp8

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

abbrev V8 : Type := Fin 4 ⊕ Fin 4 → ZMod 2

@[expose] noncomputable def Bf : BilinForm (ZMod 2) V8 :=
  Matrix.toBilin' (Matrix.J (Fin 4) (ZMod 2))

theorem Bf_apply (u v : V8) :
    Bf u v = ∑ i : Fin 4, (u (Sum.inl i) * v (Sum.inr i) + u (Sum.inr i) * v (Sum.inl i)) := by
  rw [Bf, Matrix.toBilin'_apply', Matrix.J, Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [Matrix.zero_mulVec, zero_add, add_zero, Matrix.neg_mulVec, Matrix.one_mulVec,
    Function.comp_apply, Pi.neg_apply, mul_neg]
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact CharTwo.neg_eq _

theorem Bf_comm (u v : V8) : Bf u v = Bf v u := by
  rw [Bf_apply, Bf_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Bf_isAlt : Bf.IsAlt := by
  intro u
  rw [Bf_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (u (Sum.inr i)) (u (Sum.inl i))]
  exact CharTwo.add_self_eq_zero _

theorem Bf_single_inl (u : V8) (i : Fin 4) : Bf u (Pi.single (Sum.inl i) 1) = u (Sum.inr i) := by
  rw [Bf_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have h1 : (Sum.inl j : Fin 4 ⊕ Fin 4) ≠ Sum.inl i := fun h => hj (Sum.inl_injective h)
    simp [h1]
  · simp

theorem Bf_single_inr (u : V8) (i : Fin 4) : Bf u (Pi.single (Sum.inr i) 1) = u (Sum.inl i) := by
  rw [Bf_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have h1 : (Sum.inr j : Fin 4 ⊕ Fin 4) ≠ Sum.inr i := fun h => hj (Sum.inr_injective h)
    simp [h1]
  · simp

theorem Bf_left_zero {u : V8} (h : ∀ v, Bf u v = 0) : u = 0 := by
  funext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    rwa [Bf_single_inr] at this
  · have := h (Pi.single (Sum.inl i) 1)
    rwa [Bf_single_inl] at this

theorem Bf_nondegenerate : Bf.Nondegenerate :=
  ⟨fun _ h => Bf_left_zero h, fun v h => Bf_left_zero fun u => by rw [Bf_comm]; exact h u⟩

theorem span_of_orthogonal {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (B : BilinForm (ZMod 2) V) (hB : B.Nondegenerate) (x y w : V)
    (h : ∀ z, B z x = 0 → B z y = 0 → B z w = 0) :
    w = 0 ∨ w = x ∨ w = y ∨ w = x + y := by
  let L : Fin 2 → V →ₗ[ZMod 2] ZMod 2 := ![B.flip x, B.flip y]
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker (B.flip w) := by
    intro z hz
    rw [Submodule.mem_iInf] at hz
    have h0 := hz 0
    have h1 := hz 1
    simp only [L, LinearMap.mem_ker, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 ⊢
    exact h z h0 h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1
    (mem_span_of_iInf_ker_le_ker hker)
  have hw : ∀ z, B z w = B z (c 0 • x + c 1 • y) := by
    intro z
    have := congrArg (fun f => f z) hc
    simp only [L, Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at this
    change c 0 * B z x + c 1 * B z y = B z w at this
    rw [← this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hw' : w = c 0 • x + c 1 • y := by
    have : w - (c 0 • x + c 1 • y) = 0 := by
      apply hB.2 (w - (c 0 • x + c 1 • y))
      intro v
      rw [map_sub]
      exact sub_eq_zero.2 (hw v)
    exact sub_eq_zero.1 this
  rw [hw']
  have hc0 : c 0 = 0 ∨ c 0 = 1 := by
    generalize c 0 = a
    revert a; decide
  have hc1 : c 1 = 0 ∨ c 1 = 1 := by
    generalize c 1 = a
    revert a; decide
  rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;> simp [h0, h1]

theorem V8_add_self (u : V8) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

theorem V8_neg (u : V8) : -u = u := by
  funext i
  exact CharTwo.neg_eq _

theorem mem_span_iff_orthogonal (x y w : V8) :
    (∀ z, Bf z x = 0 → Bf z y = 0 → Bf z w = 0) ↔ w = 0 ∨ w = x ∨ w = y ∨ w = x + y := by
  constructor
  · exact span_of_orthogonal Bf Bf_nondegenerate x y w
  · rintro (rfl | rfl | rfl | rfl) z hx hy
    · simp
    · exact hx
    · exact hy
    · rw [map_add, hx, hy, add_zero]

theorem zmod2_eq_of_iff (a b : ZMod 2) (h : a = 0 ↔ b = 0) : a = b := by
  revert a b; decide

theorem polar_aut (φ : V8 → V8) (h0 : φ 0 = 0) (hinj : Function.Injective φ)
    (hperp : ∀ u v, Bf u v = 0 ↔ Bf (φ u) (φ v) = 0) :
    ∃ g : LinearMap.GeneralLinearGroup (ZMod 2) V8, g ∈ bilinIsometryGroup Bf ∧
      ∀ v, (g : V8 →ₗ[ZMod 2] V8) v = φ v := by
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  have hline : ∀ x y w, (w = 0 ∨ w = x ∨ w = y ∨ w = x + y) →
      (φ w = 0 ∨ φ w = φ x ∨ φ w = φ y ∨ φ w = φ x + φ y) := by
    intro x y w hw
    have h1 := (mem_span_iff_orthogonal x y w).2 hw
    have h2 : ∀ z', Bf z' (φ x) = 0 → Bf z' (φ y) = 0 → Bf z' (φ w) = 0 := by
      intro z' hx hy
      obtain ⟨z, rfl⟩ := hsurj z'
      exact (hperp z w).1 (h1 z ((hperp z x).2 hx) ((hperp z y).2 hy))
    exact (mem_span_iff_orthogonal (φ x) (φ y) (φ w)).1 h2
  have hadd : ∀ u v, φ (u + v) = φ u + φ v := by
    intro u v
    by_cases hu : u = 0
    · rw [hu, zero_add, h0, zero_add]
    by_cases hv : v = 0
    · rw [hv, add_zero, h0, add_zero]
    by_cases huv : u = v
    · rw [huv, V8_add_self, h0, V8_add_self]
    have hw0 : u + v ≠ 0 := by
      intro h
      apply huv
      have : u = -v := eq_neg_of_add_eq_zero_left h
      rw [this, V8_neg]
    have hwu : u + v ≠ u := fun h => hv (by simpa using h)
    have hwv : u + v ≠ v := fun h => hu (by simpa using h)
    rcases hline u v (u + v) (Or.inr (Or.inr (Or.inr rfl))) with h | h | h | h
    · exact absurd (hinj (h.trans h0.symm)) hw0
    · exact absurd (hinj h) hwu
    · exact absurd (hinj h) hwv
    · exact h
  let f : V8 →+ V8 := AddMonoidHom.mk' φ hadd
  let F : V8 →ₗ[ZMod 2] V8 := AddMonoidHom.toZModLinearMap 2 f
  have hF : ∀ v, F v = φ v := fun v => rfl
  have hbij : Function.Bijective F := ⟨hinj, hsurj⟩
  let E : V8 ≃ₗ[ZMod 2] V8 := LinearEquiv.ofBijective F hbij
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv E, ?_, fun v => rfl⟩
  intro x y
  show Bf (φ x) (φ y) = Bf x y
  exact (zmod2_eq_of_iff _ _ (hperp x y)).symm

end CFSG.Monster.Existence.Fi23Sp8
