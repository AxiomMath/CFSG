module

public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.I51

section Symplectic

variable {K : Type*} [Field K]

theorem alt_skew {V : Type*} [AddCommGroup V] [Module K V] (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ v, B v v = 0) (v w : V) : B v w = - B w v := by
  have h := hB (v + w)
  simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h)

theorem exists_symplectic_family (K : Type*) [Field K] :
    ∀ (n : ℕ) (V : Type _) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : V →ₗ[K] V →ₗ[K] K), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
      Module.finrank K V = 2 * n →
      ∃ e f : Fin n → V, (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
        (∀ i j, B (e i) (e j) = 0) ∧ (∀ i j, B (f i) (f j) = 0) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B _ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ B hB hnd hn
    have hpos : 0 < Module.finrank K V := by omega
    have : Nontrivial V := Module.finrank_pos_iff.1 hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (hnd v h)
    set w' := (B v w)⁻¹ • w with hw'
    have hvw : B v w' = 1 := by
      rw [hw', map_smul, smul_eq_mul, inv_mul_cancel₀ hw]
    have hwv : B w' v = -1 := by rw [alt_skew B hB w' v, hvw]
    let Φ : V →ₗ[K] K × K := LinearMap.prod (B.flip v) (B.flip w')
    have hΦ : ∀ u, Φ u = (B u v, B u w') := fun u => rfl
    have hrange : LinearMap.range Φ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro ab
      refine ⟨(-ab.1) • w' + ab.2 • v, ?_⟩
      rw [hΦ]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwv, hvw,
        smul_eq_mul]
      ext <;> simp [hB]
    have hrk := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self, hn] at hrk
    have hW : Module.finrank K (LinearMap.ker Φ) = 2 * n := by omega
    set W := LinearMap.ker Φ with hWdef
    have hmem : ∀ u : V, u ∈ W ↔ B u v = 0 ∧ B u w' = 0 := by
      intro u
      rw [hWdef, LinearMap.mem_ker, hΦ, Prod.mk_eq_zero]
    let B' : W →ₗ[K] W →ₗ[K] K := LinearMap.BilinForm.restrict B W
    have hB'app : ∀ x y : W, B' x y = B x y := fun x y => rfl
    have hB' : ∀ x : W, B' x x = 0 := fun x => hB x
    have hnd' : ∀ x : W, (∀ y : W, B' x y = 0) → x = 0 := by
      intro x hx
      have hx0 : (x : V) = 0 := by
        apply hnd
        intro y
        have hy : y - B y w' • v + B y v • w' ∈ W := by
          rw [hmem]
          constructor
          · simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
              LinearMap.smul_apply, hB, hwv, smul_eq_mul]
            ring
          · simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
              LinearMap.smul_apply, hB, hvw, smul_eq_mul]
            ring
        have h1 := hx ⟨_, hy⟩
        rw [hB'app] at h1
        have hxv : B (x : V) v = 0 := ((hmem _).1 x.2).1
        have hxw : B (x : V) w' = 0 := ((hmem _).1 x.2).2
        simp only [map_add, map_sub, map_smul, smul_eq_mul, hxv, hxw, mul_zero, sub_zero,
          add_zero] at h1
        exact h1
      exact Subtype.ext hx0
    obtain ⟨e', f', h1, h2, h3⟩ := ih W B' hB' hnd' hW
    have hev : ∀ i, B (e' i : V) v = 0 := fun i => ((hmem _).1 (e' i).2).1
    have hew : ∀ i, B (e' i : V) w' = 0 := fun i => ((hmem _).1 (e' i).2).2
    have hfv : ∀ i, B (f' i : V) v = 0 := fun i => ((hmem _).1 (f' i).2).1
    have hfw : ∀ i, B (f' i : V) w' = 0 := fun i => ((hmem _).1 (f' i).2).2
    have hve : ∀ i, B v (e' i : V) = 0 := fun i => by rw [alt_skew B hB, hev, neg_zero]
    have hvf : ∀ i, B v (f' i : V) = 0 := fun i => by rw [alt_skew B hB, hfv, neg_zero]
    have hwe : ∀ i, B w' (e' i : V) = 0 := fun i => by rw [alt_skew B hB, hew, neg_zero]
    have hwf : ∀ i, B w' (f' i : V) = 0 := fun i => by rw [alt_skew B hB, hfw, neg_zero]
    refine ⟨Fin.cons v (fun i => (e' i : V)), Fin.cons w' (fun i => (f' i : V)), ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hvw]
      · simp [hvf, (Fin.succ_ne_zero j).symm]
      · simp [hew, Fin.succ_ne_zero i]
      · have := h1 i j
        rw [hB'app] at this
        simpa [Fin.succ_inj] using this
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hB]
      · simp [hve]
      · simp [hev]
      · have := h2 i j
        rw [hB'app] at this
        simpa using this
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hB]
      · simp [hwf]
      · simp [hfw]
      · have := h3 i j
        rw [hB'app] at this
        simpa using this

end Symplectic



section Basis

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_basis_of_symplectic_family [FiniteDimensional K V] (B : V →ₗ[K] V →ₗ[K] K)
    (n : ℕ) [NeZero n] (e f : Fin n → V)
    (he : ∀ i j, B (e i) (f j) = if i = j then 1 else 0)
    (hee : ∀ i j, B (e i) (e j) = 0) (hff : ∀ i j, B (f i) (f j) = 0)
    (hn : Module.finrank K V = 2 * n) :
    ∃ b : Module.Basis (Fin n ⊕ Fin n) K V,
      (∀ i, b (Sum.inl i) = e i) ∧ (∀ i, b (Sum.inr i) = f i) := by
  have hli : LinearIndependent K (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have h1 : ∀ j, c (Sum.inl j) = 0 := fun j => by
      have := congrArg (fun w => B w (f j)) hc
      simpa [map_add, map_sum, map_smul, he, hff, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply] using this
    have h2 : ∀ j, c (Sum.inr j) = 0 := fun j => by
      have := congrArg (fun w => B (e j) w) hc
      simpa [map_add, map_sum, map_smul, he, hee] using this
    rintro (j | j)
    · exact h1 j
    · exact h2 j
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl 0⟩
  have hcard : Fintype.card (Fin n ⊕ Fin n) = Module.finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, hn]; omega
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_, fun i => ?_⟩ <;> simp

end Basis


end CFSG.Quasithin.H13.I51
