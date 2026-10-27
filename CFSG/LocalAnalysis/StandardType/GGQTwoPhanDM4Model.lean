module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.QTwo.M4Model

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 3)

def sRoot : Fin 4 → Fin 4 → ZMod 3 :=
  ![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, 1]]

def cmod : Fin 4 → Fin 4 → ZMod 3 :=
  ![![2, -1, 0, 0], ![-1, 2, -1, -1], ![0, -1, 2, 0], ![0, -1, 0, 2]]

def rM : Fin 4 → Mat :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]]

def mul4 (M N : Mat) : Mat :=
  Matrix.of fun a b => M a 0 * N 0 b + M a 1 * N 1 b + M a 2 * N 2 b + M a 3 * N 3 b

theorem mul4_eq (M N : Mat) : mul4 M N = M * N := by
  ext a b
  simp [mul4, Matrix.mul_apply, Fin.sum_univ_four, add_assoc]

def eq4 (M N : Mat) : Bool :=
  (M 0 0 == N 0 0) && (M 0 1 == N 0 1) && (M 0 2 == N 0 2) && (M 0 3 == N 0 3) &&
  (M 1 0 == N 1 0) && (M 1 1 == N 1 1) && (M 1 2 == N 1 2) && (M 1 3 == N 1 3) &&
  (M 2 0 == N 2 0) && (M 2 1 == N 2 1) && (M 2 2 == N 2 2) && (M 2 3 == N 2 3) &&
  (M 3 0 == N 3 0) && (M 3 1 == N 3 1) && (M 3 2 == N 3 2) && (M 3 3 == N 3 3)

theorem eq4_iff {M N : Mat} : eq4 M N = true ↔ M = N := by
  constructor
  · intro h
    simp only [eq4, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h03⟩, h10⟩, h11⟩, h12⟩, h13⟩, h20⟩, h21⟩, h22⟩,
      h23⟩, h30⟩, h31⟩, h32⟩, h33⟩ := h
    ext a b
    fin_cases a <;> fin_cases b <;> assumption
  · rintro rfl
    simp [eq4]

def perms4 : List (List (Fin 4)) :=
  (List.finRange 4).flatMap fun a => (List.finRange 4).flatMap fun b =>
    (List.finRange 4).flatMap fun c => (List.finRange 4).filterMap fun d =>
      if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then some [a, b, c, d] else none

def spMat (l : List (Fin 4)) (n : ℕ) : Mat :=
  Matrix.of fun a b =>
    if a = l.getD b.val 0 then (if (n / 2 ^ b.val) % 2 = 1 then -1 else 1) else 0

def spe : List Mat :=
  perms4.flatMap fun l => [0, 3, 5, 6, 9, 10, 12, 15].map fun n => spMat l n

theorem spe_closed_bool : spe.all (fun M => (List.finRange 4).all fun i =>
    spe.any fun N => eq4 (mul4 M (rM i)) N) = true := by decide +kernel

theorem spe_one_bool : spe.any (fun N => eq4 1 N) = true := by decide +kernel

theorem spe_closed : ∀ M ∈ spe, ∀ i, M * rM i ∈ spe := by
  intro M hM i
  have h1 := List.all_eq_true.mp spe_closed_bool M hM
  have h2 := List.all_eq_true.mp h1 i (List.mem_finRange i)
  obtain ⟨N, hN, hNe⟩ := List.any_eq_true.mp h2
  rw [eq4_iff, mul4_eq] at hNe
  rwa [hNe]

theorem one_mem_spe : (1 : Mat) ∈ spe := by
  obtain ⟨N, hN, hNe⟩ := List.any_eq_true.mp spe_one_bool
  rw [eq4_iff] at hNe
  rwa [← hNe] at hN

theorem spe_stab_abcd : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    (spe.filter (fun M => decide (M.mulVec ![a, b, c, d] = ![a, b, c, d]))).length ≤ 24 := by
  decide +kernel

theorem spe_stab (w : Fin 4 → ZMod 3) (hw : w ≠ 0) :
    (spe.filter (fun M => decide (M.mulVec w = w))).length ≤ 24 := by
  have hw' : w = ![w 0, w 1, w 2, w 3] := by
    ext k
    fin_cases k <;> rfl
  have hne : ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    apply hw
    ext k
    fin_cases k <;> assumption
  rw [hw']
  exact spe_stab_abcd _ _ _ _ hne

section Abstract

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem cast_cartanD_four : ∀ i j : Fin 4, ((CartanMatrix.D 4 i j : ℤ) : ZMod 3) = cmod i j := by
  decide +kernel

theorem rM_mulVec_sRoot :
    ∀ i j : Fin 4, (rM i).mulVec (sRoot j) = sRoot j - cmod i j • sRoot i := by
  decide +kernel

theorem cmod_solve : ∀ a b c d : ZMod 3,
    (∀ k : Fin 4, a * cmod k 0 + b * cmod k 1 + c * cmod k 2 + d * cmod k 3 = 0) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by decide +kernel

theorem sRoot_solve : ∀ a b c d : ZMod 3,
    (∀ k : Fin 4, a * sRoot 0 k + b * sRoot 1 k + c * sRoot 2 k + d * sRoot 3 k = 0) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by decide +kernel

theorem d4Mod3_stab_card_le (hV : Nat.card V = 3 ^ 4) (h : Fin 4 → V)
    (α : Fin 4 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (hC : ∀ i j, α i (h j) = ((CartanMatrix.D 4 i j : ℤ) : ZMod 3)) {v : V} (hv : v ≠ 0) :
    Nat.card {g : ↥(Subgroup.closure (Set.range fun i => Module.reflection (hα i))) //
      (g : V ≃ₗ[ZMod 3] V) v = v} ≤ 24 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCm : ∀ i j, α i (h j) = cmod i j := fun i j => (hC i j).trans (cast_cartanD_four i j)
  have hfinV : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 3) V = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [hV, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hli : LinearIndependent (ZMod 3) h := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hk : ∀ k, c 0 * cmod k 0 + c 1 * cmod k 1 + c 2 * cmod k 2 + c 3 * cmod k 3 = 0 := by
      intro k
      have h1 := congrArg (α k) hc
      simpa [map_sum, map_smul, hCm, Fin.sum_univ_four] using h1
    obtain ⟨h0, h1, h2, h3⟩ := cmod_solve (c 0) (c 1) (c 2) (c 3) hk
    fin_cases i <;> assumption
  let b : Module.Basis (Fin 4) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hfin])
  have hbh : ∀ j, b j = h j := fun j => by simp [b]
  let Φ : V →ₗ[ZMod 3] (Fin 4 → ZMod 3) := b.constr (ZMod 3) sRoot
  have hΦh : ∀ j, Φ (h j) = sRoot j := fun j => by
    rw [← hbh j]
    exact b.constr_basis (ZMod 3) sRoot j
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hsum : u = ∑ j, b.repr u j • h j := by
      conv_lhs => rw [← b.sum_repr u]
      exact Finset.sum_congr rfl fun j _ => by rw [hbh j]
    have hΦu : Φ u = ∑ j, b.repr u j • sRoot j := by
      conv_lhs => rw [hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hΦh]
    have hk : ∀ k, b.repr u 0 * sRoot 0 k + b.repr u 1 * sRoot 1 k + b.repr u 2 * sRoot 2 k +
        b.repr u 3 * sRoot 3 k = 0 := by
      intro k
      have h1 : (∑ j, b.repr u j • sRoot j) = 0 := hΦu ▸ hu
      have h2 := congrFun h1 k
      simpa [Finset.sum_apply, Fin.sum_univ_four] using h2
    obtain ⟨h0, h1, h2, h3⟩ := sRoot_solve _ _ _ _ hk
    have hrepr : b.repr u = 0 := by
      ext j
      fin_cases j <;> simpa
    exact b.repr.map_eq_zero_iff.mp hrepr
  have hΦR : ∀ i u, Φ (Module.reflection (hα i) u) = (rM i).mulVec (Φ u) := by
    intro i
    have hcomp : Φ ∘ₗ (Module.reflection (hα i) : V ≃ₗ[ZMod 3] V).toLinearMap =
        (rM i).mulVecLin ∘ₗ Φ := by
      refine b.ext fun j => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
      rw [hbh j, Module.reflection_apply, map_sub, map_smul, hΦh, hΦh, hCm i j,
        rM_mulVec_sRoot]
    intro u
    exact DFunLike.congr_fun hcomp u
  have hcl : ∀ g ∈ Subgroup.closure (Set.range fun i => Module.reflection (hα i)),
      ∃ M ∈ spe, ∀ u, Φ (g u) = M.mulVec (Φ u) := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨1, one_mem_spe, fun u => by simp⟩
    | mul_right x hx y hy ih =>
      obtain ⟨M, hM, hMx⟩ := ih
      obtain ⟨i, rfl⟩ := hy
      refine ⟨M * rM i, spe_closed M hM i, fun u => ?_⟩
      rw [LinearEquiv.mul_apply, hMx, hΦR, Matrix.mulVec_mulVec]
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨M, hM, hMx⟩ := ih
      obtain ⟨i, rfl⟩ := hy
      refine ⟨M * rM i, spe_closed M hM i, fun u => ?_⟩
      rw [Module.reflection_inv, LinearEquiv.mul_apply, hMx, hΦR, Matrix.mulVec_mulVec]
  have hΦv : Φ v ≠ 0 := fun h0 => hv (hΦinj (h0.trans (map_zero Φ).symm))
  let P : Mat → Prop := fun M => M ∈ spe ∧ M.mulVec (Φ v) = Φ v
  let f : {g : ↥(Subgroup.closure (Set.range fun i => Module.reflection (hα i))) //
      (g : V ≃ₗ[ZMod 3] V) v = v} → {M : Mat // P M} :=
    fun g => ⟨(hcl g.1 g.1.2).choose, (hcl g.1 g.1.2).choose_spec.1, by
      have h1 := (hcl g.1 g.1.2).choose_spec.2 v
      rw [g.2] at h1
      exact h1.symm⟩
  have hf : Function.Injective f := by
    intro g₁ g₂ h12
    have hM : (hcl g₁.1 g₁.1.2).choose = (hcl g₂.1 g₂.1.2).choose := congrArg Subtype.val h12
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    apply hΦinj
    rw [(hcl g₁.1 g₁.1.2).choose_spec.2 u, (hcl g₂.1 g₂.1.2).choose_spec.2 u, hM]
  refine (Nat.card_le_card_of_injective f hf).trans ?_
  let L : List Mat := spe.filter fun M => decide (M.mulVec (Φ v) = Φ v)
  have hsub : {M : Mat | P M} ⊆ (↑L.toFinset : Set Mat) := by
    intro M hM
    simp only [Set.mem_setOf_eq, P] at hM
    simp [L, hM]
  calc Nat.card {M : Mat // P M} = Nat.card ↥{M : Mat | P M} := rfl
    _ ≤ Nat.card ↥(↑L.toFinset : Set Mat) := Nat.card_mono (Set.toFinite _) hsub
    _ = L.toFinset.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ L.length := List.toFinset_card_le L
    _ ≤ 24 := spe_stab (Φ v) hΦv

end Abstract

end CFSG.StandardType.QTwo.M4Model

end
