module

public import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.Set.Finite.List

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

theorem w0_mul_self (w₀ : W) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) :
    w₀ * w₀ = 1 := by
  have h := hw w₀
  have h0 : cs.length (w₀ * w₀) = 0 := by omega
  exact cs.length_eq_zero_iff.mp h0

theorem length_w0_mul (w₀ : W) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (w : W) : cs.length (w₀ * w) + cs.length w = cs.length w₀ := by
  have hw0 : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_left (w0_mul_self cs w₀ hw)
  have h := hw w⁻¹
  rw [cs.length_inv] at h
  rw [show w₀ * w = (w⁻¹ * w₀)⁻¹ by rw [mul_inv_rev, inv_inv, hw0], cs.length_inv]
  exact h

theorem length_w0_conj (w₀ : W) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (w : W) : cs.length (w₀ * w * w₀) = cs.length w := by
  have h1 := hw (w₀ * w)
  have h2 := length_w0_mul cs w₀ hw w
  omega

theorem exists_simple_conj_w0 (w₀ : W)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) (j : B) :
    ∃ j', w₀ * cs.simple j * w₀ = cs.simple j' := by
  have h := length_w0_conj cs w₀ hw (cs.simple j)
  rw [cs.length_simple] at h
  exact cs.length_eq_one_iff.mp h

theorem finite_of_w0 [Finite B] (w₀ : W)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) : Finite W := by
  let n := cs.length w₀
  have hle : ∀ w, cs.length w ≤ n := by
    intro w
    have := hw w
    omega
  let f : {ω : List B // ω.length ≤ n} → W := fun ω => cs.wordProd ω.1
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    refine ⟨⟨ω, ?_⟩, rfl⟩
    show ω.length ≤ n
    rw [← hω]
    exact hle (cs.wordProd ω)
  haveI : Finite {ω : List B // ω.length ≤ n} := (List.finite_length_le B n).to_subtype
  exact Finite.of_surjective f hf

theorem exists_rank [Finite W] :
    ∃ rk : W → ℕ, Function.Injective rk ∧ rk 1 = 0 ∧
      ∀ u v, cs.length u < cs.length v → rk u < rk v := by
  classical
  let N := Nat.card W
  have hN : 0 < N := Finite.card_pos
  let e : W ≃ Fin N := Finite.equivFin W
  let rk : W → ℕ := fun u => if u = 1 then 0 else cs.length u * N + (e u : ℕ) + 1
  have hrk : ∀ u, u ≠ 1 → rk u = cs.length u * N + (e u : ℕ) + 1 := by
    intro u hu
    show (if u = 1 then 0 else cs.length u * N + (e u : ℕ) + 1) = _
    rw [if_neg hu]
  refine ⟨rk, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u = 1
    · subst hu
      by_cases hv : v = 1
      · rw [hv]
      · exfalso
        have h1 : rk 1 = 0 := by simp [rk]
        rw [h1, hrk v hv] at huv
        omega
    · by_cases hv : v = 1
      · exfalso
        have h1 : rk 1 = 0 := by simp [rk]
        rw [hv, h1, hrk u hu] at huv
        omega
      · rw [hrk u hu, hrk v hv] at huv
        have heq : cs.length u * N + (e u : ℕ) = cs.length v * N + (e v : ℕ) := by
          omega
        have hmod : (e u : ℕ) = (e v : ℕ) := by
          have h := congrArg (· % N) heq
          rwa [Nat.add_comm (cs.length u * N) (e u : ℕ),
               Nat.add_comm (cs.length v * N) (e v : ℕ),
               Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
               Nat.mod_eq_of_lt (e u).isLt, Nat.mod_eq_of_lt (e v).isLt] at h
        exact e.injective (Fin.ext hmod)
  · simp [rk]
  · intro u v huv
    by_cases hu : u = 1
    · subst hu
      have hlen : 0 < cs.length v := by simpa using huv
      have hv : v ≠ 1 := by
        intro hv
        rw [hv] at huv
        simp at huv
      rw [show rk 1 = 0 by simp [rk], hrk v hv]
      omega
    · have hv : v ≠ 1 := by
        intro hv
        rw [hv] at huv
        simp at huv
      rw [hrk u hu, hrk v hv]
      have heu : (e u : ℕ) + 1 ≤ N := by have := (e u).isLt; omega
      calc cs.length u * N + (e u : ℕ) + 1
          = cs.length u * N + ((e u : ℕ) + 1) := by ring
        _ ≤ cs.length u * N + N := Nat.add_le_add_left heu _
        _ = (cs.length u + 1) * N := by ring
        _ ≤ cs.length v * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt huv)
        _ < cs.length v * N + (e v : ℕ) + 1 := by omega

theorem length_simple_mul_eq_length_mul_simple_of_mul_self {w : W} (hw : w * w = 1) (j : B) :
    cs.length (cs.simple j * w) = cs.length (w * cs.simple j) := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  rw [show cs.simple j * w = (w * cs.simple j)⁻¹ by
        rw [mul_inv_rev, cs.inv_simple, hw'], cs.length_inv]

end CoxeterSystem

end
