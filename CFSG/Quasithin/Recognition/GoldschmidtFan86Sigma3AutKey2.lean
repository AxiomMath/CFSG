module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutKey

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup
open scoped commutatorElement

variable {R : Type*} [Group R]

theorem moved_case (φ : MulAut (DihedralGroup 4 × R)) (hmov : φ (a0, 1) ≠ (a0, 1))
    (d : DihedralGroup 4) : (φ (d, 1)).1 = r 0 ∨ (φ (d, 1)).1 = r 2 := by
  have hc1 : (φ (a0, 1)).1 = 1 := by
    rcases image_shape φ (sr 0) (by decide) with ⟨_, h⟩ | ⟨_, _, h⟩
    · exact h
    · exact absurd h hmov
  have hnc : ∀ d₀ : DihedralGroup 4, ¬ (d₀ = r 0 ∨ d₀ = r 2) →
      (φ (d₀, 1)).1 = r 0 ∨ (φ (d₀, 1)).1 = r 2 := by
    intro d₀ hd₀
    rcases image_shape φ d₀ hd₀ with ⟨h, _⟩ | ⟨_, _, h⟩
    · exact h
    · exact absurd h hmov
  by_cases hd : d = r 0 ∨ d = r 2
  · left
    rcases hd with rfl | rfl
    · have : ((r 0 : DihedralGroup 4), (1 : R)) = 1 := rfl
      rw [this, map_one]; rfl
    · exact hc1
  · exact hnc d hd

theorem moved_pow {M : Type*} [Group M] (f : MulAut M) (p : ℕ) (hp : p.Prime)
    (hf : orderOf f = p) (x : M) (hmov : f x ≠ x) (i : ℕ) (hi : ¬ p ∣ i) : (f ^ i) x ≠ x := by
  intro hx
  have hcop : Nat.Coprime i (orderOf f) :=
    hf ▸ Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hi)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hfix : ∀ n : ℕ, ((f ^ i) ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]
  exact hmov (by rw [← hm]; exact hfix m)

theorem key_aut (f : MulAut (DihedralGroup 4 × R)) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : orderOf f = p) (i : ℕ) :
    (∀ x ∈ kleinA, (f ^ i) (x, 1) ∈ kleinA.prod ⊤) ∧
      (∀ x ∈ kleinB, (f ^ i) (x, 1) ∈ kleinB.prod ⊤) := by
  have hf' : f ^ p = 1 := hf ▸ pow_orderOf_eq_one f
  have hodd : Odd p := hp.odd_of_ne_two hp2
  by_cases hfix : f (a0, 1) = (a0, 1)
  · obtain ⟨hA, hB⟩ := fixed_case f p hodd hf' hfix i
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact Subgroup.mem_prod.2 ⟨mem_kleinA.2 ((hA (x, 1)).1 (mem_kleinA.1 hx)), Subgroup.mem_top _⟩
    · exact Subgroup.mem_prod.2 ⟨mem_kleinB.2 ((hB (x, 1)).1 (mem_kleinB.1 hx)), Subgroup.mem_top _⟩
  · rw [pow_eq_pow_mod i hf']
    by_cases h0 : i % p = 0
    · rw [h0]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simpa using Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top (1 : R)⟩
      · simpa using Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top (1 : R)⟩
    · have hnd : ¬ p ∣ i % p := fun h => h0 (Nat.eq_zero_of_dvd_of_lt h (Nat.mod_lt _ hp.pos))
      have hmov := moved_pow f p hp hf (a0, 1) hfix (i % p) hnd
      have hz : ∀ x : DihedralGroup 4, ((f ^ (i % p)) (x, 1)).1 = r 0 ∨
          ((f ^ (i % p)) (x, 1)).1 = r 2 := fun x => moved_case (f ^ (i % p)) hmov x
      refine ⟨fun x _ => ?_, fun x _ => ?_⟩
      · exact Subgroup.mem_prod.2 ⟨mem_kleinA.2 (by rcases hz x with h | h <;> rw [h] <;> decide),
          Subgroup.mem_top _⟩
      · exact Subgroup.mem_prod.2 ⟨mem_kleinB.2 (by rcases hz x with h | h <;> rw [h] <;> decide),
          Subgroup.mem_top _⟩

end CFSG.Quasithin.Fan86.Sigma3
