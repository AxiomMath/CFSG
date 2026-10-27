module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.IOneUDvd

section Field

variable {p : ℕ} [Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

theorem exists_pair_add_ne_zero {ι : Type} [Fintype ι] (h2 : (2 : ZMod p) ≠ 0)
    (h3 : 2 < Fintype.card ι) (g : ι → ZMod p) (hg : ∀ c, g c ≠ 0) :
    ∃ c c' : ι, c ≠ c' ∧ g c + g c' ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
  have h1 := hcon a b hab
  have h2' := hcon a c hac
  have h3' := hcon b c hbc
  have h4 : (2 : ZMod p) * g b = 0 := by linear_combination h1 - h2' + h3'
  rcases mul_eq_zero.mp h4 with h | h
  · exact h2 h
  · exact hg b h

end Field

section Corank

variable {p : ℕ} [Fact p.Prime]

theorem exists_endNode_of_finrank {ι : Type} [Fintype ι] [DecidableEq ι] (hp2 : p ≠ 2)
    (h3 : 2 < Fintype.card ι) {A : Submodule (ZMod p) (ι → ZMod p)}
    (hA : Fintype.card ι - 1 ≤ Module.finrank (ZMod p) A) :
    (∃ c : ι, Pi.single c (1 : ZMod p) ∈ A) ∨
      ∃ c c' : ι, c ≠ c' ∧ ∃ x ∈ A, (∀ k, k ≠ c → k ≠ c' → x k = 0) ∧
        x c ≠ 0 ∧ x c' ≠ 0 ∧ x c ≠ x c' ∧
        ∀ y ∈ A, (∀ k, k ≠ c → k ≠ c' → y k = 0) → ∃ a : ZMod p, y = a • x := by
  have h2 := two_ne_zero_zmod (p := p) hp2
  by_cases htop : A = ⊤
  · obtain ⟨c₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    exact Or.inl ⟨c₀, by rw [htop]; exact Submodule.mem_top⟩
  have hlt : A < ⊤ := lt_top_iff_ne_top.mpr htop
  obtain ⟨f, hf0, hAf⟩ := Submodule.exists_le_ker_of_lt_top A hlt
  obtain ⟨g, hg⟩ : ∃ g : ι → ZMod p, ∀ k, g k = f (Pi.single k 1) := ⟨_, fun k => rfl⟩
  have hfx : ∀ x : ι → ZMod p, f x = ∑ k, x k * g k := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, hg k]
  have hker_lt : LinearMap.ker f < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hf0 (LinearMap.ker_eq_top.mp h)
  have hdim_lt : Module.finrank (ZMod p) (LinearMap.ker f) < Fintype.card ι := by
    have := Submodule.finrank_lt_finrank_of_lt hker_lt
    rwa [finrank_top, Module.finrank_fintype_fun_eq_card] at this
  have hAeq : A = LinearMap.ker f := by
    apply Submodule.eq_of_le_of_finrank_eq hAf
    exact le_antisymm (Submodule.finrank_mono hAf) (by omega)
  have hmemA : ∀ x, x ∈ A ↔ f x = 0 := fun x => by rw [hAeq, LinearMap.mem_ker]
  by_cases hz : ∃ c, g c = 0
  · obtain ⟨c, hc⟩ := hz
    refine Or.inl ⟨c, (hmemA _).mpr ?_⟩
    rw [← hg c]
    exact hc
  push Not at hz
  obtain ⟨c, c', hcc', hsum⟩ := exists_pair_add_ne_zero h2 h3 g hz
  refine Or.inr ⟨c, c', hcc', ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : ι → ZMod p,
      x = g c' • Pi.single c (1 : ZMod p) + (-g c) • Pi.single c' (1 : ZMod p) := ⟨_, rfl⟩
  have hxc : x c = g c' := by
    rw [hx]
    simp [Pi.single_apply, hcc']
  have hxc' : x c' = -g c := by
    rw [hx]
    simp [Pi.single_apply, hcc'.symm]
  have hx0 : ∀ k, k ≠ c → k ≠ c' → x k = 0 := by
    intro k hk1 hk2
    rw [hx]
    simp [Pi.single_apply, hk1, hk2]
  have hxmem : x ∈ A := by
    rw [hmemA, hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hg c, ← hg c']
    ring
  refine ⟨x, hxmem, hx0, ?_, ?_, ?_, ?_⟩
  · rw [hxc]
    exact hz c'
  · rw [hxc']
    exact neg_ne_zero.mpr (hz c)
  · rw [hxc, hxc']
    intro h
    apply hsum
    linear_combination h
  · intro y hy hsupp
    have hy0 : f y = 0 := (hmemA y).mp hy
    have hyeq : y = y c • Pi.single c (1 : ZMod p) + y c' • Pi.single c' (1 : ZMod p) := by
      funext k
      by_cases hkc : k = c
      · rw [hkc]
        simp [Pi.single_apply, hcc']
      · by_cases hkc' : k = c'
        · rw [hkc']
          simp [Pi.single_apply, hcc', hkc]
        · simp [Pi.single_apply, hkc, hkc', hsupp k hkc hkc']
    have hyf : y c * g c + y c' * g c' = 0 := by
      have h := hy0
      rw [hyeq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hg c, ← hg c'] at h
      exact h
    have hgc' : g c' ≠ 0 := hz c'
    refine ⟨y c / g c', ?_⟩
    funext k
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hkc : k = c
    · rw [hkc, hxc, div_mul_cancel₀ _ hgc']
    · by_cases hkc' : k = c'
      · have hyc' : y c' = -(y c * g c) / g c' := by
          rw [eq_div_iff hgc']
          linear_combination hyf
        rw [hkc', hxc', hyc']
        ring
      · rw [hsupp k hkc hkc', hx0 k hkc hkc', mul_zero]

end Corank

end CFSG.StandardType.IOneUDvd
