module

public import Mathlib.GroupTheory.Subgroup.Simple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Kernel
public import Mathlib.Basic.Finite.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

variable {S₀ : Type*} [Group S₀]

private theorem exists_mul_ne_mul {T : Type*} [Group T] (hT : Subgroup.center T = ⊥) {x : T}
    (hx : x ≠ 1) : ∃ z : T, x * z ≠ z * x := by
  by_contra h
  push Not at h
  refine hx ?_
  have hxmem : x ∈ Subgroup.center T := Subgroup.mem_center_iff.mpr fun z => (h z).symm
  rw [hT] at hxmem
  simpa using hxmem

private theorem mul_mul_inv_mul_inv_ne_one {T : Type*} [Group T] {x z : T}
    (h : x * z ≠ z * x) : x * z * x⁻¹ * z⁻¹ ≠ 1 := by
  intro h1
  apply h
  have h2 : x * z * x⁻¹ = z := by
    have := congrArg (· * z) h1
    simpa [mul_assoc] using this
  have h3 : x * z = z * x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  exact h3

private theorem ker_snd_le_of_fst_ne_one [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) {x y : S₀} (hxy : (x, y) ∈ N) (hx : x ≠ 1) :
    (MonoidHom.snd S₀ S₀).ker ≤ N := by
  obtain ⟨z, hz⟩ := exists_mul_ne_mul (center_eq_bot_of_isSimpleGroup hS) hx
  have hne : z * x * z⁻¹ * x⁻¹ ≠ 1 :=
    mul_mul_inv_mul_inv_ne_one fun h => hz h.symm
  have hmem : ((z * x * z⁻¹ * x⁻¹, 1) : S₀ × S₀) ∈ N := by
    have hconj : ((z, 1) : S₀ × S₀) * (x, y) * ((z, 1) : S₀ × S₀)⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem hN (x, y) hxy (z, 1)
    have hstep : (((z, 1) : S₀ × S₀) * (x, y) * ((z, 1) : S₀ × S₀)⁻¹) * (x, y)⁻¹ ∈ N :=
      N.mul_mem hconj (N.inv_mem hxy)
    have hEq : ((z * x * z⁻¹ * x⁻¹, 1) : S₀ × S₀)
        = (((z, 1) : S₀ × S₀) * (x, y) * ((z, 1) : S₀ × S₀)⁻¹) * (x, y)⁻¹ := by
      refine Prod.ext ?_ ?_
      · simp
      · simp
    rw [hEq]
    exact hstep
  have hKtop : N.comap (MonoidHom.inl S₀ S₀) = ⊤ := by
    haveI : (N.comap (MonoidHom.inl S₀ S₀)).Normal :=
      Subgroup.Normal.comap hN (MonoidHom.inl S₀ S₀)
    have hcK : z * x * z⁻¹ * x⁻¹ ∈ N.comap (MonoidHom.inl S₀ S₀) := by
      simpa using hmem
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl S₀ S₀)) with h | h
    · rw [h] at hcK
      exact absurd (by simpa using hcK) hne
    · exact h
  rintro ⟨a, b⟩ hp
  rw [MonoidHom.mem_ker] at hp
  have hb : b = 1 := hp
  have hmem₁ : ((a, 1) : S₀ × S₀) ∈ N := by
    have : a ∈ N.comap (MonoidHom.inl S₀ S₀) := hKtop ▸ Subgroup.mem_top a
    simpa using this
  have hab : (a, b) = ((a, 1) : S₀ × S₀) := Prod.ext rfl hb
  rw [hab]
  exact hmem₁

private theorem ker_fst_le_of_snd_ne_one [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) {x y : S₀} (hxy : (x, y) ∈ N) (hy : y ≠ 1) :
    (MonoidHom.fst S₀ S₀).ker ≤ N := by
  obtain ⟨z, hz⟩ := exists_mul_ne_mul (center_eq_bot_of_isSimpleGroup hS) hy
  have hne : z * y * z⁻¹ * y⁻¹ ≠ 1 :=
    mul_mul_inv_mul_inv_ne_one fun h => hz h.symm
  have hmem : ((1, z * y * z⁻¹ * y⁻¹) : S₀ × S₀) ∈ N := by
    have hconj : ((1, z) : S₀ × S₀) * (x, y) * ((1, z) : S₀ × S₀)⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem hN (x, y) hxy (1, z)
    have hstep : (((1, z) : S₀ × S₀) * (x, y) * ((1, z) : S₀ × S₀)⁻¹) * (x, y)⁻¹ ∈ N :=
      N.mul_mem hconj (N.inv_mem hxy)
    have hEq : ((1, z * y * z⁻¹ * y⁻¹) : S₀ × S₀)
        = (((1, z) : S₀ × S₀) * (x, y) * ((1, z) : S₀ × S₀)⁻¹) * (x, y)⁻¹ := by
      refine Prod.ext ?_ ?_
      · simp
      · simp
    rw [hEq]
    exact hstep
  have hKtop : N.comap (MonoidHom.inr S₀ S₀) = ⊤ := by
    haveI : (N.comap (MonoidHom.inr S₀ S₀)).Normal :=
      Subgroup.Normal.comap hN (MonoidHom.inr S₀ S₀)
    have hcK : z * y * z⁻¹ * y⁻¹ ∈ N.comap (MonoidHom.inr S₀ S₀) := by
      simpa using hmem
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr S₀ S₀)) with h | h
    · rw [h] at hcK
      exact absurd (by simpa using hcK) hne
    · exact h
  rintro ⟨a, b⟩ hp
  rw [MonoidHom.mem_ker] at hp
  have ha : a = 1 := hp
  have hmem₁ : ((1, b) : S₀ × S₀) ∈ N := by
    have : b ∈ N.comap (MonoidHom.inr S₀ S₀) := hKtop ▸ Subgroup.mem_top b
    simpa using this
  have hab : (a, b) = ((1, b) : S₀ × S₀) := Prod.ext ha rfl
  rw [hab]
  exact hmem₁

private theorem eq_bot_or_eq_ker_fst [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) (h : ∀ p ∈ N, p.1 = 1) :
    N = ⊥ ∨ N = (MonoidHom.fst S₀ S₀).ker := by
  have hle : N ≤ (MonoidHom.fst S₀ S₀).ker := by
    rintro ⟨a, b⟩ hp
    rw [MonoidHom.mem_ker]
    exact h (a, b) hp
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · refine Or.inr (le_antisymm hle ?_)
    have hne : ∃ p ∈ N, p ≠ 1 := by
      by_contra hc
      push Not at hc
      refine hbot (le_bot_iff.mp ?_)
      intro p hp
      simpa using hc p hp
    obtain ⟨p, hp, hp1⟩ := hne
    have hp1' : p.1 = 1 := h p hp
    have hp2 : p.2 ≠ 1 := fun h2 => hp1 (Prod.ext hp1' h2)
    exact ker_fst_le_of_snd_ne_one hS hN hp hp2

theorem normal_prod_cases [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) :
    N = ⊥ ∨ N = (MonoidHom.snd S₀ S₀).ker ∨ N = (MonoidHom.fst S₀ S₀).ker ∨ N = ⊤ := by
  by_cases hA : ∃ p ∈ N, p.1 ≠ 1
  · obtain ⟨p, hp, hp1⟩ := hA
    have h₁ : (MonoidHom.snd S₀ S₀).ker ≤ N := ker_snd_le_of_fst_ne_one hS hN hp hp1
    by_cases hB : ∃ p ∈ N, p.2 ≠ 1
    · obtain ⟨q, hq, hq1⟩ := hB
      have h₂ : (MonoidHom.fst S₀ S₀).ker ≤ N := ker_fst_le_of_snd_ne_one hS hN hq hq1
      refine Or.inr (Or.inr (Or.inr (eq_top_iff.mpr fun r _ => ?_)))
      have h1' : ((r.1, 1) : S₀ × S₀) ∈ N := h₁ (by simp [Subgroup.mem_prod])
      have h2' : ((1, r.2) : S₀ × S₀) ∈ N := h₂ (by simp [Subgroup.mem_prod])
      have hmul : ((r.1, 1) : S₀ × S₀) * (1, r.2) ∈ N := N.mul_mem h1' h2'
      have hr : ((r.1, 1) : S₀ × S₀) * (1, r.2) = r := by
        refine Prod.ext ?_ ?_
        · simp
        · simp
      rw [hr] at hmul
      exact hmul
    · push Not at hB
      refine Or.inr (Or.inl (le_antisymm ?_ h₁))
      rintro ⟨a, b⟩ hr
      rw [MonoidHom.mem_ker]
      exact hB (a, b) hr
  · push Not at hA
    rcases eq_bot_or_eq_ker_fst hS hN hA with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

private theorem factor_le_of_ne_bot [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) (hbot : N ≠ ⊥) :
    (MonoidHom.snd S₀ S₀).ker ≤ N ∨ (MonoidHom.fst S₀ S₀).ker ≤ N := by
  rcases normal_prod_cases hS hN with h | h | h | h
  · exact absurd h hbot
  · exact Or.inl (le_of_eq h.symm)
  · exact Or.inr (le_of_eq h.symm)
  · exact Or.inl (by rw [h]; exact le_top)

theorem eq_bot_of_pow_four_prod [Finite S₀] [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    {N : Subgroup (S₀ × S₀)} (hN : N.Normal) (h4 : ∀ x ∈ N, x ^ 4 = 1) : N = ⊥ := by
  by_contra hbot
  have hfac := factor_le_of_ne_bot hS hN hbot
  have hall : ∀ x : S₀, x ^ 4 = 1 := by
    intro x
    rcases hfac with h | h
    · have hxN : ((x, 1) : S₀ × S₀) ∈ N := h (by simp [Subgroup.mem_prod])
      simpa using h4 (x, 1) hxN
    · have hxN : ((1, x) : S₀ × S₀) ∈ N := h (by simp [Subgroup.mem_prod])
      simpa using h4 (1, x) hxN
  have htop : (⊤ : Subgroup S₀) = ⊥ :=
    eq_bot_of_pow_four hS (N := ⊤) Subgroup.normal_top fun x _ => hall x
  obtain ⟨x, hx⟩ := exists_ne (1 : S₀)
  have hxbot : x ∈ (⊥ : Subgroup S₀) := by
    rw [← htop]
    trivial
  exact hx (by simpa using hxbot)

theorem not_isSimpleGroup_prod [Nontrivial S₀] : ¬ IsSimpleGroup (S₀ × S₀) := by
  intro hs
  obtain ⟨x, hx⟩ := exists_ne (1 : S₀)
  haveI : IsSimpleGroup (S₀ × S₀) := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.fst S₀ S₀).ker with h | h
  · have h1 : ((1, x) : S₀ × S₀) ∈ (MonoidHom.fst S₀ S₀).ker := by
      simp [Subgroup.mem_prod]
    rw [h] at h1
    exact hx (by simpa using h1)
  · have h1 : ((x, 1) : S₀ × S₀) ∈ (MonoidHom.fst S₀ S₀).ker := by
      rw [h]
      trivial
    exact hx (by simpa [Subgroup.mem_prod] using h1)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
