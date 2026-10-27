module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6Aut

open Equiv

abbrev c : Perm (Fin 6) := swap 0 1 * swap 1 2

abbrev d : Perm (Fin 6) := swap 3 4 * swap 4 5

set_option maxRecDepth 100000 in
theorem inv_cen_c : ∀ u : Perm (Fin 6), u * u = 1 → u ≠ 1 → u * c = c * u →
    u = swap 3 4 ∨ u = swap 3 5 ∨ u = swap 4 5 := by decide

set_option maxRecDepth 100000 in
theorem inv_cen_d : ∀ u : Perm (Fin 6), u * u = 1 → u ≠ 1 → u * d = d * u →
    u = swap 0 1 ∨ u = swap 0 2 ∨ u = swap 1 2 := by decide

set_option maxRecDepth 100000 in
theorem swap23 : ∀ u : Perm (Fin 6), u * u = 1 → u * swap 0 1 = swap 0 1 * u →
    u * swap 4 5 = swap 4 5 * u → (u * swap 1 2) ^ 3 = 1 → (u * swap 3 4) ^ 3 = 1 →
    u = swap 2 3 := by decide

variable (σ : Perm (Fin 6) →* Perm (Fin 6))

theorem map_conj (g x : Perm (Fin 6)) : σ (g * x * g⁻¹) = σ g * σ x * (σ g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem map_inv_cen {x t : Perm (Fin 6)} (hσ : ∀ z, σ (σ z) = z) (hx : σ x = x) (ht : t * t = 1)
    (ht1 : t ≠ 1) (htx : t * x = x * t) :
    σ t * σ t = 1 ∧ σ t ≠ 1 ∧ σ t * x = x * σ t := by
  refine ⟨by rw [← map_mul, ht, map_one], fun h => ht1 ?_, by rw [← hx, ← map_mul, htx, map_mul]⟩
  rw [← hσ t, h, map_one]

theorem fix_34 (hσ : ∀ z, σ (σ z) = z) (hc : σ c = c) (hd : σ d = d) :
    σ (swap 3 4) = swap 3 4 ∧ σ (swap 4 5) = swap 4 5 := by
  have e45 : swap 4 5 = d * swap 3 4 * d⁻¹ := by decide
  have e35 : swap 3 5 = d * swap 4 5 * d⁻¹ := by decide
  have h45 : σ (swap 4 5) = d * σ (swap 3 4) * d⁻¹ := by rw [e45, map_conj, hd]
  have h35 : σ (swap 3 5) = d * σ (swap 4 5) * d⁻¹ := by rw [e35, map_conj, hd]
  obtain ⟨h1, h2, h3⟩ := map_inv_cen σ hσ hc (t := swap 3 4) (by decide) (by decide) (by decide)
  have hinv := hσ (swap 3 4)
  rcases inv_cen_c _ h1 h2 h3 with h | h | h
  · exact ⟨h, by rw [h45, h]; decide⟩
  · exfalso
    rw [h, h35, h45, h] at hinv
    exact absurd hinv (by decide)
  · exfalso
    rw [h, h45, h] at hinv
    exact absurd hinv (by decide)

theorem fix_01 (hσ : ∀ z, σ (σ z) = z) (hc : σ c = c) (hd : σ d = d) :
    σ (swap 0 1) = swap 0 1 ∧ σ (swap 1 2) = swap 1 2 := by
  have e12 : swap 1 2 = c * swap 0 1 * c⁻¹ := by decide
  have e02 : swap 0 2 = c * swap 1 2 * c⁻¹ := by decide
  have h12 : σ (swap 1 2) = c * σ (swap 0 1) * c⁻¹ := by rw [e12, map_conj, hc]
  have h02 : σ (swap 0 2) = c * σ (swap 1 2) * c⁻¹ := by rw [e02, map_conj, hc]
  obtain ⟨h1, h2, h3⟩ := map_inv_cen σ hσ hd (t := swap 0 1) (by decide) (by decide) (by decide)
  have hinv := hσ (swap 0 1)
  rcases inv_cen_d _ h1 h2 h3 with h | h | h
  · exact ⟨h, by rw [h12, h]; decide⟩
  · exfalso
    rw [h, h02, h12, h] at hinv
    exact absurd hinv (by decide)
  · exfalso
    rw [h, h12, h] at hinv
    exact absurd hinv (by decide)

theorem eq_of_fix_cd (hσ : ∀ z, σ (σ z) = z) (hc : σ c = c) (hd : σ d = d) (z : Perm (Fin 6)) :
    σ z = z := by
  obtain ⟨h34, h45⟩ := fix_34 σ hσ hc hd
  obtain ⟨h01, h12⟩ := fix_01 σ hσ hc hd
  have h23 : σ (swap 2 3) = swap 2 3 := by
    refine swap23 _ (by rw [← map_mul, swap_mul_self, map_one]) ?_ ?_ ?_ ?_
    · rw [← h01, ← map_mul, show swap 2 3 * swap 0 1 = swap 0 1 * swap (2 : Fin 6) 3 by decide,
        map_mul]
    · rw [← h45, ← map_mul, show swap 2 3 * swap 4 5 = swap 4 5 * swap (2 : Fin 6) 3 by decide,
        map_mul]
    · rw [← h12, ← map_mul, ← map_pow, show (swap 2 3 * swap 1 2) ^ 3 = (1 : Perm (Fin 6)) by
        decide, map_one]
    · rw [← h34, ← map_mul, ← map_pow, show (swap 2 3 * swap 3 4) ^ 3 = (1 : Perm (Fin 6)) by
        decide, map_one]
  have hgen : Set.EqOn σ (MonoidHom.id _)
      (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [h01, h12, h23, h34, h45]
  have := MonoidHom.eqOn_closureM hgen
  rw [Perm.mclosure_swap_castSucc_succ] at this
  exact this (Set.mem_univ z)

theorem eq_of_fix_sylow (hσ : ∀ z, σ (σ z) = z) {P : Subgroup (Perm (Fin 6))}
    (hP : Nat.card P = 9) (hfix : ∀ z ∈ P, σ z = z) (z : Perm (Fin 6)) : σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have hle9 : ∀ Q : Sylow 3 (Perm (Fin 6)), Nat.card Q ≤ 9 := fun Q => by
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    have hdvd := Subgroup.card_subgroup_dvd_card (Q : Subgroup (Perm (Fin 6)))
    rw [hk, hcard] at hdvd
    rw [hk]
    by_contra h
    have hk3 : 3 ≤ k := by
      by_contra h'
      interval_cases k <;> norm_num at h
    exact absurd ((pow_dvd_pow 3 hk3).trans hdvd) (by norm_num)
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPS' : (P : Subgroup _) = S :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [hP]; exact hle9 S)
  have hcp : ∀ x : Perm (Fin 6), x ^ 3 = 1 → x ≠ 1 → IsPGroup 3 (Subgroup.zpowers x) :=
    fun x hx hx1 => IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hx hx1)
  have hcd : c * d = d * c := by decide
  have hc3 : IsPGroup 3 ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers d) :=
    IsPGroup.to_sup_of_normal_right' (hcp c (by decide) (by decide))
      (hcp d (by decide) (by decide))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [(Commute.zpow_right hcd k).eq, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers d k))
  obtain ⟨S₀, hS₀⟩ := hc3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) S₀ S
  have hmem : ∀ x ∈ (S₀ : Subgroup (Perm (Fin 6))), g * x * g⁻¹ ∈ P := fun x hx => by
    rw [hPS', ← hg]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
  set τ : Perm (Fin 6) →* Perm (Fin 6) := (MulAut.conj g⁻¹).toMonoidHom.comp
    (σ.comp (MulAut.conj g).toMonoidHom) with hτ
  have hτv : ∀ x, τ x = g⁻¹ * σ (g * x * g⁻¹) * g := fun x => by
    simp [hτ, MulAut.conj_apply]
  have hτσ : ∀ x, τ (τ x) = x := fun x => by
    rw [hτv, hτv, show g * (g⁻¹ * σ (g * x * g⁻¹) * g) * g⁻¹ = σ (g * x * g⁻¹) by group, hσ]
    group
  have hτfix : ∀ x ∈ (S₀ : Subgroup (Perm (Fin 6))), τ x = x := fun x hx => by
    rw [hτv, hfix _ (hmem x hx)]; group
  have hz := eq_of_fix_cd τ hτσ (hτfix _ (hS₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))))
    (hτfix _ (hS₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))) (g⁻¹ * z * g)
  rw [hτv, show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hz
  calc σ z = g * (g⁻¹ * σ z * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hz]
    _ = z := by group

end CFSG.RankThree.PartTwo.Sec21.FF81.S6Aut
