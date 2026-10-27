module

import Mathlib.Algebra.Group.Subgroup.Pointwise

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.JFacts

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open

open scoped Pointwise

theorem false_of_conj_of_product {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ x y : K, x * y ≠ y * x) (k : K) (hk1 : k ≠ 1) (hk3 : MulAut.conj k ^ 3 = 1)
    (O J : Subgroup K) (hfix : ∀ x : K, x ∈ O ⊔ J ↔ MulAut.conj k x = x) (hdisj : O ⊓ J = ⊥)
    (hcomm : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x) (hO : Nat.Coprime (Nat.card O) 3)
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) : False := by
  have _hunused : O ⊓ J = ⊥ := hdisj
  have hcenter : Subgroup.center K = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have hx : x ∈ Subgroup.center K := by rw [h]; trivial
      exact hxy (Subgroup.mem_center_iff.mp hx y).symm
  have hk3pow : k ^ 3 = 1 := by
    have hmem : k ^ 3 ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : k ^ 3 * x * (k ^ 3)⁻¹ = x := by
        have h1 : MulAut.conj (k ^ 3) x = x := by rw [map_pow, hk3]; rfl
        simpa only [MulAut.conj_apply] using h1
      have hx' : k ^ 3 * x = x * k ^ 3 := by
        calc k ^ 3 * x = k ^ 3 * x * (k ^ 3)⁻¹ * k ^ 3 := by group
          _ = x * k ^ 3 := by rw [hx]
      exact hx'.symm
    rw [hcenter] at hmem
    simpa using hmem
  have hkord : orderOf k = 3 := orderOf_eq_prime hk3pow hk1
  have hk_mem : k ∈ O ⊔ J := (hfix k).mpr (by rw [MulAut.conj_apply]; group)
  have hOcent : O ≤ Subgroup.centralizer (J : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hOle : O ≤ Subgroup.normalizer (J : Set K) :=
    hOcent.trans (Subgroup.centralizer_le_normalizer (J : Set K))
  have hk_prod : k ∈ (O : Set K) * (J : Set K) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right O J hOle]
    simpa using hk_mem
  obtain ⟨o, hoO, j, hjJ, hoj⟩ := Set.mem_mul.mp hk_prod
  have hkJ : ∀ y ∈ J, k * y = y * k := by
    intro y hy
    have hy_fix : MulAut.conj k y = y := (hfix y).mp (Subgroup.mem_sup_right hy)
    rw [MulAut.conj_apply] at hy_fix
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [hy_fix]
  have hjcomm : ∀ y : J, j * (y : K) = (y : K) * j := by
    intro y
    have h1 : Commute o⁻¹ (y : K) :=
      (show Commute o (y : K) from hcomm o hoO (y : K) y.2).inv_left
    have h2 : Commute k (y : K) := hkJ (y : K) y.2
    have hj_eq : j = o⁻¹ * k := by rw [← hoj]; group
    rw [hj_eq]
    exact h1.mul_left h2
  have hjcenter : (⟨j, hjJ⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using (hjcomm y).symm
  have hj1 : j = 1 := by
    have hmem : (⟨j, hjJ⟩ : J) ∈ (⊥ : Subgroup J) := by
      rw [← center_eq_bot_of_modelJ J hJ]
      exact hjcenter
    have h1 : (⟨j, hjJ⟩ : J) = 1 := Subgroup.mem_bot.mp hmem
    simpa using congrArg Subtype.val h1
  have hkO : k ∈ O := by
    have : k = o := by rw [← hoj, hj1, mul_one]
    rw [this]; exact hoO
  have hdvd : 3 ∣ Nat.card O := by
    rw [← hkord]
    exact O.orderOf_dvd_natCard hkO
  have h33 : Nat.Coprime 3 3 := hO.coprime_dvd_left hdvd
  have h31 : (3 : ℕ) = 1 := (Nat.coprime_self 3).mp h33
  omega

end CFSG.StandardType.FF81.CatQ1
