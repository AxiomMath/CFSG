module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

open scoped commutatorElement

namespace CFSG.Quasithin

open CFSG.ComponentClassification

namespace Gold14610

@[expose] def negOne (q : ℕ) : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨-1, by simp [Matrix.det_neg]⟩

theorem negOne_mul_self (q : ℕ) : negOne q * negOne q = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [negOne]

theorem negOne_comm (q : ℕ) (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    negOne q * A = A * negOne q := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [negOne]

theorem negOne_ne_one {q : ℕ} (h2 : (2 : ZMod q) ≠ 0) : negOne q ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h
  simp [negOne] at h1
  apply h2
  linear_combination (-1 : ZMod q) * h1

theorem orderOf_negOne {q : ℕ} (h2 : (2 : ZMod q) ≠ 0) : orderOf (negOne q) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negOne_mul_self q) (negOne_ne_one h2)

theorem normal_le_center_of_odd {B : Type*} [Group B] [Finite B] (hB : CFSG.IsQuasisimple B)
    {S : Subgroup B} (hS : S.Normal) (hodd : Odd (Nat.card S)) : S ≤ Subgroup.center B := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hB hS with h | h
  · exfalso
    subst h
    have hBodd : Odd (Nat.card B) := by simpa [Subgroup.card_top] using hodd
    have := CFSG.FeitThompson.isSolvable_of_odd_natCard B hBodd
    have := CFSG.LocalCores.isQuasisimple_nontrivial hB
    have := hB.1
    exact Group.IsPerfect.not_isSolvable B ‹_›
  · exact h

theorem mem_center_of_commutators_central {B : Type*} [Group B] (hperf : Group.IsPerfect B)
    {w : B} (h : ∀ b : B, ⁅w, b⁆ ∈ Subgroup.center B) : w ∈ Subgroup.center B := by
  have hle : commutator B ≤ Subgroup.centralizer {w} := by
    rw [commutator_def, Subgroup.commutator_le]
    intro b₁ _ b₂ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : ∀ b : B, w * b * w⁻¹ = b * ⁅w, b⁆ := fun b => by
      have h1 : w * b * w⁻¹ = ⁅w, b⁆ * b := by simp [commutatorElement_def, mul_assoc]
      rw [h1]
      exact ((Subgroup.mem_center_iff.mp (h b)) b).symm
    have hc : w * ⁅b₁, b₂⁆ * w⁻¹ = ⁅b₁, b₂⁆ := by
      calc w * ⁅b₁, b₂⁆ * w⁻¹ = ⁅w * b₁ * w⁻¹, w * b₂ * w⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅b₁ * ⁅w, b₁⁆, b₂ * ⁅w, b₂⁆⁆ := by rw [e, e]
        _ = ⁅b₁, b₂⁆ := by
          rw [CentralExtensions.commutator_mul_center_left _ _ _ (h b₁),
            CentralExtensions.commutator_mul_center_right _ _ _ (h b₂)]
    calc ⁅b₁, b₂⁆ * w = w * ⁅b₁, b₂⁆ * w⁻¹ * w := by rw [hc]
      _ = w * ⁅b₁, b₂⁆ := by group
  rw [Subgroup.mem_center_iff]
  intro b
  have hb : b ∈ Subgroup.centralizer {w} := by
    have : b ∈ commutator B := by rw [hperf.commutator_eq_top]; trivial
    exact hle this
  exact (Subgroup.mem_centralizer_singleton_iff).mp hb

theorem false_of_sl2_cover {Kg B : Type*} [Group Kg] [Group B] [Finite B] {q : ℕ}
    (h2 : (2 : ZMod q) ≠ 0) (hB : CFSG.IsQuasisimple B)
    (φ : Kg →* B) (hφ : Function.Surjective φ)
    (ψ : Kg →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (hψ : Function.Surjective ψ)
    (hcen : ∀ z ∈ Subgroup.center B, ¬ Even (orderOf z))
    (h₁ : ∀ x ∈ ψ.ker, ∃ n : ℕ, Odd n ∧ φ x ^ n = 1)
    (h₂ : ∀ x ∈ φ.ker, ∃ n : ℕ, Odd n ∧ ψ x ^ n = 1) : False := by
  obtain ⟨y, hy⟩ := hψ (negOne q)
  set S : Subgroup B := ψ.ker.map φ with hS
  have hSn : S.Normal := (MonoidHom.normal_ker ψ).map φ hφ
  have hSodd : Odd (Nat.card S) := by
    by_contra hnot
    have hev : 2 ∣ Nat.card S := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 hev
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp s.2
    obtain ⟨n, hn, hxn⟩ := h₁ x hx
    have hdvd : orderOf (s : B) ∣ n := orderOf_dvd_of_pow_eq_one (by rw [← hxs]; exact hxn)
    rw [Subgroup.orderOf_coe, hs] at hdvd
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hdvd)
  have hSc : S ≤ Subgroup.center B := normal_le_center_of_odd hB hSn hSodd
  have hw : φ y ∈ Subgroup.center B := by
    refine mem_center_of_commutators_central hB.1 fun b => ?_
    obtain ⟨x, rfl⟩ := hφ b
    refine hSc ⟨y * x * y⁻¹ * x⁻¹, ?_, by simp [commutatorElement_def]⟩
    show y * x * y⁻¹ * x⁻¹ ∈ ψ.ker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hy]
    rw [negOne_comm q (ψ x)]
    group
  have hdvd : y ^ orderOf (φ y) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨n, hn, hyn⟩ := h₂ _ hdvd
  rw [map_pow, hy] at hyn
  have h2o : orderOf (negOne q) ∣ orderOf (φ y) * n :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hyn)
  rw [orderOf_negOne h2] at h2o
  have h2e : 2 ∣ orderOf (φ y) :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_left.mpr hn) h2o
  exact hcen _ hw (even_iff_two_dvd.mpr h2e)

end Gold14610

end CFSG.Quasithin
