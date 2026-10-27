module

public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem commutator_mem_radQ_of_rho {d : hypSU h 2 0} (hd : d ∈ parP h) (hρ : rho h d = 1)
    {k : hypSU h 2 0} (hk : k ∈ parP h) : d * k * d⁻¹ * k⁻¹ ∈ radQ h := by
  have hdi := (parP h).inv_mem hd
  have hki := (parP h).inv_mem hk
  have hdk := (parP h).mul_mem hd hk
  have hdkd := (parP h).mul_mem hdk hdi
  refine mem_radQ_of_chi_rho h ((parP h).mul_mem hdkd hki) ?_ ?_
  · rw [chi_mul h hki, chi_mul h hdi, chi_mul h hk]
    have e1 := chi_mul_inv h hd
    have e2 := chi_mul_inv h hk
    linear_combination (chi h k * chi h k⁻¹) * e1 + e2
  · have e1 : rho h d⁻¹ = 1 := by
      have := rho_mul_inv h hd
      rwa [hρ, one_mul] at this
    rw [rho_mul h hdkd hki, rho_mul h hdk hdi, rho_mul h hd hk, hρ, e1, one_mul, mul_one,
      rho_mul_inv h hk]

theorem exists_torus_order_three (h : UnitaryFieldData 2 2 K) :
    ∃ d ∈ parP h, rho h d = 1 ∧ orderOf d = 3 := by
  have := h.finite
  have := h.charP
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card h.fixedField = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    norm_num
  obtain ⟨l, hl0, hl1⟩ : ∃ l : h.fixedField, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hcon
    have hall : ∀ l : h.fixedField, l = 0 ∨ l = 1 := fun l => by
      by_contra hl
      exact hcon ⟨l, fun e => hl (Or.inl e), fun e => hl (Or.inr e)⟩
    have hle : Fintype.card h.fixedField ≤ Fintype.card Bool :=
      Fintype.card_le_of_surjective (fun b : Bool => if b then (1 : h.fixedField) else 0)
        (fun l => by
          rcases hall l with rfl | rfl
          · exact ⟨false, rfl⟩
          · exact ⟨true, rfl⟩)
    rw [hcard, Fintype.card_bool] at hle
    omega
  have hl3 : l ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one l hl0
    rwa [hcard] at this
  have ha0 : (l : K) ≠ 0 := fun e => hl0 (Subtype.ext e)
  have ha1 : (l : K) ≠ 1 := fun e => hl1 (Subtype.ext e)
  have hbar : h.bar (l : K) = l := (h.mem_fixedField).mp l.2
  have ha3 : (l : K) ^ 3 = 1 := by
    have := congrArg (fun x : h.fixedField => (x : K)) hl3
    simpa using this
  obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU (r := 2) (ε := 0) h ![Units.mk0 (l : K) ha0, 1]
    (d := fun k => k.elim0) (fun k => k.elim0)
    (by simp [torusRatio, Fin.prod_univ_two, hbar, ha0])
  set e := torusEntries h ![Units.mk0 (l : K) ha0, 1] (fun k : Fin 0 => k.elim0) with he
  have e1 : e ie1 = l := rfl
  have e2 : e ie2 = 1 := rfl
  have e3 : e if1 = (l : K)⁻¹ := by
    change (h.bar (l : K))⁻¹ = _
    rw [hbar]
  have e4 : e if2 = 1 := by
    change (h.bar (1 : K))⁻¹ = 1
    rw [map_one, inv_one]
  have hE : ∀ i j, ((g : GL Ix K) : Matrix Ix Ix K) i j = if i = j then e i else 0 := by
    intro i j
    rw [hg, diagonal_apply]
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [mem_parP_iff]
    intro a ha
    simp [hE, ha]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rho, hE, e2, e4]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · apply hypSU_ext
      change ((((g : hypSU h 2 0) ^ 3 : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = 1
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      rcases ix_cases i with rfl | rfl | rfl | rfl
      · simp [e1, ha3]
      · simp [e2]
      · simp [e3, inv_pow, ha3]
      · simp [e4]
    · intro h1
      have := hE ie1 ie1
      simp only [h1, e1, ite_true] at this
      exact ha1 (by simpa using this.symm)

theorem factX3ParabolicU4_holds : FactX3ParabolicU4 := by
  intro Y _ T M₁ M hY hpair hsp
  obtain ⟨-, K, _, h, ψ, hψ, -, -, hMY, hcore, hO⟩ := recog_of (m := 2) le_rfl hY hpair hsp
  obtain ⟨d, hdP, hdρ, hd3⟩ := exists_torus_order_three h
  refine ⟨ψ d, ?_, ?_, ?_⟩
  · have hmem : ψ d ∈ M ⊓ ψ.range := by
      rw [hMY]
      exact Subgroup.mem_map_of_mem ψ hdP
    exact hmem.1
  · rw [orderOf_injective ψ hψ, hd3]
  · intro k hk
    rw [hcore] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    rw [hO]
    refine ⟨d * k₀ * d⁻¹ * k₀⁻¹,
      commutator_mem_radQ_of_rho h hdP hdρ (perfectCore_le (parP h) hk₀), ?_⟩
    simp [map_mul, map_inv]

end CFSG.Quasithin.H13.U4Par
