module

public import CFSG.Timmesfeld.Bridge.RootClosureRankOne
public import CFSG.Timmesfeld.Bridge.RootStructR2DegenBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure RootDegen

variable {G : Type} [Group G] {D : Set G}

section SL2

open CFSG.Glauberman.Dickson

theorem splitTorus_conj_mem_upperUnipotent {F : Type*} [Field F] (a : Fˣ)
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ upperUnipotent F) :
    splitTorusSLHom F a * u * (splitTorusSLHom F a)⁻¹ ∈ upperUnipotent F := by
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := hg
    apply Subgroup.subset_closure
    refine ⟨(a : F) * t * (a : F), ?_⟩
    rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      splitTorusSLHom_coe, splitTorusSLHom_coe, ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  | one => simp
  | mul a' b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show splitTorusSLHom F a * a' * (splitTorusSLHom F a)⁻¹ *
        (splitTorusSLHom F a * b * (splitTorusSLHom F a)⁻¹) =
        splitTorusSLHom F a * (a' * b) * (splitTorusSLHom F a)⁻¹ by group] at this
  | inv a' _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (splitTorusSLHom F a * a' * (splitTorusSLHom F a)⁻¹)⁻¹ =
        splitTorusSLHom F a * a'⁻¹ * (splitTorusSLHom F a)⁻¹ by group] at this

theorem exists_splitTorus_weyl {F : Type*} [Field F] [CharP F 2] [Finite F]
    (hF : 4 ≤ Nat.card F) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ h : Matrix.SpecialLinearGroup (Fin 2) F, orderOf h = p ∧
      (∀ u ∈ lowerUnipotent F, h * u * h⁻¹ ∈ lowerUnipotent F) ∧
      (∀ u ∈ upperUnipotent F, h * u * h⁻¹ ∈ upperUnipotent F) ∧
      ∃ g ∈ lowerUnipotent F, ∃ u ∈ upperUnipotent F, u ≠ 1 ∧
        (g * u * g⁻¹) * h * (g * u * g⁻¹)⁻¹ = h⁻¹ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcardU : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  have hk' : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  have hodd : Odd (Nat.card F - 1) := by
    rw [hk']
    have hpos : 0 < (k : ℕ) := k.pos
    have : Even (2 ^ (k : ℕ)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    obtain ⟨j, hj⟩ := this
    have h1 : 1 ≤ 2 ^ (k : ℕ) := Nat.one_le_two_pow
    exact ⟨j - 1, by omega⟩
  set p := (Nat.card F - 1).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ Nat.card F - 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpdvd)
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [hcardU]; exact hpdvd)
  refine ⟨p, hpp, hp2, splitTorusSLHom F a, ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · rw [orderOf_injective _ splitTorusSLHom_injective a, ha]
  · exact splitTorus_conj_mem_lowerUnipotent a hu
  · exact splitTorus_conj_mem_upperUnipotent a hu
  · obtain ⟨g, hg, u, hu, hu1, hw⟩ := standardSplitWeylSL_eq_conj (F := F)
    refine ⟨g, hg, u, hu, hu1, ?_⟩
    rw [← hw, standardSplitWeylSL_conj, map_inv]

end SL2

end CFSG.Timmesfeld.Bridge
