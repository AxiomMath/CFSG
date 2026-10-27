module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.16)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.16) -/


public theorem section14_theorem_14_16_mul_lt_two_geom_quotient
    {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    p * q < 2 * ((p ^ q - 1) / (p - 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsum : p * q < 2 * (∑ k ∈ Finset.range q, p ^ k) := by
    refine Nat.le_induction ?base ?step q hq.two_le
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num
      omega
    · intro n hn ih
      rw [Finset.sum_range_succ, Nat.mul_succ]
      have hp_le_pow : p ≤ p ^ n := Nat.le_self_pow (by omega : n ≠ 0) p
      omega
  simpa [Nat.geomSum_eq hp2 q] using hsum

public theorem section14_theorem_14_16_case_a_contradiction_of_x_lower
    {p q u h x : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hu : u = (p ^ q - 1) / (p - 1))
    (hh : h = u * x)
    (hx : 2 * p * q < x)
    (hineq :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ)) :
    False := by
  have hpq_pos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hgeom_gt : p * q < 2 * u := by
    rw [hu]
    exact section14_theorem_14_16_mul_lt_two_geom_quotient hp hq
  have hu_pos : 0 < u := by omega
  have h_h_lower : 2 * p * q * u < h := by
    rw [hh]
    have hmul := Nat.mul_lt_mul_of_pos_left hx hu_pos
    nlinarith
  have hsub_lower : 2 * p * q * u ≤ h - 1 := by omega
  have hleft :
      ((2 * u : ℕ) : ℝ) ≤
        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) := by
    have hden_pos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
      exact_mod_cast hpq_pos
    have hcast :
        ((2 * p * q * u : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) =
          ((2 * u : ℕ) : ℝ) := by
      field_simp [ne_of_gt hden_pos]
      norm_num [mul_assoc, mul_left_comm, mul_comm]
    rw [← hcast]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hsub_lower) (by positivity)
  have hright : ((p * q - 1 : ℕ) : ℝ) < (p * q : ℝ) := by
    have : p * q - 1 < p * q := by omega
    exact_mod_cast this
  have hlt : ((2 * u : ℕ) : ℝ) < (p * q : ℝ) :=
    lt_of_le_of_lt (le_trans hleft hineq) hright
  have hgt : (p * q : ℝ) < ((2 * u : ℕ) : ℝ) := by
    exact_mod_cast hgeom_gt
  linarith

public theorem section14_theorem_14_16_case_b_numeric_of_formula
    {p q u v : ℕ}
    (hu : u = (p ^ q - 1) / (p - 1))
    (hv : v = (q ^ p - 1) / (q - 1))
    (hq : q = 3)
    (hp : p = 5) :
    u = 31 ∧ v = 121 := by
  subst q
  subst p
  norm_num at hu hv
  exact ⟨hu, hv⟩

public theorem section14_theorem_14_16_case_b_ratio_chain
    {p q u v h x : ℕ}
    (hq : q = 3)
    (hp : p = 5)
    (hu : u = 31)
    (hv : v = 121)
    (hh : h = u * x)
    (hx : 2 * p * q < x) :
    ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
        ((v - 1 : ℕ) : ℝ) / (p : ℝ) ∧
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  subst q
  subst p
  subst u
  subst v
  norm_num at hx
  have hx31 : 31 ≤ x := by omega
  have hh' : h = 31 * x := by simpa using hh
  have hsub : 960 ≤ h - 1 := by
    rw [hh']
    omega
  constructor
  · have hleft : (64 : ℝ) ≤ ((h - 1 : ℕ) : ℝ) / 15 := by
      have hcast : (960 : ℝ) ≤ ((h - 1 : ℕ) : ℝ) := by
        exact_mod_cast hsub
      nlinarith
    linarith
  · norm_num

public def section14_theorem_14_16_case_b_signed_expansion_data
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βLτ φτ ψτ : Section1.ClassFunction G) : Prop :=
  (∀ i j, Section1.scalarProduct G (η i j) ψτ = 0) ∧
    Section1.scalarProduct G φτ ψτ = 0 ∧
    Section1.scalarProduct G (Section1.conjugateCharacter φτ) ψτ = 0 ∧
    ∃ ε : Fin q → Fin p → ℤ,
      (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        (βLτ =
          (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - φτ ∨
          βLτ =
            (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) +
              Section1.conjugateCharacter φτ)

public def section14_theorem_14_16_case_b_signed_remainder_data
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βLτ φτ ψτ : Section1.ClassFunction G) : Prop :=
  (∀ i j, Section1.scalarProduct G (η i j) ψτ = 0) ∧
    Section1.scalarProduct G φτ ψτ = 0 ∧
    Section1.scalarProduct G (Section1.conjugateCharacter φτ) ψτ = 0 ∧
    ∃ ε : Fin q → Fin p → ℤ,
      (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : Section1.ClassFunction G,
          Section3.IsSignedIrreducibleCharacter χ ∧
            βLτ =
              (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - χ ∧
            (Section1.scalarProduct G χ φτ = 1 ∨
              Section1.scalarProduct G χ (Section1.conjugateCharacter φτ) = -1)

public def section14_theorem_14_16_case_b_norm_one_remainder_data
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βLτ φτ ψτ : Section1.ClassFunction G) : Prop :=
  (∀ i j, Section1.scalarProduct G (η i j) ψτ = 0) ∧
    Section1.scalarProduct G φτ ψτ = 0 ∧
    Section1.scalarProduct G (Section1.conjugateCharacter φτ) ψτ = 0 ∧
    ∃ ε : Fin q → Fin p → ℤ,
      (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : Section1.ClassFunction G,
          Theory.Character.IsVirtualCharacter χ ∧
            Section1.scalarProduct G χ χ = 1 ∧
            βLτ =
              (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - χ ∧
            (Section1.scalarProduct G χ φτ = 1 ∨
              Section1.scalarProduct G χ (Section1.conjugateCharacter φτ) = -1)

public def section14_theorem_14_16_case_b_post_coefficients_data
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βLτ φτ ψτ : Section1.ClassFunction G) : Prop :=
  (∀ i j, Section1.scalarProduct G (η i j) ψτ = 0) ∧
    ∃ ε : Fin q → Fin p → ℤ,
      (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : Section1.ClassFunction G,
          Theory.Character.IsVirtualCharacter χ ∧
            Section1.scalarProduct G χ χ = 1 ∧
            βLτ =
              (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - χ ∧
            (Section1.scalarProduct G χ φτ = 1 ∨
              Section1.scalarProduct G χ (Section1.conjugateCharacter φτ) = -1)


public theorem section14_theorem_14_16_case_b_signed_remainder_data_of_norm_one
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    {βLτ φτ ψτ : Section1.ClassFunction G}
    (hnorm :
      section14_theorem_14_16_case_b_norm_one_remainder_data η βLτ φτ ψτ) :
    section14_theorem_14_16_case_b_signed_remainder_data η βLτ φτ ψτ := by
  rcases hnorm with
    ⟨horth_eta, horth_phi, horth_phibar, ε, hεsign,
      χ, hχVirt, hχSelf, hβrem, hsp⟩
  have hχSigned : Section3.IsSignedIrreducibleCharacter χ :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hχVirt hχSelf
  exact ⟨horth_eta, horth_phi, horth_phibar, ε, hεsign,
    χ, hχSigned, hβrem, hsp⟩

public theorem section14_theorem_14_16_case_b_signed_expansion_data_of_remainder
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    {βLτ φτ ψτ : Section1.ClassFunction G}
    (hφτ : Section3.IsSignedIrreducibleCharacter φτ)
    (hrem :
      section14_theorem_14_16_case_b_signed_remainder_data η βLτ φτ ψτ) :
    section14_theorem_14_16_case_b_signed_expansion_data η βLτ φτ ψτ := by
  rcases hrem with
    ⟨horth_eta, horth_phi, horth_phibar, ε, hεsign,
      χ, hχSigned, hβrem, hsp⟩
  exact ⟨horth_eta, horth_phi, horth_phibar, ε, hεsign,
    section14_expansion_alternative_of_signed_remainder hχSigned hφτ
      hβrem hsp⟩

public theorem section14_scalarProduct_signed_eta_sum_left_eq_zero
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    {ψτ : Section1.ClassFunction G}
    (ε : Fin q → Fin p → ℤ)
    (horth_eta : ∀ i j, Section1.scalarProduct G (η i j) ψτ = 0) :
    Section1.scalarProduct G
      (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) ψτ = 0 := by
  have hsum_fun :
      (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j) :
          Section1.ClassFunction G) =
        (fun g => ∑ i : Fin q, ∑ j : Fin p,
          ((ε i j : ℂ) • η i j) g) := by
    ext g
    simp
  rw [hsum_fun]
  rw [Section1.scalarProduct_fintype_sum_left]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_left]
  apply Finset.sum_eq_zero
  intro j _hj
  change Section1.scalarProduct G (((ε i j : ℂ) • η i j)) ψτ = 0
  rw [Section1.scalarProduct_smul_left, horth_eta i j]
  simp

public theorem section14_conjugate_eta_orthogonal_of_etaData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    {ψτ : Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η)
    (horth : ∀ i j, Section1.scalarProduct G ψτ (η i j) = 0) :
    ∀ i j,
      Section1.scalarProduct G (Section1.conjugateCharacter ψτ) (η i j) = 0 := by
  classical
  intro i j
  have hconjOrth :
      Section1.scalarProduct G ψτ (Section1.conjugateCharacter (η i j)) = 0 := by
    rcases section14_eta_conjugate_entry_of_etaData
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (heta := heta) i j with
      ⟨i', j', hconj⟩
    rw [← hconj]
    exact horth i' j'
  have hconjSwap :
      Section1.scalarProduct G (Section1.conjugateCharacter ψτ) (η i j) =
        star (Section1.scalarProduct G ψτ
          (Section1.conjugateCharacter (η i j))) := by
    simp [Section1.scalarProduct, Section1.conjugateCharacter]
  rw [hconjSwap, hconjOrth]
  simp

public theorem section14_theorem_14_16_case_b_expansion_contradiction
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    {βLτ φτ ψτ : Section1.ClassFunction G}
    (hsp : Section1.scalarProduct G βLτ ψτ ≠ 0)
    (hdata :
      section14_theorem_14_16_case_b_signed_expansion_data η βLτ φτ ψτ) :
    False := by
  rcases hdata with
    ⟨horth_eta, horth_phi, horth_phibar, ε, _hεsign, hβ | hβ⟩
  · apply hsp
    have hsum_zero :
        Section1.scalarProduct G
          (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) ψτ = 0 :=
      section14_scalarProduct_signed_eta_sum_left_eq_zero ε horth_eta
    rw [hβ, Section5.scalarProduct_sub_left, hsum_zero, horth_phi]
    simp
  · apply hsp
    have hsum_zero :
        Section1.scalarProduct G
          (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) ψτ = 0 :=
      section14_scalarProduct_signed_eta_sum_left_eq_zero ε horth_eta
    rw [hβ, Section1.scalarProduct_add_left, hsum_zero, horth_phibar]
    simp

public theorem section14_theorem_14_16_x_gt_two_mul_of_decomp_odd
    {p q x n : ℕ}
    (hpOdd : Odd p)
    (hqOdd : Odd q)
    (hxn : x = 1 + n * (p * q))
    (hxOdd : Odd x)
    (hxne : x ≠ 1) :
    2 * p * q < x := by
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hxne
    rw [hxn, hn0]
    simp
  have hpqOdd : Odd (p * q) := hpOdd.mul hqOdd
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    subst n
    have hx_eq : x = 1 + p * q := by
      simpa using hxn
    have hxEven : Even x := by
      rw [hx_eq]
      exact Odd.add_odd odd_one hpqOdd
    exact Nat.not_even_iff_odd.mpr hxOdd hxEven
  have hn_ge_two : 2 ≤ n := by omega
  have hle : 2 * p * q ≤ n * (p * q) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (p * q) hn_ge_two
  have hlt : n * (p * q) < 1 + n * (p * q) := by
    simp [Nat.add_comm]
  rw [hxn]
  exact lt_of_le_of_lt hle hlt

public theorem section14_theorem_14_16_x_gt_two_mul_of_mod_odd
    {p q x : ℕ}
    (hpOdd : Odd p)
    (hqOdd : Odd q)
    (hmod : x % (p * q) = 1)
    (hxOdd : Odd x)
    (hxne : x ≠ 1) :
    2 * p * q < x := by
  let n := x / (p * q)
  have hxn : x = 1 + n * (p * q) := by
    have hx_eq : 1 + (p * q) * (x / (p * q)) = x := by
      simpa [hmod] using (Nat.mod_add_div x (p * q))
    simpa [n, Nat.mul_comm] using hx_eq.symm
  exact section14_theorem_14_16_x_gt_two_mul_of_decomp_odd
    hpOdd hqOdd hxn hxOdd hxne

public theorem section14_theorem_14_16_u_mod_p_eq_one
    {p q u : ℕ}
    (hp : Nat.Prime p)
    (hqpos : 0 < q)
    (hu : u = (p ^ q - 1) / (p - 1)) :
    u % p = 1 := by
  rw [hu]
  exact section14_theorem_14_15_geom_quotient_mod_p_eq_one hp hqpos

public theorem section14_theorem_14_16_x_mod_mul_of_mods
    {p q x : ℕ}
    (hpq : Nat.Coprime p q)
    (hp : 1 < p)
    (hq : 1 < q)
    (hxp : x % p = 1)
    (hxq : x % q = 1) :
    x % (p * q) = 1 := by
  have hxpMod : x ≡ 1 [MOD p] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hp] using hxp
  have hxqMod : x ≡ 1 [MOD q] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hq] using hxq
  have hxMod : x ≡ 1 [MOD p * q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp ⟨hxpMod, hxqMod⟩
  rw [Nat.ModEq] at hxMod
  have hpq_gt : 1 < p * q := by nlinarith
  simpa [Nat.mod_eq_of_lt hpq_gt] using hxMod

public theorem section14_theorem_14_16_x_ne_one_of_h_eq_u_mul
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H M : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d h x : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h1413 : hypothesis_14_13_statement L M H h)
    (hHU : H ≠ U)
    (hh : h = u * x) :
    x ≠ 1 := by
  intro hx1
  rcases section14_theorem_14_5_pf13_17_inputs hctx h143 with
    ⟨_htypeII, _hfrobLH, hUH, _hcomp⟩
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hccard, _hd,
      hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rw [hUcard, hc_one, Nat.mul_one]
  have hHcard_eq : Nat.card H = u := by
    have h_hu : h = u := by
      simpa [hx1] using hh
    rw [h1413.2] at h_hu
    exact h_hu
  have hUH_eq : U = H :=
    Subgroup.eq_of_le_of_card_ge hUH (by rw [hHcard_eq, hUcard_eq])
  exact hHU hUH_eq.symm

public theorem section14_theorem_14_16_relIndex_eq_mul_of_theorem_14_5_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h145 : theorem_14_5_data L H W1 W2 Q) :
    H.relIndex L = p * q := by
  classical
  rcases h145 with ⟨y, hyQ, hsemi⟩
  have hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsource with
    ⟨hcase, _hSTypeP, _hTTypeP, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  rcases Section13.theorem_13_16 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hnormW1, hcentW1⟩
  have hycent : y ∈ Subgroup.centralizer (W1 : Set G) := by
    have hySup : y ∈ Q ⊔ W2 := (show Q ≤ Q ⊔ W2 from le_sup_left) hyQ
    have hyCentIn : y ∈ subgroupCentralizerIn (⊤ : Subgroup G) W1 := by
      simpa [hcentW1] using hySup
    exact hyCentIn.2
  have hrel : H.relIndex L = Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hcard :
      Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) = q * p := by
    calc
      Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) =
          Nat.card W1 * Nat.card W2 :=
        section14_card_sup_conjBy_eq_mul_of_directProduct_of_mem_centralizer
          hprod hycent
      _ = q * p := by rw [hq_card, hp_card]
  calc
    H.relIndex L = Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) := hrel
    _ = p * q := by simpa [Nat.mul_comm] using hcard

public theorem section14_theorem_14_16_pf13_19_second_of_ratio
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {βL βS φ : Section1.ClassFunction G}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {p q u v h : ℕ}
    (hcard : h = Nat.card H)
    (hrel : H.relIndex L = p * q)
    (h1319 :
      Section13.theorem_13_19_alternativeData H βL βS φ ηNat p q u
        (H.relIndex L))
    (hbig :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
        ((v - 1 : ℕ) : ℝ) / (p : ℝ))
    (hratio :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
        ((u - 1 : ℕ) : ℝ) / (q : ℝ)) :
    (∀ j : ℕ, 0 < j → j < p →
        Section13.oddScalarProduct (Section1.scalarProduct G βL (ηNat 0 j))) ∧
      p ≤ H.relIndex L := by
  rcases h1319 with hfirst | hsecond
  · exfalso
    have hlt :
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) <
          ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) :=
      lt_trans hratio hbig
    have hle :
        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
          ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
      simpa [hcard, hrel] using hfirst.2
    exact (not_lt_of_ge hle) hlt
  · exact hsecond

public theorem section14_theorem_14_16_pf13_19_swapped_second_of_ratio
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {βL βT φ : Section1.ClassFunction G}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {p q v h : ℕ}
    (hcard : h = Nat.card H)
    (hrel : H.relIndex L = p * q)
    (h1319 :
      Section13.theorem_13_19_alternativeData H βL βT φ
        (fun i j => ηNat j i) q p v (H.relIndex L))
    (hbig :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
        ((v - 1 : ℕ) : ℝ) / (p : ℝ)) :
    (∀ i : ℕ, 0 < i → i < q →
        Section13.oddScalarProduct (Section1.scalarProduct G βL (ηNat i 0))) ∧
      q ≤ H.relIndex L := by
  rcases h1319 with hfirst | hsecond
  · exfalso
    have hle :
        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
          ((v - 1 : ℕ) : ℝ) / (p : ℝ) := by
      simpa [hcard, hrel] using hfirst.2
    exact (not_lt_of_ge hle) hbig
  · refine ⟨?_, hsecond.2⟩
    intro i hi hlt
    simpa using hsecond.1 i hi hlt

public theorem section14_theorem_14_16_tauL_betaL_vanishesOn_cyclicTISet_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ →
        Section3.VanishesOn (τL βL) (Section3.cyclicTISet W1 W2 W) := by
  intro hctx h143 hnotation
  rcases h143 with
    ⟨hLmax, _hNormU, hHMF, hTypeI, hDadeL, hPunctL, _h52b, hExtL,
      hφmem, _hφirr, hφdeg, hβS_eq, _hβT_eq, hβL_eq, _hDadeNotation⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis L H Smax P W1 Lfam RL
        τS τL τL₁ φ (τL₁ φ) (μ 0 1) (τL βL)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (H.relIndex L) := by
    refine ⟨hLmax, hHMF, hTypeI, rfl, hDadeL, hPunctL, hExtL,
      hφmem, hφdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τL hβL_eq
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam RL
    τS τT τL τL₁ φ (τL βL)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τL₁ φ)
    ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (H.relIndex L) hctx.1 hnotation hhyp
  have hβCFOn :
      Section2.CFOn L (Section12.typeIASet L H) βL := by
    rw [hβL_eq]
    exact section14_betaInput_CFOn_typeIASet hHMF hPunctL hφmem hφdeg
  intro g hg
  have hnotSupport :
      g ∉ Section2.dadeSupport (Section12.typeIASet L H) RL := by
    intro hgSupport
    have hgWconj :
        g ∈ section16ConjugatesOfSetBySet (W : Set G) Set.univ := by
      refine ⟨g, Section3.cyclicTISet_subset W1 W2 W hg, 1, Set.mem_univ _, ?_⟩
      simp
    exact (Set.disjoint_left.mp h1319.1 hgSupport) (Or.inr hgWconj)
  exact section14_betaM_tau_eq_zero_of_not_mem_dadeSupport
    (M := L) (K := H) (τM := τL) (βM := βL)
    (βMτ := τL βL) (R := RL) hDadeL hβCFOn rfl hnotSupport

public theorem section14_theorem_14_16_eta_tauM1_psi_orthogonal_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (Mfam : Finset (Section1.ClassFunction M))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
      section14EtaData Smax Tmax W W1 W2 p q η →
        ∀ i j, Section1.scalarProduct G (η i j) (τM₁ ψ) = 0 := by
  intro hctx h1410 heta i j
  classical
  have h1410_saved := h1410
  rcases h1410 with
    ⟨_hMmax, _hModd, _hNormV, _hKMF, _hTypeI, _hDadePkg, _hPunctM,
      _h52M, _hExtM, hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases heta with
    ⟨ωNat, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hnotation, hη⟩
  have hnotation_saved := hnotation
  rcases hnotation with
    ⟨hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNatData with ⟨_h31, _hqpos, _hppos, ωFin, _hωFin, hωeq⟩
  have hησ : η i j = σ (ωFin i j) := by
    calc
      η i j = ηNat (i : ℕ) (j : ℕ) := hη i j
      _ = σ (ωNat (i : ℕ) (j : ℕ)) :=
        hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt
      _ = σ (ωFin i j) := by
        simpa using congrArg σ (hωeq (i : ℕ) (j : ℕ) i.isLt j.isLt)
  have hforward :
      Section1.scalarProduct G (τM₁ ψ) (η i j) = 0 := by
    simpa [hησ] using
      section14_tauM1_mfam_sigma_orthogonal_of_pf13_19_source
        Smax Tmax W W1 W2 P Q U V C D M K V Sfam Tfam Mfam
        τS τT τM τM₁ ψ βM p q u v c d σ ωFin
        hnotation_saved hωeq hctx h1410_saved ψ hψmem i j
  have hswap := Section1.scalarProduct_star_swap (G := G) (τM₁ ψ) (η i j)
  have hstarzero :
      star (Section1.scalarProduct G (η i j) (τM₁ ψ)) = 0 := by
    simpa [hforward] using hswap
  simpa using congrArg star hstarzero

public theorem section14_tauL_betaL_isClassFunction_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax L H P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section1.IsClassFunction (τL βL) := by
  have hside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  exact Section1.isVirtualCharacter_isClassFunction
    (section14_typeI_core_ltr_beta_tau_virtual hside)

public theorem section14_tauL_betaL_self_scalar_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax L H P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section1.scalarProduct G (τL βL) (τL βL) =
      (H.relIndex L : ℂ) + 1 := by
  classical
  have hside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  rcases hside with
    ⟨_hHL, _hPunct, _h52, _hCoh, _hExt, _hφmem, _hφirr, _hφdeg,
      hβτ, hsetup⟩
  rcases hsetup with ⟨R, T, h76, hDadeAgree, h78, _hhalf⟩
  have hβNorm :
      Section5.cfNormSq (τL βL) =
        ((H.relIndex L + 1 : ℕ) : ℝ) := by
    rw [hβτ]
    have hnorm := Section7.theorem_7_8_beta_norm
      (A := Section12.typeIASet L H) (L := L) (H := H) (K := R)
      (T := T) (S := Lfam) (τ := τL) (ν := τL₁) (ζ := φ)
      h76 hDadeAgree h78
    rw [hnorm]
    norm_num
  have hβVirt : Theory.Character.IsVirtualCharacter (τL βL) := by
    exact section14_typeI_core_ltr_beta_tau_virtual
      ⟨_hHL, _hPunct, _h52, _hCoh, _hExt, _hφmem, _hφirr, _hφdeg,
        hβτ, ⟨R, T, h76, hDadeAgree, h78, _hhalf⟩⟩
  have hself :=
    section14_scalarProduct_self_eq_of_virtual_cfNormSq_nat
      (G := G) (χ := τL βL) (n := H.relIndex L + 1) hβVirt hβNorm
  norm_num at hself ⊢
  exact hself

public theorem section14_tauL1_conjugate_phi_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax L H P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section1.conjugateCharacter (τL₁ φ) =
      τL₁ (Section1.conjugateCharacter φ) := by
  classical
  rcases h143 with
    ⟨hLmax, _hNormU, hHMF, hTypeI, hDadeL, hPunctL,
      _h52L, hExtL, hφmem, _hφirr, _hφdeg, _hβS, _hβT,
      _hβL, _hDadeNotation⟩
  have h12 :
      Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  rcases Section12.theorem_12_2_a L H Lfam RL τL h12 with
    ⟨SX, hdata⟩
  rcases Section12.theorem_12_2_b L H Lfam SX RL τL h12 hdata with
    ⟨_R1, R, _hRdata, h52R⟩
  have h52 : Section5.hypothesis_5_2_statement Lfam τL := by
    rcases h52R with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
    exact ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hcoh : Section6.coherentExtension Lfam τL τL₁ := by
    rcases hExtL with ⟨hIso, hVirt, hAgree⟩
    exact ⟨hIso, hVirt, hAgree⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hIrr : ∀ χ : Section1.ClassFunction L, χ ∈ Lfam →
      Section1.IsIrreducibleCharacterOnGroup χ :=
    Section12.theorem_12_6_irreducible_of_frobenius L H Lfam RL τL h12 hfrob
  have hskew :
      Section1.conjugateCharacter
          (τL (φ - Section1.conjugateCharacter φ)) =
        -(τL (φ - Section1.conjugateCharacter φ)) :=
    Section12.conjugateCharacter_tau_sub_conjugate_of_hypothesis12
      L H Lfam SX RL τL h12 hdata hφmem
  exact
    section14_theorem_14_9_late_type_T1_tauT1_conjugate_source_bridge
      (Tmax := L) (T1T := Lfam) (τT := τL) (τT1 := τL₁)
      h52 hcoh hIrr hφmem hskew

public theorem section14_tauL1_phi_diff_conjugate_betaL_tau_scalar_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax L H P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    Section1.scalarProduct G
        ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ)) (τL βL) =
      -1 := by
  classical
  have hside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  rcases h143 with
    ⟨hLmax, _hNormU, hHMF, hTypeI, hDadeL, hPunctL,
      _h52L, hExtL, hφmem, hφirr, hφdeg, hβS, hβT,
      hβL, hDadeNotation⟩
  rcases hside with
    ⟨_hHLside, _hPunctSide, _h52Side, _hCohSide, _hExtSide,
      _hφmemSide, _hφirrSide, _hφdegSide, hβLτ_eq, hsetup⟩
  rcases hsetup with ⟨_R, _T, h76L, hDadeAgreeL, h78L, _hhalf⟩
  have hLOdd : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hHMF
  have hφbar_mem : Section1.conjugateCharacter φ ∈ Lfam :=
    Section12.puncturedInducedFamily_conjugate_mem L H Lfam hHnormal
      hPunctL φ hφmem
  have hφ_ne_bar : φ ≠ Section1.conjugateCharacter φ :=
    Section12.puncturedInducedFamily_ne_conjugate L H Lfam hHnormal
      hLOdd hPunctL φ hφmem
  rcases Section7.theorem_7_8_beta_zeta_coeff_int h76L hDadeAgreeL h78L with
    ⟨a, hβφ⟩
  have hφchar : Section1.IsCharacter φ :=
    Section12.isCharacter_of_isIrreducibleCharacterOnGroup hφirr
  have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hφbar_one_div :
      Section1.conjugateCharacter φ 1 / (H.relIndex L : ℂ) = 1 := by
    have hdegbar :
        Section1.degree (Section1.conjugateCharacter φ) =
          (H.relIndex L : ℂ) := by
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hφchar, hφdeg]
    have hval : Section1.conjugateCharacter φ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegbar
    rw [hval]
    field_simp [hrel_ne]
  have hβφbar :
      Section1.scalarProduct G (Section7.theorem_7_8_beta L H τL φ)
          (τL₁ (Section1.conjugateCharacter φ)) = (a : ℂ) := by
    have hraw :=
      Section7.theorem_7_8_beta_scalarProduct_of_mem
        h76L hDadeAgreeL h78L hβφ hφbar_mem
    have hne : Section1.conjugateCharacter φ ≠ φ := by
      intro h
      exact hφ_ne_bar h.symm
    rw [if_neg hne] at hraw
    simpa [hφbar_one_div] using hraw
  have hβdiff_right :
      Section1.scalarProduct G (τL βL)
          ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ)) = -1 := by
    calc
      Section1.scalarProduct G (τL βL)
          ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ)) =
          Section1.scalarProduct G (Section7.theorem_7_8_beta L H τL φ)
            ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ)) := by
            rw [hβLτ_eq]
      _ = Section1.scalarProduct G (Section7.theorem_7_8_beta L H τL φ)
            (τL₁ φ) -
          Section1.scalarProduct G (Section7.theorem_7_8_beta L H τL φ)
            (τL₁ (Section1.conjugateCharacter φ)) := by
            rw [Section5.scalarProduct_sub_right]
      _ = ((a : ℂ) - 1) - (a : ℂ) := by
            rw [hβφ, hβφbar]
      _ = -1 := by ring
  have hswap :=
    Section1.scalarProduct_star_swap (G := G) (τL βL)
      ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ))
  have hstar :
      star (Section1.scalarProduct G
        ((τL₁ φ) - τL₁ (Section1.conjugateCharacter φ)) (τL βL)) = -1 :=
    hswap.trans hβdiff_right
  have h := congrArg star hstar
  simpa using h

public theorem section14_hypothesis_14_10_data_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL) :
    hypothesis_14_10_data L H U Lfam τL τL₁ φ βL := by
  classical
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, hNormUleL, hHMF, hTypeI, hDadeL, hPunctL,
      h52L, hExtL, hφmem, hφirr, hφdeg, _hβS, _hβT,
      hβL, hDadeNotation⟩
  have hLodd : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  have hDadeSupport :
      ∀ tildeAL : Set G,
        Section10.section10TildeAData L H tildeAL →
          Section2.dadeSupport (Section12.typeIASet L H) RL = tildeAL := by
    intro tildeAL htilde
    rcases hDadeNotation with ⟨D, tildeA, tildeA0, tildeA1, h814⟩
    rcases htilde with ⟨Ms, A, A0, A1, D', tildeA0', tildeA1', R', h810', h814'⟩
    rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
    have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
    have hMsL : Section8.msChoiceSource L H H := by
      simpa [hMsLEq] using hMsLraw
    have h810 :
        Section8.notation_8_10_source_data L H H
          (Section12.typeIASet L H) (Section12.typeIASet L H)
          (Section8.a1Set H) :=
      Section12.notation_8_10_source_data_of_typeI_msChoice L H
        hLmax hHMF hTypeI hMsL
    have hsuppEq :
        Section2.dadeSupport (Section12.typeIASet L H) RL =
          Section2.dadeSupport (Section12.typeIASet L H) R' :=
      section14_typeI_dadeSupport_eq_of_notation_8_14
        L H H Ms
        (Section12.typeIASet L H) (Section12.typeIASet L H)
        (Section8.a1Set H) D tildeA tildeA0 tildeA1
        A A0 A1 D' tildeAL tildeA0' tildeA1'
        RL R' hTypeI h810 h814 h810' h814'
    have hsupp' :
        Section2.dadeSupport (Section12.typeIASet L H) R' = tildeAL :=
      section14_typeI_dadeSupport_eq_tildeA_of_notation_8_14
        L H Ms A A0 A1 D' tildeAL tildeA0' tildeA1' R'
        hTypeI h810' h814'
    exact hsuppEq.trans hsupp'
  exact ⟨hLmax, hLodd, hNormUleL, hHMF, hTypeI,
    ⟨RL, hDadeL, hDadeSupport, hDadeNotation⟩,
    hPunctL, h52L, hExtL, hφmem, hφirr, hφdeg, hβL⟩

public theorem section14_theorem_14_16_case_b_l_support_coherence_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ηNat : ℕ → ℕ → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      section14EtaData Smax Tmax W W1 W2 p q η →
      (∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)) →
      (∀ i j, Section1.scalarProduct G (τL₁ φ) (η i j) = 0) →
      (∀ j : ℕ, 0 < j → j < p →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τL βL) (ηNat 0 j))) →
      (∀ i : ℕ, 0 < i → i < q →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τL βL) (ηNat i 0))) →
      u = (p ^ q - 1) / (p - 1) →
      theorem_14_5_data L H W1 W2 Q →
      H ≠ U →
        ∃ ε : Fin q → Fin p → ℤ,
          (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
            ∃ χ : Section1.ClassFunction G,
              Theory.Character.IsVirtualCharacter χ ∧
                Section1.scalarProduct G χ χ = 1 ∧
                τL βL =
                  (∑ i : Fin q, ∑ j : Fin p,
                    ((ε i j : ℂ) • η i j)) - χ ∧
                (Section1.scalarProduct G χ (τL₁ φ) = 1 ∨
                  Section1.scalarProduct G χ
                    (Section1.conjugateCharacter (τL₁ φ)) = -1) := by
  intro hctx h143 heta hηNat_target hφ_eta hrow hcol _hu h145 _hneq
  classical
  have heta_saved := heta
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases heta with
    ⟨ωNat0, ηNat0, μ, ν, μsum, νsum, δ, δ', σ, hnotation, hηFin⟩
  have hnotation_saved := hnotation
  rcases hnotation with
    ⟨hωNatData, hσ, hηNat0_sigma, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  rcases hωNatData with ⟨h31, hqpos, hppos, ωFin, hωFin, hωNat_eq_fin⟩
  let i0 : Fin q := ⟨0, hqpos⟩
  let j0 : Fin p := ⟨0, hppos⟩
  have hη_sigma : ∀ i j, η i j = σ (ωFin i j) := by
    intro i j
    calc
      η i j = ηNat0 (i : ℕ) (j : ℕ) := hηFin i j
      _ = σ (ωNat0 (i : ℕ) (j : ℕ)) :=
          hηNat0_sigma (i : ℕ) (j : ℕ) i.isLt j.isLt
      _ = σ (ωFin i j) := by
          rw [hωNat_eq_fin (i : ℕ) (j : ℕ) i.isLt j.isLt]
  have hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat0 i j = ωFin ⟨i, hi⟩ ⟨j, hj⟩ := hωNat_eq_fin
  have hside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  have hβVirt : Theory.Character.IsVirtualCharacter (τL βL) :=
    section14_typeI_core_ltr_beta_tau_virtual hside
  have hσωVirt :
      ∀ i j, Theory.Character.IsVirtualCharacter (σ (ωFin i j)) := by
    intro i j
    exact hσ.2.1 (ωFin i j)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hωFin.irreducible i j))
  have hcoeffInt :
      ∀ i j, ∃ z : ℤ,
        Section1.scalarProduct G (τL βL) (σ (ωFin i j)) = (z : ℂ) := by
    intro i j
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hβVirt
      (hσωVirt i j)
  let coeff : Fin q → Fin p → ℤ := fun i j =>
    Classical.choose (hcoeffInt i j)
  have hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τL βL) (σ (ωFin i j)) := by
    intro i j
    exact (Classical.choose_spec (hcoeffInt i j)).symm
  have h1410L : hypothesis_14_10_data L H U Lfam τL τL₁ φ βL :=
    section14_hypothesis_14_10_data_of_hypothesis_14_3 hctx h143
  have hvanish :
      Section3.VanishesOn (τL βL) (Section3.cyclicTISet W1 W2 W) :=
    section14_theorem_14_16_tauL_betaL_vanishesOn_cyclicTISet_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d σ
      hctx h143 hnotation_saved
  let βproj : Section1.ClassFunction G :=
    τL βL -
      ∑ p : Fin q × Fin p,
        ((coeff p.1 p.2 : ℂ) • σ (ωFin p.1 p.2))
  have hβClass : Section1.IsClassFunction (τL βL) :=
    section14_tauL_betaL_isClassFunction_of_hypothesis_14_3 h143
  have h36projection :
      let coeffC : Fin q → Fin p → ℂ := fun i j =>
        Section1.scalarProduct G (τL βL) (σ (ωFin i j))
      let βC : Section1.ClassFunction G :=
        τL βL - ∑ p : Fin q × Fin p,
          coeffC p.1 p.2 • σ (ωFin p.1 p.2)
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ωFin σ (τL βL) βC coeffC h31 hωFin :=
    section14_hypothesis_3_6_of_projection
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ωFin) (σ := σ) (ψ := τL βL)
      (h31 := h31) (hω := hωFin) hσ hβClass hvanish
  have h36 :
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ωFin σ (τL βL) βproj
        (fun i j => (coeff i j : ℂ)) h31 hωFin := by
    simpa [βproj, hcoeffEq] using h36projection
  have hβprincipal :
      Section1.scalarProduct G (τL βL) (Section1.principalCharacter G) = 1 :=
    section14_betaM_tau_principal_scalar_of_hypothesis_14_10 h1410L
  rcases hσ with
    ⟨hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
  have hσ00 : σ (ωFin i0 j0) = Section1.principalCharacter G := by
    calc
      σ (ωFin i0 j0) = σ (Section1.principalCharacter W) := by
        rw [hωFin.principal]
      _ = Section1.principalCharacter G := hσprincipal
  have h00c : (coeff i0 j0 : ℂ) = 1 := by
    rw [hcoeffEq i0 j0, hσ00, hβprincipal]
  have hrowc : ∀ j, j ≠ j0 →
      Section13.oddScalarProduct (coeff i0 j : ℂ) := by
    intro j hj
    have hj_ne_zero : (j : ℕ) ≠ 0 := by
      intro hjzero
      apply hj
      ext
      simpa [j0] using hjzero
    have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj_ne_zero
    have hcoeff :
        (coeff i0 j : ℂ) =
          Section1.scalarProduct G (τL βL) (ηNat (0 : ℕ) (j : ℕ)) := by
      rw [hcoeffEq i0 j, ← hη_sigma i0 j, hηNat_target i0 j]
    simpa [hcoeff] using hrow (j : ℕ) hjpos j.isLt
  have hcolc : ∀ i, i ≠ i0 →
      Section13.oddScalarProduct (coeff i j0 : ℂ) := by
    intro i hi
    have hi_ne_zero : (i : ℕ) ≠ 0 := by
      intro hizero
      apply hi
      ext
      simpa [i0] using hizero
    have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi_ne_zero
    have hcoeff :
        (coeff i j0 : ℂ) =
          Section1.scalarProduct G (τL βL) (ηNat (i : ℕ) (0 : ℕ)) := by
      rw [hcoeffEq i j0, ← hη_sigma i j0, hηNat_target i j0]
    simpa [hcoeff] using hcol (i : ℕ) hipos i.isLt
  have h00 : coeff i0 j0 = 1 := by
    exact_mod_cast h00c
  have hrowOdd : ∀ j, j ≠ j0 → Odd (coeff i0 j) := by
    intro j hj
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i0 j : ℂ)) rfl (hrowc j hj)
  have hcolOdd : ∀ i, i ≠ i0 → Odd (coeff i j0) := by
    intro i hi
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i j0 : ℂ)) rfl (hcolc i hi)
  have hexchangec : ∀ i j, i ≠ i0 → j ≠ j0 →
      (coeff i j : ℂ) =
        (coeff i j0 : ℂ) + (coeff i0 j : ℂ) - (coeff i0 j0 : ℂ) := by
    intro i j hi hj
    exact Section3.proposition_3_7_particular
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ωFin) (σ := σ) (ψ := τL βL) (β := βproj)
      (a := fun i j => (coeff i j : ℂ)) h36 i j
  have hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0 := by
    intro i j hi hj
    exact section14_int_eq_of_complex_cast_eq (hexchangec i j hi hj)
  have hodd : ∀ i j, Odd (coeff i j) :=
    section14_odd_integer_coefficients_of_row_col_exchange
      i0 j0 coeff h00 hrowOdd hcolOdd hexchange
  have hrel : H.relIndex L = p * q :=
    section14_theorem_14_16_relIndex_eq_mul_of_theorem_14_5_data hctx h145
  have hoff :
      (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        ((H.relIndex L - 1 : ℕ) : ℝ) :=
    section14_theorem_14_11_2_off_base_bound_without_111_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H U Sfam Tfam Lfam
      τS τT τL τL₁ φ βL p q u v c d (H.relIndex L)
      σ ωFin i0 j0 hnotation_saved hωNat_eq_ω h31 hωFin
      ⟨hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
      coeff hcoeffEq hctx h1410L rfl
  have hrel_pos : 0 < H.relIndex L := by
    have hne : (H.subgroupOf L).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := L) (H := H.subgroupOf L)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hupper : H.relIndex L ≤ p * q := by
    exact le_of_eq hrel
  have hcoeffSumLe :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        (Fintype.card (Fin q × Fin p) : ℝ) :=
    section14_coefficients_normSq_sum_le_card_of_off_base_bound
      i0 j0 coeff h00c hrel_pos hupper hoff
  have hεsign : ∀ i j, coeff i j = 1 ∨ coeff i j = -1 :=
    section14_odd_integer_coefficients_sign_of_normSq_sum_le_card
      coeff hodd hcoeffSumLe
  let Sigma : Section1.ClassFunction G :=
    ∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • η i j)
  let Sigmaσ : Section1.ClassFunction G :=
    ∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • σ (ωFin i j))
  have hSigma_eq_sigma : Sigma = Sigmaσ := by
    ext g
    simp [Sigma, Sigmaσ, hη_sigma]
  let χ : Section1.ClassFunction G := Sigma - τL βL
  have hSigmaσVirt : Theory.Character.IsVirtualCharacter Sigmaσ := by
    dsimp [Sigmaσ]
    exact section14_int_weighted_sigma_double_sum_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W)
      ⟨hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
      (fun i j => hωFin.irreducible i j) coeff
  have hSigmaVirt : Theory.Character.IsVirtualCharacter Sigma := by
    rw [hSigma_eq_sigma]
    exact hSigmaσVirt
  have hχVirt : Theory.Character.IsVirtualCharacter χ := by
    dsimp [χ]
    exact Section3.isVirtualCharacter_sub hSigmaVirt hβVirt
  let sigmaFamily : Fin q × Fin p → Section1.ClassFunction G := fun ij =>
    σ (ωFin ij.1 ij.2)
  let coeffPair : Fin q × Fin p → ℤ := fun ij => coeff ij.1 ij.2
  let etaFamily : Fin q × Fin p → Section1.ClassFunction G := fun ij =>
    η ij.1 ij.2
  have hSigmaWeighted :
      Sigma =
        Section1.weightedFamilySum
          (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) etaFamily := by
    dsimp [Sigma, coeffPair, etaFamily]
    simpa using
      section14_double_sum_eq_weightedFamilySum
        (G := G) (W := G)
        (σ := (LinearMap.id :
          Section1.ClassFunction G →ₗ[ℂ] Section1.ClassFunction G))
        (ω := η) (coeff := coeff)
  have hSigmaσWeighted :
      Sigmaσ =
        Section1.weightedFamilySum
          (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily := by
    dsimp [Sigmaσ, coeffPair, sigmaFamily]
    exact section14_double_sum_eq_weightedFamilySum
      (G := G) (W := W) σ ωFin coeff
  have horthSigma : ∀ ij kl : Fin q × Fin p,
      Section1.scalarProduct G (sigmaFamily ij) (sigmaFamily kl) =
        if ij = kl then 1 else 0 := by
    intro ij kl
    exact
      (hσIso (ωFin ij.1 ij.2) (ωFin kl.1 kl.2)
        (hωFin.is_class ij.1 ij.2) (hωFin.is_class kl.1 kl.2)).trans
        (by simpa [sigmaFamily] using hωFin.orthonormal ij kl)
  have hcoeffPairEq : ∀ ij : Fin q × Fin p,
      (coeffPair ij : ℂ) =
        Section1.scalarProduct G (τL βL) (sigmaFamily ij) := by
    intro ij
    dsimp [coeffPair, sigmaFamily]
    exact hcoeffEq ij.1 ij.2
  have hcoeffSumExact :
      (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
          (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
        (H.relIndex L : ℝ) := by
    have hterm : ∀ ij : Fin q × Fin p,
        Complex.normSq (coeffPair ij : ℂ) = 1 := by
      intro ij
      rcases hεsign ij.1 ij.2 with hij | hij
      · simp [coeffPair, hij]
      · simp [coeffPair, hij]
    have hsum_card :
        (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
          (Fintype.card (Fin q × Fin p) : ℝ) := by
      calc
        (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
          (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun _ij => (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro ij _hij
            exact hterm ij
        _ = (Fintype.card (Fin q × Fin p) : ℝ) := by
            have hcard_qp :
                @Fintype.card (Fin q × Fin p)
                    (Fintype.ofFinite (Fin q × Fin p)) = q * p := by
              rw [← @Nat.card_eq_fintype_card (Fin q × Fin p)
                (Fintype.ofFinite (Fin q × Fin p))]
              simp
            simp
            exact_mod_cast hcard_qp
    have hcard : Fintype.card (Fin q × Fin p) = p * q := by
      simp [Fintype.card_prod, Nat.mul_comm]
    calc
      (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
          (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
        (Fintype.card (Fin q × Fin p) : ℝ) := hsum_card
      _ = (H.relIndex L : ℝ) := by
          rw [hcard, ← hrel]
  have hSigmaSelf : Section1.scalarProduct G Sigmaσ Sigmaσ = (H.relIndex L : ℂ) := by
    have hweighted :=
      section14_scalarProduct_weightedFamilySum_self_orthonormal_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p)
        (w := fun ij : Fin q × Fin p => (coeffPair ij : ℂ))
        (χ := sigmaFamily) horthSigma
    calc
      Section1.scalarProduct G Sigmaσ Sigmaσ =
          Section1.scalarProduct G
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily)
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily) := by
            rw [hSigmaσWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((H.relIndex L : ℝ) : ℂ) := by rw [hcoeffSumExact]
      _ = (H.relIndex L : ℂ) := by norm_num
  have hBetaSigma : Section1.scalarProduct G (τL βL) Sigmaσ = (H.relIndex L : ℂ) := by
    have hweighted :=
      section14_scalarProduct_right_weightedFamilySum_int_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p) (β := τL βL)
        (χ := sigmaFamily) (coeff := coeffPair) hcoeffPairEq
    calc
      Section1.scalarProduct G (τL βL) Sigmaσ =
          Section1.scalarProduct G (τL βL)
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily) := by
            rw [hSigmaσWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((H.relIndex L : ℝ) : ℂ) := by rw [hcoeffSumExact]
      _ = (H.relIndex L : ℂ) := by norm_num
  have hSigmaBeta : Section1.scalarProduct G Sigmaσ (τL βL) = (H.relIndex L : ℂ) := by
    have hweighted :=
      section14_scalarProduct_left_weightedFamilySum_int_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p) (β := τL βL)
        (χ := sigmaFamily) (coeff := coeffPair) hcoeffPairEq
    calc
      Section1.scalarProduct G Sigmaσ (τL βL) =
          Section1.scalarProduct G
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily)
            (τL βL) := by
            rw [hSigmaσWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((H.relIndex L : ℝ) : ℂ) := by rw [hcoeffSumExact]
      _ = (H.relIndex L : ℂ) := by norm_num
  have hBetaSelf :
      Section1.scalarProduct G (τL βL) (τL βL) =
        (H.relIndex L : ℂ) + 1 :=
    section14_tauL_betaL_self_scalar_of_hypothesis_14_3 h143
  have hχSelf : Section1.scalarProduct G χ χ = 1 := by
    change Section1.scalarProduct G (Sigma - τL βL) (Sigma - τL βL) = 1
    rw [hSigma_eq_sigma]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [hSigmaSelf, hSigmaBeta, hBetaSigma, hBetaSelf]
    ring
  have hφbar_eta :
      ∀ i j,
        Section1.scalarProduct G (Section1.conjugateCharacter (τL₁ φ)) (η i j) = 0 :=
    section14_conjugate_eta_orthogonal_of_etaData heta_saved hφ_eta
  have hφSigma : Section1.scalarProduct G (τL₁ φ) Sigma = 0 := by
    rw [hSigmaWeighted, Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro ij _hij
    rw [hφ_eta ij.1 ij.2]
    simp
  have hφbarSigma :
      Section1.scalarProduct G (Section1.conjugateCharacter (τL₁ φ)) Sigma = 0 := by
    rw [hSigmaWeighted, Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro ij _hij
    rw [hφbar_eta ij.1 ij.2]
    simp
  have hDiffSigma :
      Section1.scalarProduct G
          ((τL₁ φ) - Section1.conjugateCharacter (τL₁ φ)) Sigma = 0 := by
    rw [Section5.scalarProduct_sub_left, hφSigma, hφbarSigma]
    ring
  have hConjTau :
      Section1.conjugateCharacter (τL₁ φ) =
        τL₁ (Section1.conjugateCharacter φ) :=
    section14_tauL1_conjugate_phi_of_hypothesis_14_3 h143
  have hDiffBeta :
      Section1.scalarProduct G
        ((τL₁ φ) - Section1.conjugateCharacter (τL₁ φ)) (τL βL) = -1 := by
    rw [hConjTau]
    exact section14_tauL1_phi_diff_conjugate_betaL_tau_scalar_of_hypothesis_14_3
      h143
  have hDiffChi :
      Section1.scalarProduct G
        ((τL₁ φ) - Section1.conjugateCharacter (τL₁ φ)) χ = 1 := by
    change Section1.scalarProduct G
      ((τL₁ φ) - Section1.conjugateCharacter (τL₁ φ)) (Sigma - τL βL) = 1
    rw [Section5.scalarProduct_sub_right, hDiffSigma, hDiffBeta]
    ring
  have hφSigned :
      Section3.IsSignedIrreducibleCharacter (τL₁ φ) :=
    section14_phiTau_signedIrreducible_of_hypothesis_14_3 h143 rfl
  have hχφ :
      Section1.scalarProduct G χ (τL₁ φ) = 1 ∨
        Section1.scalarProduct G χ
          (Section1.conjugateCharacter (τL₁ φ)) = -1 :=
    section14_scalarProduct_sign_of_diff_scalar_eq_one
      hχVirt hχSelf hφSigned hDiffChi
  refine ⟨coeff, hεsign, χ, hχVirt, hχSelf, ?_, hχφ⟩
  dsimp [χ, Sigma]
  ext g
  simp

public theorem section14_theorem_14_16_case_b_post_coefficients_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ηNat : ℕ → ℕ → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            section14EtaData Smax Tmax W W1 W2 p q η →
            (∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)) →
            (∀ i j, Section1.scalarProduct G (τL₁ φ) (η i j) = 0) →
            (∀ j : ℕ, 0 < j → j < p →
              Section13.oddScalarProduct
                (Section1.scalarProduct G (τL βL) (ηNat 0 j))) →
            (∀ i : ℕ, 0 < i → i < q →
              Section13.oddScalarProduct
                (Section1.scalarProduct G (τL βL) (ηNat i 0))) →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              section14_theorem_14_16_case_b_post_coefficients_data
                η (τL βL) (τL₁ φ) (τM₁ ψ) := by
  intro hctx h143 h1410 h1413 heta hηNat hφ_eta hrow hcol hu h145 hneq
  have horth_eta :
      ∀ i j, Section1.scalarProduct G (η i j) (τM₁ ψ) = 0 :=
    section14_theorem_14_16_eta_tauM1_psi_orthogonal_source_bridge
      Smax Tmax W W1 W2 P Q U V C D M K Sfam Tfam Mfam
      τS τT τM τM₁ ψ βM p q u v c d η hctx h1410 heta
  rcases section14_theorem_14_16_case_b_l_support_coherence_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d η ηNat
      hctx h143 heta hηNat hφ_eta hrow hcol hu h145 hneq with
    ⟨ε, hεsign, χ, hχVirt, hχSelf, hβrem, hχφ⟩
  exact ⟨horth_eta, ε, hεsign, χ, hχVirt, hχSelf, hβrem, hχφ⟩

public theorem section14_theorem_14_16_case_b_norm_one_remainder_after_row_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ηNat : ℕ → ℕ → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            section14EtaData Smax Tmax W W1 W2 p q η →
            (∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)) →
            (∀ i j, Section1.scalarProduct G (τL₁ φ) (η i j) = 0) →
            (∀ j : ℕ, 0 < j → j < p →
              Section13.oddScalarProduct
                (Section1.scalarProduct G (τL βL) (ηNat 0 j))) →
            (∀ i : ℕ, 0 < i → i < q →
              Section13.oddScalarProduct
                (Section1.scalarProduct G (τL βL) (ηNat i 0))) →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              section14_theorem_14_16_case_b_norm_one_remainder_data
                η (τL βL) (τL₁ φ) (τM₁ ψ) := by
  intro hctx h143 h1410 h1413 heta hηNat hφ_eta hrow hcol hu h145 hneq
  rcases section14_theorem_14_16_case_b_post_coefficients_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h η ηNat hctx h143 h1410 h1413 heta hηNat hφ_eta
      hrow hcol hu h145 hneq with
    ⟨horth_eta, ε, hεsign, χ, hχVirt, hχSelf, hβrem, hχφ⟩
  rcases section14_theorem_14_14_source_estimate_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 with
    ⟨horth_phi, horth_phibar, _hnonzero, _hMestimate, _hLestimate⟩
  exact ⟨horth_eta, horth_phi, horth_phibar, ε, hεsign,
    χ, hχVirt, hχSelf, hβrem, hχφ⟩

public theorem section14_theorem_14_16_case_b_norm_one_remainder_of_pf13_19_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ηNat : ℕ → ℕ → Section1.ClassFunction G)
    (μNat : ℕ → ℕ → Section1.ClassFunction Smax)
    (νNat : ℕ → ℕ → Section1.ClassFunction Tmax) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            section14EtaData Smax Tmax W W1 W2 p q η →
            (∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)) →
            (∀ i j, Section1.scalarProduct G (τL₁ φ) (η i j) = 0) →
            Section13.theorem_13_19_alternativeData H (τL βL)
              (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μNat 0 1))
              (τL₁ φ) ηNat p q u (H.relIndex L) →
            Section13.theorem_13_19_alternativeData H (τL βL)
              (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - νNat 1 0))
              (τL₁ φ) (fun i j => ηNat j i) q p v (H.relIndex L) →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
                ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
                  ((v - 1 : ℕ) : ℝ) / (p : ℝ) →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
                  ((u - 1 : ℕ) : ℝ) / (q : ℝ) →
                section14_theorem_14_16_case_b_norm_one_remainder_data
                  η (τL βL) (τL₁ φ) (τM₁ ψ) := by
  intro hctx h143 h1410 h1413 heta hηNat hφ_eta h1319 h1319T hu h145 hneq hsp hbig hratio
  have hsecond_of_rel :
      H.relIndex L = p * q →
        (∀ j : ℕ, 0 < j → j < p →
            Section13.oddScalarProduct
              (Section1.scalarProduct G (τL βL) (ηNat 0 j))) ∧
          p ≤ H.relIndex L := by
    intro hrel
    exact section14_theorem_14_16_pf13_19_second_of_ratio
      h1413.2 hrel h1319 hbig hratio
  have hrel : H.relIndex L = p * q :=
    section14_theorem_14_16_relIndex_eq_mul_of_theorem_14_5_data hctx h145
  have hsecond :
      (∀ j : ℕ, 0 < j → j < p →
          Section13.oddScalarProduct
            (Section1.scalarProduct G (τL βL) (ηNat 0 j))) ∧
        p ≤ H.relIndex L :=
    hsecond_of_rel hrel
  have hsecondT :
      (∀ i : ℕ, 0 < i → i < q →
          Section13.oddScalarProduct
            (Section1.scalarProduct G (τL βL) (ηNat i 0))) ∧
        q ≤ H.relIndex L :=
    section14_theorem_14_16_pf13_19_swapped_second_of_ratio
      h1413.2 hrel h1319T hbig
  exact
    section14_theorem_14_16_case_b_norm_one_remainder_after_row_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h η ηNat hctx h143 h1410 h1413 heta hηNat hφ_eta
      hsecond.1 hsecondT.1 hu h145 hneq

public theorem section14_theorem_14_16_case_b_norm_one_remainder_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            section14EtaData Smax Tmax W W1 W2 p q η →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
                ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
                  ((v - 1 : ℕ) : ℝ) / (p : ℝ) →
                ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
                  ((u - 1 : ℕ) : ℝ) / (q : ℝ) →
                section14_theorem_14_16_case_b_norm_one_remainder_data
                  η (τL βL) (τL₁ φ) (τM₁ ψ) := by
  intro hctx h143 h1410 h1413 heta hu h145 hneq hsp hbig hratio
  rcases section14_theorem_13_19_eta_outputs_of_hypothesis_14_3 hctx h143 heta with
    ⟨ηNat, μNat, νNat, hηNat, hφ_eta, h1319, h1319T⟩
  exact
    section14_theorem_14_16_case_b_norm_one_remainder_of_pf13_19_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h η ηNat μNat νNat hctx h143 h1410 h1413 heta
      hηNat hφ_eta h1319 h1319T hu h145 hneq hsp hbig hratio

public theorem section14_theorem_14_16_x_congruence_and_case_b_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            section14EtaData Smax Tmax W W1 W2 p q η →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              2 < q ∧
                h % p = 1 ∧
                h % q = 1 ∧
                (∀ x : ℕ, h = u * x → Odd x) ∧
                (Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
                  ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
                    ((v - 1 : ℕ) : ℝ) / (p : ℝ) →
                  ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
                    ((u - 1 : ℕ) : ℝ) / (q : ℝ) →
                  section14_theorem_14_16_case_b_norm_one_remainder_data
                    η (τL βL) (τL₁ φ) (τM₁ ψ)) := by
  intro hctx h143 h1410 h1413 heta hu h145 hneq
  rcases section14_fixedPointFree_h_congruence_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 h145 with
    ⟨h2q, hhp, hhq, hxOddAll⟩
  exact ⟨h2q, hhp, hhq, hxOddAll,
    section14_theorem_14_16_case_b_norm_one_remainder_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h η hctx h143 h1410 h1413 heta hu h145 hneq⟩

public theorem section14_theorem_14_16_x_and_case_b_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            H ≠ U →
              (∃ x : ℕ, h = u * x ∧ 2 * p * q < x) ∧
                (Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
                  ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
                    ((v - 1 : ℕ) : ℝ) / (p : ℝ) →
                  ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
                    ((u - 1 : ℕ) : ℝ) / (q : ℝ) →
                  False) := by
  intro hctx h143 h1410 h1413 hu h145 hneq
  rcases section14EtaData_of_sourceData hctx.1 with ⟨η, heta⟩
  rcases section14_exists_h_eq_u_mul_of_hypotheses
      Smax Tmax W W1 W2 P Q U V C D L H M Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d h
      hctx h143 h1413 with
    ⟨x, hh⟩
  rcases section14_theorem_14_16_x_congruence_and_case_b_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h η hctx h143 h1410 h1413 heta hu h145 hneq with
    ⟨h2q, hhp, hhq, hxOddAll, hcaseBData⟩
  have hxOdd : Odd x := hxOddAll x hh
  rcases section14_context_primes_of_sourceData hctx with ⟨hpPrime, hqPrime⟩
  have hp_gt_two : 2 < p := lt_trans h2q hctx.2
  have hpOdd : Odd p :=
    hpPrime.odd_of_ne_two (ne_of_gt hp_gt_two)
  have hqOdd : Odd q :=
    hqPrime.odd_of_ne_two (ne_of_gt h2q)
  have hup : u % p = 1 :=
    section14_theorem_14_16_u_mod_p_eq_one hpPrime (by omega) hu
  have huq : u % q = 1 :=
    section14_theorem_14_15_u_mod_q_eq_one hctx h2q
  have hxp : x % p = 1 :=
    section14_theorem_14_15_x_mod_q_of_h_mod_q_and_u_mod_q
      hpPrime.one_lt hh hhp hup
  have hxq : x % q = 1 :=
    section14_theorem_14_15_x_mod_q_of_h_mod_q_and_u_mod_q
      hqPrime.one_lt hh hhq huq
  have hpq : Nat.Coprime p q :=
    (Nat.coprime_primes hpPrime hqPrime).mpr (ne_of_gt hctx.2)
  have hmod : x % (p * q) = 1 :=
    section14_theorem_14_16_x_mod_mul_of_mods
      hpq hpPrime.one_lt hqPrime.one_lt hxp hxq
  have hxne : x ≠ 1 :=
    section14_theorem_14_16_x_ne_one_of_h_eq_u_mul
      hctx h143 h1413 hneq hh
  have hcaseBSource :
      Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) >
          ((v - 1 : ℕ) : ℝ) / (p : ℝ) →
        ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
          ((u - 1 : ℕ) : ℝ) / (q : ℝ) →
        False := by
    intro hsp hbig hratio
    have hφτSigned :
        Section3.IsSignedIrreducibleCharacter (τL₁ φ) :=
      section14_phiTau_signedIrreducible_of_hypothesis_14_3
        (Smax := Smax) (Tmax := Tmax) (L := L) (H := H)
        (P := P) (Q := Q) (U := U) (W1 := W1) (W2 := W2)
        (Lfam := Lfam) (RL := RL) (τL := τL) (τL₁ := τL₁)
        (φ := φ) (μ01 := μ01) (ν10 := ν10)
        (βS := βS) (βT := βT) (βL := βL) h143 rfl
    have hdata :
        section14_theorem_14_16_case_b_signed_expansion_data
          η (τL βL) (τL₁ φ) (τM₁ ψ) :=
      section14_theorem_14_16_case_b_signed_expansion_data_of_remainder
        hφτSigned
        (section14_theorem_14_16_case_b_signed_remainder_data_of_norm_one
          (hcaseBData hsp hbig hratio))
    exact section14_theorem_14_16_case_b_expansion_contradiction hsp hdata
  exact ⟨⟨x, hh,
    section14_theorem_14_16_x_gt_two_mul_of_mod_odd
      hpOdd hqOdd hmod hxOdd hxne⟩, hcaseBSource⟩

public theorem section14_theorem_14_16_contradiction_with_formula_complement_alternative_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            u = (p ^ q - 1) / (p - 1) →
            theorem_14_5_data L H W1 W2 Q →
            theorem_14_14_alternative (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q h →
            H ≠ U →
              False := by
  intro hctx h143 h1410 h1413 hu h145 h1414 hneq
  rcases section14_theorem_14_16_x_and_case_b_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hu h145 hneq with
    ⟨hxpack, hcaseBSource⟩
  rcases h1414 with hcaseA | hcaseB
  · rcases hcaseA with ⟨_hsp, hineq⟩
    rcases hxpack with ⟨x, hh, hx⟩
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    exact section14_theorem_14_16_case_a_contradiction_of_x_lower
      hp hq hu hh hx hineq
  · rcases hcaseB with ⟨hsp, hq3, hp5⟩
    rcases section14_theorem_14_4_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
        hctx h143 with
      ⟨_hcaseT, hv⟩
    rcases section14_theorem_14_16_case_b_numeric_of_formula
        hu hv hq3 hp5 with
      ⟨hu31, hv121⟩
    rcases hxpack with ⟨x, hh, hx⟩
    rcases section14_theorem_14_16_case_b_ratio_chain
        hq3 hp5 hu31 hv121 hh hx with
      ⟨hbig, hratio⟩
    exact hcaseBSource hsp hbig hratio

public theorem section14_theorem_14_16_contradiction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            H ≠ U →
              False := by
  intro hctx h143 h1410 h1413 hneq
  have hu : u = (p ^ q - 1) / (p - 1) :=
    section14_theorem_14_15_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413
  have h145 : theorem_14_5_data L H W1 W2 Q :=
    section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have h1414 :
      theorem_14_14_alternative (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q h :=
    section14_theorem_14_14_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q u v c d h
      hctx h143 h1410 h1413 rfl rfl rfl rfl
  exact section14_theorem_14_16_contradiction_with_formula_complement_alternative_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d h hctx h143 h1410 h1413 hu h145 h1414 hneq

public theorem section14_theorem_14_16_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            H = U := by
  intro hctx h143 h1410 h1413
  by_contra hneq
  exact section14_theorem_14_16_contradiction_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d h hctx h143 h1410 h1413 hneq


end CFSG.Section14
