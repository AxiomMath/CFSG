module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenRight

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Quasithin.H13.NF314ptA312
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312
open scoped Pointwise

theorem q_dvd_card_L2_leaf {q : ℕ} (hq : q.Prime) (hq2' : q ≠ 2) (hq2 : q % 2 = 1) :
    q ∣ q * (q ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ q * (q ^ 2 - 1) := by
    have hsq : q ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hq2]
    exact Dvd.dvd.mul_left (by omega) q
  have hmul : q * (q ^ 2 - 1) / 2 * 2 = q * (q ^ 2 - 1) := Nat.div_mul_cancel h2
  have hq2N : q ∣ q * (q ^ 2 - 1) / 2 * 2 := by
    rw [hmul]
    exact dvd_mul_right q _
  exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hq Nat.prime_two).mpr hq2') hq2N

theorem eq_of_dvd_smooth_leaf {q r : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) (hr : r.Prime) {a b c d : ℕ}
    (h : q ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * r) : q = r := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · exact (not_dvd_smooth (n := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) (a := a) (b := b) (c := c)
      (d := d) hq hq11 rfl h1).elim
  · exact (Nat.prime_dvd_prime_iff_eq hq hr).mp h1

theorem leafA312_holds :
    LeafA312 := by
  unfold LeafA312
  intro Q _ _ B₁ B₂ J q hq hq24 hB₁ hB₂ hB₁J hB₂J h₁ h₂
  have hq11 : 11 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  have hq2' : q ≠ 2 := by omega
  have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by omega
  have hS₁ : IsSimpleGroup (↥B₁ ⧸ CFSG.pCore 2 ↥B₁) := isSimpleGroup_of_isPSL hB₁
  have hc₁ : Nat.card (↥B₁ ⧸ CFSG.pCore 2 ↥B₁) = 168 := card_psl32 hB₁
  obtain ⟨k, hk⟩ := pCore_card_two_pow B₁
  have hcB₁ : Nat.card ↥B₁ = 168 * 2 ^ k := by
    rw [card_eq_quot_mul B₁, hc₁, hk]
  have hS₂ : IsSimpleGroup (↥B₂ ⧸ CFSG.pCore 2 ↥B₂) := isSimpleGroup_of_isPSL hB₂
  have hcQ₂ : Nat.card (↥B₂ ⧸ CFSG.pCore 2 ↥B₂) = q * (q ^ 2 - 1) / 2 :=
    card_psl2_odd hB₂ hq2
  have hN8 : q * (q ^ 2 - 1) / 2 % 8 = 4 := mod_eight_L2 hq8
  have hEven₂ : Even (Nat.card (↥B₂ ⧸ CFSG.pCore 2 ↥B₂)) := by
    rw [hcQ₂]
    exact even_iff_two_dvd.mpr (by omega)
  obtain ⟨j, hj⟩ := pCore_card_two_pow B₂
  have hqB₂ : q ∣ Nat.card ↥B₂ := by
    rw [card_eq_quot_mul B₂, hcQ₂, hj]
    exact dvd_mul_of_dvd_left (q_dvd_card_L2_leaf hq hq2' hq2) _
  by_cases hJ1 : B₁ = J
  ·
    have hB₂B₁ : B₂ ≤ B₁ := by
      rw [hJ1]
      exact hB₂J
    have hdiv : Nat.card ↥B₂ ∣ Nat.card ↥B₁ := Subgroup.card_dvd_of_le hB₂B₁
    rw [hcB₁] at hdiv
    have h7 : q ∣ 168 * 2 ^ k := dvd_trans hqB₂ hdiv
    have := p_eq_seven_of_dvd hq (by omega) h7
    omega
  by_cases hJ2 : B₂ = J
  ·
    have hB₁B₂ : B₁ ≤ B₂ := by
      rw [hJ2]
      exact hB₁J
    let ψ : ↥B₁ →* ↥B₂ ⧸ CFSG.pCore 2 ↥B₂ :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥B₂)).comp (Subgroup.inclusion hB₁B₂)
    have hcard1 : Nat.card (↥B₁ ⧸ ψ.ker) ∣ q * (q ^ 2 - 1) / 2 := by
      rw [← hcQ₂]
      exact card_dvd_of_injective (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ)
    have hV2 : Nat.card ψ.ker ∣ 2 ^ j := by
      have hmemV : ∀ x : ↥ψ.ker, Subgroup.inclusion hB₁B₂ x.1 ∈ CFSG.pCore 2 ↥B₂ := by
        intro x
        have hx : ψ x.1 = 1 := MonoidHom.mem_ker.mp x.2
        exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hB₁B₂ x.1)).mp hx
      let g : ↥ψ.ker →* ↥(CFSG.pCore 2 ↥B₂) :=
        { toFun := fun x => ⟨Subgroup.inclusion hB₁B₂ x.1, hmemV x⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hg : Function.Injective g := by
        intro x y hxy
        have h1 : Subgroup.inclusion hB₁B₂ x.1 = Subgroup.inclusion hB₁B₂ y.1 :=
          congrArg Subtype.val hxy
        exact Subtype.ext (Subgroup.inclusion_injective hB₁B₂ h1)
      have := card_dvd_of_injective g hg
      rw [hj] at this
      exact this
    have hB1 : Nat.card ↥B₁ = Nat.card ψ.ker * Nat.card (↥B₁ ⧸ ψ.ker) := by
      have := Subgroup.card_mul_index ψ.ker
      rw [Subgroup.index] at this
      exact this.symm
    rcases quot_dichotomy hS₁ ψ.ker with hd | hd
    ·
      rw [hc₁] at hd
      have h8 : 8 ∣ q * (q ^ 2 - 1) / 2 := dvd_trans (by norm_num) (dvd_trans hd hcard1)
      omega
    ·
      rw [hk] at hd
      have hdvd : Nat.card ↥B₁ ∣ 2 ^ j * 2 ^ k := by
        rw [hB1]
        exact Nat.mul_dvd_mul hV2 hd
      have h7B : 7 ∣ Nat.card ↥B₁ := by
        rw [hcB₁]
        exact Dvd.dvd.mul_right (by norm_num) _
      have h7 : 7 ∣ 2 ^ j * 2 ^ k := dvd_trans h7B hdvd
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
      · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
        norm_num at this
      · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
        norm_num at this
  ·
    have hR : ¬ 64 ∣ Nat.card ↥J := (gen_right_card hq hq24 hB₂ hB₂J h₂).resolve_left hJ2
    have hL := gen_left_card hB₁ hB₁J h₁
    have hdiv : Nat.card ↥B₂ ∣ Nat.card ↥J := Subgroup.card_dvd_of_le hB₂J
    have hqJ : q ∣ Nat.card ↥J := dvd_trans hqB₂ hdiv
    rcases hL with h | h64 | h2520 | h7560 | h58800 | h1876896 | h5630688 | h5663616 | h336
    · exact absurd h hJ1
    · exact (hR h64).elim
    · rw [h2520] at hqJ
      exact (not_dvd_2520 hq hq11 hqJ).elim
    · rw [h7560] at hqJ
      exact (not_dvd_7560 hq hq11 hqJ).elim
    · rw [h58800] at hqJ
      exact (not_dvd_smooth hq hq11 (show (58800 : ℕ) = 2 ^ 4 * 3 ^ 1 * 5 ^ 2 * 7 ^ 2 by norm_num)
        hqJ).elim
    ·
      rw [h1876896] at hqJ
      have e : (1876896 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 ^ 0 * 7 ^ 3 * 19 := by norm_num
      rw [e] at hqJ
      have := eq_of_dvd_smooth_leaf hq hq11 (by norm_num : Nat.Prime 19) hqJ
      omega
    ·
      rw [h5630688] at hqJ
      have e : (5630688 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 ^ 0 * 7 ^ 3 * 19 := by norm_num
      rw [e] at hqJ
      have := eq_of_dvd_smooth_leaf hq hq11 (by norm_num : Nat.Prime 19) hqJ
      omega
    ·
      rw [h5663616] at hqJ
      have e : (5663616 : ℕ) = 2 ^ 7 * 3 ^ 1 * 5 ^ 0 * 7 ^ 3 * 43 := by norm_num
      rw [e] at hqJ
      have := eq_of_dvd_smooth_leaf hq hq11 (by norm_num : Nat.Prime 43) hqJ
      omega
    ·
      have hinj : Function.Injective
          ((QuotientGroup.mk' (CFSG.oddCore ↥J)).comp (Subgroup.inclusion hB₂J) :
            ↥B₂ →* ↥J ⧸ CFSG.oddCore ↥J) := by
        rw [injective_iff_map_eq_one]
        intro b hb
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
        exact inter_oddCore_eq_one hB₂J hS₂ hEven₂ b hb
      have hdiv336 : Nat.card ↥B₂ ∣ 336 := by
        rw [← h336]
        exact card_dvd_of_injective _ hinj
      have hq336 : q ∣ 336 := dvd_trans hqB₂ hdiv336
      exact (not_dvd_smooth hq hq11 (show (336 : ℕ) = 2 ^ 4 * 3 ^ 1 * 5 ^ 0 * 7 ^ 1 by norm_num)
        hq336).elim

end CFSG.Quasithin.H13.NF314pt
