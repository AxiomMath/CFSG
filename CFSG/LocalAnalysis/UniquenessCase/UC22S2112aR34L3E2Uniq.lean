module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Uniq
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2UniqSU
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan Matrix Module CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped MatrixGroups

private theorem uc22s2112r34_ordA_ne_one_of_three_le {q n : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (hn : 3 ≤ n) : ordA (n - 1) q ≠ ordA 1 q := by
  have hdvd : q ^ 2 ∣ ordA (n - 1) q := by
    let C : ℕ := ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)
    let d : ℕ := Nat.gcd n (q - 1)
    have hdvdC : d ∣ C := by
      have h1 : d ∣ q - 1 := Nat.gcd_dvd_right _ _
      have h2 : q - 1 ∣ q ^ 2 - 1 := by
        simpa using Nat.sub_one_dvd_pow_sub_one q 2
      have h3 : q ^ 2 - 1 ∣ C := by
        show q ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)
        exact Finset.dvd_prod_of_mem (fun j => q ^ j - 1)
          (by simp only [Finset.mem_Icc]; omega)
      exact h1.trans (h2.trans h3)
    have hdvdnum : d ∣ q ^ ((n - 1) * n / 2) * C :=
      dvd_mul_of_dvd_right hdvdC _
    have hmul : ordA (n - 1) q * d = q ^ ((n - 1) * n / 2) * C := by
      rw [CFSG.Open.ordA]
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Nat.div_mul_cancel hdvdnum
    have hexp : 2 ≤ (n - 1) * n / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h : 2 * 2 ≤ (n - 1) * n := by
        have hn2 : 2 ≤ n - 1 := by omega
        calc 2 * 2 = 4 := by norm_num
          _ ≤ 2 * 3 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul hn2 hn
      omega
    have hdvdq : q ^ 2 ∣ q ^ ((n - 1) * n / 2) := Nat.pow_dvd_pow q hexp
    have hdvdnum2 : q ^ 2 ∣ q ^ ((n - 1) * n / 2) * C :=
      hdvdq.trans (dvd_mul_right _ _)
    have hcopq : Nat.Coprime q (q - 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd q (q - 1) ∣ q - (q - 1) :=
        Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      rw [show q - (q - 1) = 1 by omega] at hd
      exact Nat.dvd_one.mp hd
    have hcop : Nat.Coprime (q ^ 2) d :=
      (hcopq.pow_left 2).of_dvd_right (Nat.gcd_dvd_right _ _)
    have hdiv : q ^ 2 ∣ ordA (n - 1) q * d := by
      rw [hmul]
      exact hdvdnum2
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv
  have hnot : ¬ q ^ 2 ∣ ordA 1 q := by
    have htwo : 2 * ordA 1 q = q * (q ^ 2 - 1) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd
    intro h
    have h1 : q ^ 2 ∣ q * (q ^ 2 - 1) := by
      have h2 := h.mul_right 2
      rwa [mul_comm (ordA 1 q) 2, htwo] at h2
    have h1' : q * q ∣ q * (q ^ 2 - 1) := by
      rwa [show q * q = q ^ 2 from (pow_two q).symm]
    have h2 : q ∣ q ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left (k := q) (by omega) h1'
    have h3 : q ∣ 1 := by
      have hq2dvd : q ∣ q ^ 2 := dvd_pow_self q (by norm_num : 2 ≠ 0)
      have h4 := Nat.dvd_sub hq2dvd h2
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      rwa [Nat.sub_sub_eq_min, min_eq_right hq2pos] at h4
    have := Nat.dvd_one.mp h3
    omega
  intro heq
  exact hnot (heq ▸ hdvd)

private theorem uc22s2112r34_ordTwistedA_ne_one_of_three_le {q n : ℕ} (hq : 3 ≤ q)
    (hodd : Odd q) (hn : 3 ≤ n) : ordTwistedA (n - 1) q ≠ ordA 1 q := by
  have hdvd : q ^ 2 ∣ ordTwistedA (n - 1) q := by
    let C : ℕ := ∏ j ∈ Finset.Icc 2 n, (q ^ j - (-1 : ℤ) ^ j).toNat
    let d : ℕ := Nat.gcd n (q + 1)
    have hterm : (q ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
      simpa using
        CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (q := q) (i := 2)
          (by omega) even_two
    have hdvdC : d ∣ C := by
      have h1 : d ∣ q + 1 := Nat.gcd_dvd_right _ _
      have h2 : q + 1 ∣ q ^ 2 - 1 := by
        have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
          simpa using Nat.sq_sub_sq q 1
        rw [h]
        exact dvd_mul_right _ _
      have h3 : q ^ 2 - 1 ∣ C := by
        rw [← hterm]
        exact Finset.dvd_prod_of_mem (fun j => (q ^ j - (-1 : ℤ) ^ j).toNat)
          (by simp only [Finset.mem_Icc]; omega)
      exact h1.trans (h2.trans h3)
    have hdvdnum : d ∣ q ^ ((n - 1) * n / 2) * C :=
      dvd_mul_of_dvd_right hdvdC _
    have hmul : ordTwistedA (n - 1) q * d = q ^ ((n - 1) * n / 2) * C := by
      rw [CFSG.Open.ordTwistedA]
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Nat.div_mul_cancel hdvdnum
    have hexp : 2 ≤ (n - 1) * n / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have h : 2 * 2 ≤ (n - 1) * n := by
        have hn2 : 2 ≤ n - 1 := by omega
        calc 2 * 2 = 4 := by norm_num
          _ ≤ 2 * 3 := by norm_num
          _ ≤ (n - 1) * n := Nat.mul_le_mul hn2 hn
      omega
    have hdvdq : q ^ 2 ∣ q ^ ((n - 1) * n / 2) := Nat.pow_dvd_pow q hexp
    have hcopq : Nat.Coprime q (q + 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hd : Nat.gcd q (q + 1) ∣ (q + 1) - q :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      rw [show q + 1 - q = 1 by omega] at hd
      exact Nat.dvd_one.mp hd
    have hcop : Nat.Coprime (q ^ 2) d :=
      (hcopq.pow_left 2).of_dvd_right (Nat.gcd_dvd_right _ _)
    have hdiv : q ^ 2 ∣ ordTwistedA (n - 1) q * d := by
      rw [hmul]
      exact hdvdq.trans (dvd_mul_right _ _)
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv
  have hnot : ¬ q ^ 2 ∣ ordA 1 q := by
    have htwo : 2 * ordA 1 q = q * (q ^ 2 - 1) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hodd
    intro h
    have h1 : q ^ 2 ∣ q * (q ^ 2 - 1) := by
      have h2 := h.mul_right 2
      rwa [mul_comm (ordA 1 q) 2, htwo] at h2
    have h1' : q * q ∣ q * (q ^ 2 - 1) := by
      rwa [show q * q = q ^ 2 from (pow_two q).symm]
    have h2 : q ∣ q ^ 2 - 1 :=
      Nat.dvd_of_mul_dvd_mul_left (k := q) (by omega) h1'
    have h3 : q ∣ 1 := by
      have hq2dvd : q ∣ q ^ 2 := dvd_pow_self q (by norm_num : 2 ≠ 0)
      have h4 := Nat.dvd_sub hq2dvd h2
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      rwa [Nat.sub_sub_eq_min, min_eq_right hq2pos] at h4
    have := Nat.dvd_one.mp h3
    omega
  intro heq
  exact hnot (heq ▸ hdvd)


private theorem uc22s2112r34_eq_of_mem_inf_psl3_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [fact : Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : n = 3)
    (hadm : StatedLieAdmissible .PSL n p f) (hX : CFSG.Blueprint.LieModel X .PSL n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) : K = K' := by
  classical
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL n p f hp hp2 (by trivial) hadm X hX
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver hK)
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro hL2
    obtain ⟨r, f', hr, hr2, hq, hf', hm2⟩ := hL2
    have hcardX : Nat.card X = ordA (n - 1) (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA (2 - 1) (r ^ f') :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hm2
    have heq : ordA (n - 1) (p ^ f) = ordA 1 (p ^ f) := by
      calc ordA (n - 1) (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := by
            rw [hZ]
            exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
        _ = ordA (2 - 1) (r ^ f') := hcardQ
        _ = ordA 1 (r ^ f') := by norm_num
        _ = ordA 1 (p ^ f) := by rw [← hq]
    have hf : 1 ≤ f := hadm.2.1
    have hq3 : 3 ≤ p ^ f := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      exact hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
    exact uc22s2112r34_ordA_ne_one_of_three_le hq3 ((hp.odd_of_ne_two hp2).pow)
      (by omega : 3 ≤ n) heq
  obtain ⟨R, hR, hRK, hRk⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp hp2 hadm hX (by trivial) (by simp; omega) hL2 ψ hψ hker hK
  obtain ⟨R', hR', hR'K, hR'k⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp hp2 hadm hX (by trivial) (by simp; omega) hL2 ψ hψ hker hK'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hRlong : R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1) := by
    refine CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := m) (F := GaloisField p f) (by omega : 2 ≤ m + 1) ?_
    change R ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m (GaloisField p f)) at hR
    exact hR
  have hR'long : R' ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1) := by
    refine CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := m) (F := GaloisField p f) (by omega : 2 ≤ m + 1) ?_
    change R' ∈ fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m (GaloisField p f)) at hR'
    exact hR'
  obtain ⟨i, hi⟩ := hRlong
  obtain ⟨i', hi'⟩ := hR'long
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp (hRK ▸ hxK)
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp (hR'K ▸ hxK')
  let a' : SL(m + 1, GaloisField p f) := a
  let b' : SL(m + 1, GaloisField p f) := b
  let ψ' : SL(m + 1, GaloisField p f) →* X := ψ
  have hψa' : ψ' a' = x := hψa
  have hψb' : ψ' b' = x := hψb
  set r : ℕ := orderOf x with hr
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have ha_order : orderOf a = r := by
    refine Nat.dvd_antisymm ?_ ?_
    · apply orderOf_dvd_of_pow_eq_one
      have hmem : a ^ r ∈ R ⊓ ψ.ker := by
        refine ⟨R.pow_mem haR r, ?_⟩
        show ψ (a ^ r) = 1
        rw [map_pow, hψa, hr, pow_orderOf_eq_one]
      rw [hRk] at hmem
      exact Subgroup.mem_bot.mp hmem
    · rw [hr, ← hψa]
      exact orderOf_map_dvd ψ a
  have hb_order : orderOf b = r := by
    refine Nat.dvd_antisymm ?_ ?_
    · apply orderOf_dvd_of_pow_eq_one
      have hmem : b ^ r ∈ R' ⊓ ψ.ker := by
        refine ⟨R'.pow_mem hbR r, ?_⟩
        show ψ (b ^ r) = 1
        rw [map_pow, hψb, hr, pow_orderOf_eq_one]
      rw [hR'k] at hmem
      exact Subgroup.mem_bot.mp hmem
    · rw [hr, ← hψb]
      exact orderOf_map_dvd ψ b
  have ha1 : a ≠ 1 := by
    intro h1
    have h1' : r = 1 := by rw [← ha_order, h1, orderOf_one]
    exact hxr.ne_one h1'
  have har : a ^ r = 1 := by rw [← ha_order, pow_orderOf_eq_one]
  have hbr : b ^ r = 1 := by rw [← hb_order, pow_orderOf_eq_one]
  have ha1' : a' ≠ 1 := ha1
  have har' : a' ^ r = 1 := har
  have hbr' : b' ^ r = 1 := hbr
  let ζ : SL(m + 1, GaloisField p f) := a' * b'⁻¹
  have hζker : ζ ∈ ψ'.ker := by
    show ψ' (a' * b'⁻¹) = 1
    rw [map_mul, map_inv, hψa', hψb', mul_inv_cancel]
  have hζcenter : ζ ∈ Subgroup.center SL(m + 1, GaloisField p f) := hker hζker
  obtain ⟨ω, hω, hζmat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hζcenter
  have hζr : ζ ^ r = 1 := by
    have hcomm : Commute ζ b' := (Subgroup.mem_center_iff.mp hζcenter b').symm
    have h1 : (ζ * b') ^ r = ζ ^ r * b' ^ r := hcomm.mul_pow r
    have hζb : ζ * b' = a' := by
      show a' * b'⁻¹ * b' = a'
      group
    rw [hζb, har', hbr', mul_one] at h1
    exact h1.symm
  have hζ1 : ζ = 1 := by
    have h4 : m + 1 = 3 := hn
    have hω3 : ω ^ 3 = 1 := by
      have := hω
      rw [h4] at this
      simpa using this
    have hζ3 : ζ ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hζmat,
        ← map_pow, hω3, map_one]
    have hcop : Nat.Coprime 3 r := by
      refine (Nat.coprime_primes Nat.prime_three hxr).mpr ?_
      rw [hr]
      exact Ne.symm hx3
    exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hζ3, hζr⟩
  have hab : a' = b' := by
    have h : a' * b'⁻¹ = 1 := hζ1
    calc a' = a' * b'⁻¹ * b' := by group
      _ = b' := by rw [h, one_mul]
  have haR' : a' ∈ R := haR
  have hbR' : b' ∈ R' := hbR
  have hbR'a : a' ∈ R' := hab.symm ▸ hbR'
  have hR_eq : R = R' :=
    uc22s2112r34_isLongRootSL2_eq_of_mem (K := GaloisField p f) (p := p) (n := m + 1)
      (hn := by omega) hp h2 hi hi' haR' hbR'a ha1' hxr hxp har'
  rw [hRK, hR'K, hR_eq]

theorem uc22s2112r34_eq_of_mem_inf_psl3 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL 3 p f) (hX : CFSG.Blueprint.LieModel X .PSL 3 p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) : K = K' :=
  uc22s2112r34_eq_of_mem_inf_psl3_aux (n := 3) (fact := ⟨hp⟩) hp hp2 rfl hadm hX hK hK' hxK hxK'
    hxr hx2 hx3 hxp

private theorem uc22s2112r34_eq_of_mem_inf_psu3_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [fact : Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : n = 3)
    (hadm : StatedLieAdmissible .PSU n p f) (hX : CFSG.Blueprint.LieModel X .PSU n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) : K = K' := by
  classical
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU n p f Fact.out hp2 (by trivial) hadm X hX
  have hf : 1 ≤ f := hadm.2.1
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
  have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro hL2
    obtain ⟨r, f', hr, hr2, hq, hf', hm2⟩ := hL2
    have hcardX : Nat.card X = ordTwistedA (n - 1) (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSU (by omega) hp2 hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA 1 (r ^ f') := by
      simpa using CFSG.GH74.card_of_lieModel_PSL (n := 2) (p := r) (f := f')
        (by norm_num) hm2
    have hZbot : Subgroup.center X = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
      · exact hbot
      · exfalso
        have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
          rw [htop]
          exact QuotientGroup.subsingleton_quotient_top
        have hcard1 : Nat.card (X ⧸ Subgroup.center X) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨(1 : X ⧸ Subgroup.center X)⟩⟩
        have hq1 : ordA 1 (r ^ f') = 1 := by
          rw [← hcardQ, hcard1]
        have hr3 : 3 ≤ r := by
          have := hr.two_le
          omega
        have hq3' : 3 ≤ r ^ f' :=
          hr3.trans (Nat.le_self_pow (by omega : f' ≠ 0) r)
        have htwo : 2 * ordA 1 (r ^ f') = r ^ f' * ((r ^ f') ^ 2 - 1) :=
          CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one
            ((hr.odd_of_ne_two hr2).pow)
        have h2 : 2 = r ^ f' * ((r ^ f') ^ 2 - 1) := by
          rw [← htwo, hq1, mul_one]
        have h9 : 9 ≤ (r ^ f') ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (r ^ f') ^ 2 := Nat.pow_le_pow_left hq3' 2
        have hq2pos : 8 ≤ (r ^ f') ^ 2 - 1 := by omega
        have hprod : 24 ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := by
          calc 24 = 3 * 8 := by norm_num
            _ ≤ r ^ f' * ((r ^ f') ^ 2 - 1) := Nat.mul_le_mul hq3' hq2pos
        omega
    have heq : ordTwistedA (n - 1) (p ^ f) = ordA 1 (p ^ f) := by
      calc ordTwistedA (n - 1) (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := by
            rw [hZbot]
            exact (Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv).symm
        _ = ordA 1 (r ^ f') := hcardQ
        _ = ordA 1 (p ^ f) := by rw [← hq]
    exact uc22s2112r34_ordTwistedA_ne_one_of_three_le hq3 hoddq (by omega : 3 ≤ n) heq
  obtain ⟨R, hR, hRK, hRker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      (by trivial) (by simp) hL2 ψ hψ hker hK
  obtain ⟨R', hR', hR'K, hR'ker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      (by trivial) (by simp) hL2 ψ hψ hker hK'
  let F := GaloisField p (2 * f)
  have hFcard : Nat.card F = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hqne2 : p ^ f ≠ 2 :=
    CFSG.ClassicalInvolution.Models.prime_pow_ne_two_of_ne_two hp2 f
  obtain ⟨e, he⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let L : Subgroup (Su F p f n) := R.map e.toMonoidHom
  let L' : Subgroup (Su F p f n) := R'.map e.toMonoidHom
  obtain ⟨i, hi⟩ := (he R).mp hR
  obtain ⟨i', hi'⟩ := (he R').mp hR'
  have hxKmap : x ∈ R.map ψ := by rw [← hRK]; exact hxK
  have hxK'map : x ∈ R'.map ψ := by rw [← hR'K]; exact hxK'
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp hxKmap
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp hxK'map
  have ha_r : a ^ orderOf x = 1 := by
    have hmem : a ^ orderOf x ∈ R ⊓ ψ.ker := by
      refine ⟨pow_mem haR _, ?_⟩
      change ψ (a ^ orderOf x) = 1
      rw [map_pow, hψa, pow_orderOf_eq_one]
    rw [hRker] at hmem
    simpa using hmem
  have hb_r : b ^ orderOf x = 1 := by
    have hmem : b ^ orderOf x ∈ R' ⊓ ψ.ker := by
      refine ⟨pow_mem hbR _, ?_⟩
      change ψ (b ^ orderOf x) = 1
      rw [map_pow, hψb, pow_orderOf_eq_one]
    rw [hR'ker] at hmem
    simpa using hmem
  have ha1 : a ≠ 1 := by
    intro ha
    have hx1 : x = 1 := by rw [← hψa, ha, map_one]
    exact hxr.ne_one (by rw [hx1, orderOf_one])
  let ζ := a * b⁻¹
  have hζker : ζ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (a * b⁻¹) = 1
    rw [map_mul, map_inv, hψa, hψb, mul_inv_cancel]
  have hζcenter := hker hζker
  have hζcomm : Commute ζ b := (Subgroup.mem_center_iff.mp hζcenter b).symm
  have haeq : a = ζ * b := by
    change a = (a * b⁻¹) * b
    group
  have hζpow : ζ ^ orderOf x = 1 := by
    have h1 : a ^ orderOf x = (ζ ^ orderOf x) * (b ^ orderOf x) := by
      rw [haeq]
      exact hζcomm.mul_pow (orderOf x)
    rw [ha_r, hb_r, mul_one] at h1
    exact h1.symm
  have hζcenterSu : e ζ ∈ Subgroup.center (Su F p f n) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hζcenter
  obtain ⟨c, hc⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3W.exists_scalar_of_mem_center_su3
      (K := F) (p := p) (f := f) hFcard hqne2 (by omega : 3 ≤ n) hζcenterSu
  have hζsmul : ∀ m : ℕ, suMat ((e ζ) ^ m) = (suMat (e ζ)) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, suMat_mul, ih]
  have hc_r : c ^ orderOf x = 1 := by
    have hmap : (e ζ) ^ orderOf x = 1 := by rw [← map_pow, hζpow, map_one]
    have h := congrArg (fun z : Su F p f n => suMat z) hmap
    rw [hζsmul (orderOf x), hc, suMat_one,
      ← map_pow (Matrix.scalar (Fin n)) c (orderOf x)] at h
    have h0 := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h0
  have hζ1_of_c1 : c = 1 → ζ = 1 := by
    intro hc1
    have hζ1Su : e ζ = 1 := by
      apply suMat_injective
      rw [hc, hc1, suMat_one]
      exact map_one (Matrix.scalar (Fin n))
    exact e.injective (by simpa using hζ1Su)
  have hodd : Odd (orderOf x) := hxr.odd_of_ne_two hx2
  have hab : a = b := by
    have hc3 : c ^ 3 = 1 := by
      have h := det_suMat (e ζ)
      rw [hc] at h
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin] at h
      simpa [hn] using h
    have hcop : Nat.Coprime 3 (orderOf x) :=
      (Nat.coprime_primes Nat.prime_three hxr).mpr (Ne.symm hx3)
    have hc1 : c = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨hc3, hc_r⟩
    have hζ1 : ζ = 1 := hζ1_of_c1 hc1
    have h : a * b⁻¹ = 1 := hζ1
    exact mul_inv_eq_one.mp h
  have haL : e a ∈ L := Subgroup.mem_map_of_mem e.toMonoidHom haR
  have hbL' : e b ∈ L' := Subgroup.mem_map_of_mem e.toMonoidHom hbR
  have haL' : e a ∈ L' := by
    rw [show e a = e b from congrArg e hab]
    exact hbL'
  have ha1Su : e a ≠ 1 := by
    intro ha1e
    apply ha1
    exact e.injective (by simpa using ha1e)
  have harSu : (e a) ^ orderOf x = 1 := by
    rw [← map_pow, ha_r, map_one]
  have hLL' : L = L' :=
    uc22s2112r34_isLongRootSU2_eq_of_mem hFcard hp2 hi hi' haL haL' ha1Su hxr hxp harSu
  have hR_eq : R = R' := Subgroup.map_injective e.injective (by simpa [L, L'] using hLL')
  rw [hRK, hR'K, hR_eq]

theorem uc22s2112r34_eq_of_mem_inf_psu3 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU 3 p f) (hX : CFSG.Blueprint.LieModel X .PSU 3 p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K')
    {x : X} (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) : K = K' :=
  uc22s2112r34_eq_of_mem_inf_psu3_aux (n := 3) (fact := ⟨hp⟩) hp hp2 rfl hadm hX hK hK' hxK hxK'
    hxr hx2 hx3 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22
