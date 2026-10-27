module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_12
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.12) -/


private theorem section13_three_le_of_odd_prime {n : ℕ}
    (hn : Nat.Prime n) (hodd : Odd n) :
    3 ≤ n := by
  have h2le : 2 ≤ n := hn.two_le
  have hn_ne_two : n ≠ 2 := by
    intro hn2
    have hnot_even : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    exact hnot_even (by rw [hn2]; exact even_two)
  omega

private theorem section13_natCard_actor_dvd_group_card_sub_one
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (hfree : ∀ a : A, a ≠ 1 → ∀ q : Q, a • q = q → q = 1) :
    Nat.card A ∣ Nat.card Q - 1 := by
  classical
  let α := {q : Q // q ≠ 1}
  letI : MulAction A α :=
    { smul := fun a x => ⟨a • (x : Q), by
        intro h
        apply x.2
        have h' := congrArg (fun y : Q => a⁻¹ • y) h
        simpa using h'⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : A) • (x : Q) = (x : Q)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change (a * b) • (x : Q) = a • (b • (x : Q))
        rw [mul_smul] }
  have hstab : ∀ x : α, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (x : Q) = (x : Q) := congrArg Subtype.val hax
    exact x.2 (hfree a ha_ne (x : Q) hfix)
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card Q - 1 := by
    letI : Fintype Q := Fintype.ofFinite Q
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {q : Q // q ≠ 1} = Fintype.card Q - 1
    simp
  rw [hcardα, Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A α)), by
    rw [mul_comm]
    exact hcard_equiv⟩

private theorem section13_le_normalizer_subgroupCentralizerIn_of_le_normalizers
    {G : Type u} [Group G]
    {X U P : Subgroup G}
    (hXnormU : X ≤ Subgroup.normalizer (U : Set G))
    (hXnormP : X ≤ Subgroup.normalizer (P : Set G)) :
    X ≤ Subgroup.normalizer ((subgroupCentralizerIn U P : Subgroup G) : Set G) := by
  have hXnormCentralizer :
      X ≤ Subgroup.normalizer ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro p hp
      have hp' : n⁻¹ * p * n ∈ P :=
        (Subgroup.mem_normalizer_iff''.mp (hXnormP hn) p).1 hp
      have hcomm : (n⁻¹ * p * n) * c = c * (n⁻¹ * p * n) :=
        hc (n⁻¹ * p * n) hp'
      calc
        p * (n * c * n⁻¹) = n * ((n⁻¹ * p * n) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * p * n)) * n⁻¹ := by rw [hcomm]
        _ = (n * c * n⁻¹) * p := by group
    · intro hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro p hp
      have hp' : n * p * n⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hXnormP hn) p).1 hp
      have hcomm :
          (n * p * n⁻¹) * (n * c * n⁻¹) =
            (n * c * n⁻¹) * (n * p * n⁻¹) :=
        hc (n * p * n⁻¹) hp'
      calc
        p * c = n⁻¹ * ((n * p * n⁻¹) * (n * c * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * c * n⁻¹) * (n * p * n⁻¹)) * n := by rw [hcomm]
        _ = c * p := by group
  intro x hx
  have hxinf :
      x ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    ⟨hXnormU hx, hXnormCentralizer hx⟩
  simpa [subgroupCentralizerIn] using
    (Subgroup.inf_normalizer_le_normalizer_inf (G := G)
      (H := U) (K := Subgroup.centralizer (P : Set G)) hxinf)

private theorem section13_theorem_13_12_q_dvd_c_sub_one_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    q ∣ c - 1 := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, hq_card, hC, _hD, hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  have hptypeSOrig := hptypeS
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hMcomp, _hUleD,
      _hUnil, hW1normUInM, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1leS, _hW1Hall⟩
  rcases hMF with ⟨⟨hPS, hPNormalS, _hPnil, _hPHall⟩, _hSmaxMax⟩
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUInM hw)).1
  have hW1normP : W1 ≤ Subgroup.normalizer (P : Set G) :=
    hW1leS.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hPS).1 hPNormalS)
  have hW1normC : W1 ≤ Subgroup.normalizer (C : Set G) := by
    simpa [hC] using
      (section13_le_normalizer_subgroupCentralizerIn_of_le_normalizers
        (X := W1) (U := U) (P := P) hW1normU hW1normP)
  haveI : Subgroup.Normalizes W1 C := ⟨hW1normC⟩
  have hregular : section14ActsRegularlyOn W1 U :=
    source_typeP_W1_actsRegularlyOn_U hptypeSOrig
  have hfree : ∀ a : W1, a ≠ 1 → ∀ y : C, a • y = y → y = 1 := by
    intro a ha y hy
    have haG_ne : (a : G) ≠ 1 := by
      intro h
      exact ha (Subtype.ext h)
    have hcent_eq := hregular.2 (a : G) a.property haG_ne
    have hyU : (y : G) ∈ U := by
      have hyC : (y : G) ∈ subgroupCentralizerIn U P := by
        simpa [hC] using (show (y : G) ∈ C from y.property)
      exact hyC.1
    have hyconj : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hy
    have hycomm : (y : G) * (a : G) = (a : G) * (y : G) := by
      have hmul := congrArg (fun t : G => t * (a : G)) hyconj
      simpa [mul_assoc] using hmul.symm
    have hycent : (y : G) ∈ elementCentralizerIn U (a : G) := by
      exact ⟨hyU, Subgroup.mem_centralizer_singleton_iff.mpr hycomm⟩
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      simpa [hcent_eq] using hycent
    apply Subtype.ext
    simpa using hybot
  have hdivCards : Nat.card W1 ∣ Nat.card C - 1 :=
    section13_natCard_actor_dvd_group_card_sub_one (A := W1) (Q := C) hfree
  simpa [hq_card, hc_card] using hdivCards

private theorem section13_two_mul_add_one_le_of_odd_dvd_sub_one
    {q c : ℕ}
    (hqPrime : Nat.Prime q) (hq3 : 3 ≤ q) (hcOdd : Odd c) (hcne : c ≠ 1)
    (hdiv : q ∣ c - 1) :
    2 * q + 1 ≤ c := by
  rcases hcOdd with ⟨a, rfl⟩
  rcases hdiv with ⟨k, hk⟩
  have hk_exact : 2 * a = q * k := by
    simpa using hk
  have hkpos : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hknot
    rw [hk0, Nat.mul_zero] at hk_exact
    have ha0 : a = 0 := by omega
    exact hcne (by omega)
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    omega
  have hqOdd : Odd q := hqPrime.odd_of_ne_two hq_ne_two
  rcases hqOdd with ⟨b, hq⟩
  subst q
  have h2dvd : 2 ∣ (2 * b + 1) * k :=
    ⟨a, hk_exact.symm⟩
  have h2not : ¬ 2 ∣ 2 * b + 1 := by
    intro h
    rcases h with ⟨t, ht⟩
    omega
  have h2dvd_k : 2 ∣ k := by
    exact (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd |>.resolve_left h2not
  rcases h2dvd_k with ⟨t, ht⟩
  subst k
  have htpos : 0 < t := by omega
  have hk' : 2 * a = (2 * b + 1) * (2 * t) := by
    simpa using hk_exact
  have hle2a : 2 * (2 * b + 1) ≤ 2 * a := by
    calc
      2 * (2 * b + 1) = (2 * b + 1) * 2 := by omega
      _ ≤ (2 * b + 1) * (2 * t) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * a := hk'.symm
  omega

private theorem section13_eq_seven_or_thirteen_le_of_odd_three_dvd_sub_one
    {c : ℕ} (hcOdd : Odd c) (hcne : c ≠ 1) (hdiv : 3 ∣ c - 1) :
    c = 7 ∨ 13 ≤ c := by
  rcases hcOdd with ⟨a, rfl⟩
  by_cases h13 : 13 ≤ 2 * a + 1
  · exact Or.inr h13
  · left
    have ha_lt : a < 6 := by omega
    interval_cases a <;> simp at hcne hdiv ⊢

public theorem section13_u_div_c_le_of_le_bounds
    {u c : ℕ} {A C : ℝ}
    (huA : (u : ℝ) ≤ A) (hCc : C ≤ (c : ℝ)) (hCpos : 0 < C) (hAnonneg : 0 ≤ A) :
    (u : ℝ) / (c : ℝ) ≤ A / C := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le hCpos hCc
  calc
    (u : ℝ) / (c : ℝ) ≤ A / (c : ℝ) := by
      exact div_le_div_of_nonneg_right huA hcpos.le
    _ ≤ A / C := by
      exact div_le_div_of_nonneg_left hAnonneg hCpos hCc

public theorem section13_m_lt_of_u_div_c_le
    {p q u c : ℕ} {m B : ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (h10ineq : (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ))
    (huc_le : (u : ℝ) / (c : ℝ) ≤ B) :
    m < B * (q : ℝ) / ((p : ℝ) ^ (q - 1)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpPow : (0 : ℝ) < (p : ℝ) ^ (q - 1) := pow_pos hpR _
  have hscale_pos : (0 : ℝ) < (q : ℝ) / ((p : ℝ) ^ (q - 1)) := div_pos hqR hpPow
  have hscaled := mul_lt_mul_of_pos_right h10ineq hscale_pos
  calc
    m = ((m * (p : ℝ) ^ (q - 1)) / (q : ℝ)) *
        ((q : ℝ) / ((p : ℝ) ^ (q - 1))) := by
      field_simp [hqR.ne', hpPow.ne']
    _ < ((u : ℝ) / (c : ℝ)) * ((q : ℝ) / ((p : ℝ) ^ (q - 1))) := hscaled
    _ ≤ B * ((q : ℝ) / ((p : ℝ) ^ (q - 1))) := by
      exact mul_le_mul_of_nonneg_right huc_le hscale_pos.le
    _ = B * (q : ℝ) / ((p : ℝ) ^ (q - 1)) := by ring

public theorem section13_m_upper_lt_qp_ratio
    {p q : ℕ} (hp1 : 1 < p) (hq : 0 < q) :
    ((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) /
        ((2 * q + 1 : ℕ) : ℝ)) * (q : ℝ) / ((p : ℝ) ^ (q - 1))) <
      (((q : ℝ) * (p : ℝ)) /
        (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  have hp_pos : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpSub : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp1
  have hCpos : (0 : ℝ) < ((2 * q + 1 : ℕ) : ℝ) := by positivity
  have hpPow : (0 : ℝ) < (p : ℝ) ^ (q - 1) := pow_pos hpR _
  have hden : (0 : ℝ) <
      (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) *
        ((p : ℝ) ^ (q - 1))) := by positivity
  have hpow_eq : (p : ℝ) ^ q = (p : ℝ) * (p : ℝ) ^ (q - 1) := by
    have hqeq : q = (q - 1) + 1 := by omega
    calc
      (p : ℝ) ^ q = (p : ℝ) ^ ((q - 1) + 1) :=
        congrArg (fun n : ℕ => (p : ℝ) ^ n) hqeq
      _ = (p : ℝ) ^ (q - 1) * (p : ℝ) := pow_succ _ _
      _ = (p : ℝ) * (p : ℝ) ^ (q - 1) := by ring
  have hnum_lt : (p : ℝ) ^ q - 1 < (p : ℝ) ^ q := by linarith
  calc
    ((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) /
        ((2 * q + 1 : ℕ) : ℝ)) * (q : ℝ) / ((p : ℝ) ^ (q - 1))) =
        ((q : ℝ) * ((p : ℝ) ^ q - 1)) /
          (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) *
            ((p : ℝ) ^ (q - 1))) := by
      field_simp [hpSub.ne', hCpos.ne', hpPow.ne']
    _ < ((q : ℝ) * ((p : ℝ) ^ q)) /
          (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) *
            ((p : ℝ) ^ (q - 1))) := by
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hnum_lt hqR) hden
    _ = (((q : ℝ) * (p : ℝ)) /
        (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
      rw [hpow_eq]
      field_simp [hpPow.ne']

private theorem section13_p_eq_three_qp_upper_lt_eight_tenths {q : ℕ} (hq : 0 < q) :
    (((q : ℝ) * (3 : ℝ)) /
      (((2 * q + 1 : ℕ) : ℝ) * ((3 - 1 : ℕ) : ℝ))) < (8 : ℝ) / 10 := by
  have hden : (((2 * q + 1 : ℕ) : ℝ) * ((3 - 1 : ℕ) : ℝ)) ≠
      (0 : ℝ) := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp [hden]
  norm_num
  nlinarith

private theorem section13_p_eq_three_qp_upper_lt_seven_tenths_of_q_eq_five
    {q : ℕ} (hqeq : q = 5) :
    (((q : ℝ) * (3 : ℝ)) /
      (((2 * q + 1 : ℕ) : ℝ) * ((3 - 1 : ℕ) : ℝ))) < (7 : ℝ) / 10 := by
  subst q
  norm_num

public theorem section13_numeric_contradiction_of_p_eq_three
    {p q : ℕ} {m : ℝ}
    (hqPrime : Nat.Prime q) (hpne : p ≠ q) (hq3 : 3 ≤ q)
    (h11a : 3 ≤ p → 7 ≤ q → (8 : ℝ) / 10 < m)
    (h11b : 3 ≤ p → 5 ≤ q → (7 : ℝ) / 10 < m)
    (hm_qp : m < ((q : ℝ) * (p : ℝ)) /
      (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))
    (hp_eq : p = 3) :
    False := by
  subst p
  have hq_ne_three : q ≠ 3 := by
    intro hqeq
    exact hpne hqeq.symm
  have hnot7 : ¬ 7 ≤ q := by
    intro hq7
    have hm_low : (8 : ℝ) / 10 < m := h11a (by norm_num) hq7
    have hm_high : m < (8 : ℝ) / 10 :=
      lt_trans hm_qp (section13_p_eq_three_qp_upper_lt_eight_tenths (by omega))
    linarith
  have hq_le6 : q ≤ 6 := by omega
  have hqeq : q = 5 := by
    interval_cases q
    · contradiction
    · have h2dvd : 2 ∣ 4 := by norm_num
      have h2eq := hqPrime.eq_one_or_self_of_dvd 2 h2dvd
      omega
    · rfl
    · have h2dvd : 2 ∣ 6 := by norm_num
      have h2eq := hqPrime.eq_one_or_self_of_dvd 2 h2dvd
      omega
  have hm_low7 : (7 : ℝ) / 10 < m := h11b (by norm_num) (by omega)
  have hm_high7 : m < (7 : ℝ) / 10 :=
    lt_trans hm_qp (section13_p_eq_three_qp_upper_lt_seven_tenths_of_q_eq_five hqeq)
  linarith

public theorem section13_five_le_of_prime_three_le_ne_three
    {p : ℕ} (hpPrime : Nat.Prime p) (hp3 : 3 ≤ p) (hpne3 : p ≠ 3) :
    5 ≤ p := by
  by_contra hnot
  have hp_le4 : p ≤ 4 := by omega
  interval_cases p
  · exact hpne3 rfl
  · have h2dvd : 2 ∣ 4 := by norm_num
    have h2eq := hpPrime.eq_one_or_self_of_dvd 2 h2dvd
    omega

private theorem section13_qp_ratio_lt_seven_tenths_of_five_le
    {p q : ℕ} (hp : 5 ≤ p) (hq : 0 < q) :
    (((q : ℝ) * (p : ℝ)) /
      (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) < (7 : ℝ) / 10 := by
  have hp1le : 1 ≤ p := by omega
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt (by omega : 1 < p)
  have hden : (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) ≠
      (0 : ℝ) := by positivity
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp [hden]
  norm_num [Nat.cast_sub hp1le, Nat.cast_add, Nat.cast_mul]
  nlinarith

public theorem section13_q_eq_three_of_five_le_numeric
    {p q : ℕ} {m : ℝ}
    (hqPrime : Nat.Prime q) (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (h11b : 3 ≤ p → 5 ≤ q → (7 : ℝ) / 10 < m)
    (hm_qp : m < ((q : ℝ) * (p : ℝ)) /
      (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) :
    q = 3 := by
  have hq_pos : 0 < q := by omega
  have hnot5 : ¬ 5 ≤ q := by
    intro hq5
    have hm_low : (7 : ℝ) / 10 < m := h11b (by omega) hq5
    have hm_high : m < (7 : ℝ) / 10 :=
      lt_trans hm_qp (section13_qp_ratio_lt_seven_tenths_of_five_le hp5 hq_pos)
    linarith
  have hq_le4 : q ≤ 4 := by omega
  interval_cases q
  · rfl
  · have h2dvd : 2 ∣ 4 := by norm_num
    have h2eq := hqPrime.eq_one_or_self_of_dvd 2 h2dvd
    omega

private theorem section13_q_three_c_thirteen_upper_lt_49_100
    {p q : ℕ} (hp : 5 ≤ p) (hqeq : q = 3) :
    (((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) / (13 : ℝ)) *
        (q : ℝ) / ((p : ℝ) ^ (q - 1))) < (49 : ℝ) / 100 := by
  subst q
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1le : 1 ≤ p := by omega
  have hpSubPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < p)
  have hpSub : ((p - 1 : ℕ) : ℝ) ≠ 0 := hpSubPos.ne'
  have hpPow : (p : ℝ) ^ (3 - 1) ≠ 0 := pow_ne_zero _ hp_pos.ne'
  field_simp [hpSub, hpPow]
  norm_num [Nat.cast_sub hp1le]
  ring_nf
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [sq_nonneg ((p : ℝ) - 5)]

private theorem section13_q_three_c_seven_upper_lt_49_100_of_eleven_le
    {p q : ℕ} (hp : 11 ≤ p) (hqeq : q = 3) :
    (((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) / (7 : ℝ)) *
        (q : ℝ) / ((p : ℝ) ^ (q - 1))) < (49 : ℝ) / 100 := by
  subst q
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1le : 1 ≤ p := by omega
  have hpSubPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < p)
  have hpSub : ((p - 1 : ℕ) : ℝ) ≠ 0 := hpSubPos.ne'
  have hpPow : (p : ℝ) ^ (3 - 1) ≠ 0 := pow_ne_zero _ hp_pos.ne'
  field_simp [hpSub, hpPow]
  norm_num [Nat.cast_sub hp1le]
  ring_nf
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [sq_nonneg ((p : ℝ) - 11)]

private theorem section13_theorem_13_12_linearComparisonPrereqs_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  rcases theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig h10 with
    ⟨_hD, hcaseT, _hv⟩
  rcases hcaseT with
    ⟨_hhyp92, _hH0, _hcent, hqPrime, hpPrime, _hho, _hquot,
      _hCcent, _hUbar, _hirr, _hfield, _hcop, _hdvd⟩
  have hpne : p ≠ q := by
    rcases hcaseB with
      ⟨hprod, hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
        _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
        _hCover⟩
    have hcop_cards : Nat.Coprime (Nat.card W1) (Nat.card W2) :=
      section13_natCard_coprime_of_section12InternalDirectProduct_cyclic hprod hWcyc
    have hcop_qp : Nat.Coprime q p := by
      simpa [hq_card, hp_card] using hcop_cards
    intro hpq
    have hcop_qq : Nat.Coprime q q := by
      simpa [hpq] using hcop_qp
    exact hqPrime.ne_one (Nat.Coprime.eq_one_of_dvd hcop_qq dvd_rfl)
  have hoddG : Odd (Nat.card G) := by
    letI : IsMinCE G :=
      section13_theorem_13_2_global_isMinCE_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
    exact IsMinCE.odd_order
  have hpOdd : Odd p := by
    rw [hp_card]
    exact section13_odd_card_subgroup_of_odd_group W2 hoddG
  have hqOdd : Odd q := by
    rw [hq_card]
    exact section13_odd_card_subgroup_of_odd_group W1 hoddG
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hMF, _htype, _htypeLarge, _hUcomm, _hfrobUW1, _hPelem, _hPcard,
      huBound, _hcoh, _hTI, _hTau, _hnorm⟩
  rcases section13_theorem_13_10_rawSourcePositivity_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig with
    ⟨_hp_pos, _hq_pos, hc_pos⟩
  exact ⟨hpPrime, hqPrime, hpne, section13_three_le_of_odd_prime hpPrime hpOdd,
    section13_three_le_of_odd_prime hqPrime hqOdd, huBound, hc_pos⟩

private theorem section13_theorem_13_12_c_lower_bound_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcne : c ≠ 1)
    (hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c) :
    2 * q + 1 ≤ c := by
  have hsourceOrig := hsource
  rcases hpre with ⟨_hpPrime, hqPrime, _hpne, _hp3, hq3, _huBound, _hcpos⟩
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  have hoddG : Odd (Nat.card G) := by
    letI : IsMinCE G :=
      section13_theorem_13_2_global_isMinCE_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
    exact IsMinCE.odd_order
  have hcOdd : Odd c := by
    rw [hc_card]
    exact section13_odd_card_subgroup_of_odd_group C hoddG
  exact section13_two_mul_add_one_le_of_odd_dvd_sub_one hqPrime hq3 hcOdd hcne
    (section13_theorem_13_12_q_dvd_c_sub_one_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig)

private theorem section13_theorem_13_12_c_eq_seven_or_thirteen_le_of_q_eq_three_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcne : c ≠ 1) (hqeq : q = 3) :
    c = 7 ∨ 13 ≤ c := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  have hoddG : Odd (Nat.card G) := by
    letI : IsMinCE G :=
      section13_theorem_13_2_global_isMinCE_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
    exact IsMinCE.odd_order
  have hcOdd : Odd c := by
    rw [hc_card]
    exact section13_odd_card_subgroup_of_odd_group C hoddG
  have hdiv3 : 3 ∣ c - 1 := by
    simpa [hqeq] using
      (section13_theorem_13_12_q_dvd_c_sub_one_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig)
  exact section13_eq_seven_or_thirteen_le_of_odd_three_dvd_sub_one hcOdd hcne hdiv3

private theorem section13_theorem_13_12_not_PC_nilpotentNormalHall_of_c_eq_seven_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hc7 : c = 7) :
    ¬ section16NilpotentNormalHallIn (P ⊔ C) Smax := by
  intro hPC
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  rcases hptypeS with
    ⟨hSF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer, _hW2leInf, _hW2cyc,
      _hW2ne, _hCent, _hNorm⟩
  rcases hDercomp with ⟨_hPleD, _hUleD, _hDsup, hP_U_disj⟩
  have hPCleP : P ⊔ C ≤ P := hSF.2 (P ⊔ C) hPC
  have hCleP : C ≤ P := le_sup_right.trans hPCleP
  have hCleU : C ≤ U := by
    rw [hC]
    exact inf_le_left
  have hCbot : C = ⊥ := by
    apply le_bot_iff.mp
    intro x hxC
    exact (Subgroup.disjoint_def.mp hP_U_disj) (hCleP hxC) (hCleU hxC)
  have hc_one : c = 1 := by
    rw [hc_card, hCbot]
    simp
  omega

private theorem section13_theorem_13_12_p_c_coprime_of_small_exception_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c)
    (_hp5 : 5 ≤ p) (_hplt11 : p < 11) (_hqeq : q = 3) (_hceq : c = 7) :
    Nat.Coprime p c := by
  have hsourceOrig := hsource
  rcases hpre with ⟨_hpPrime, _hqPrime, _hpne, _hp3, hq3, _huBound, _hcpos⟩
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  rcases hptypeS with
    ⟨hSF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hSF with ⟨⟨hPS, _hPNormalS, _hPnil, hPHallS⟩, _hSmaxMax⟩
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hMF, _htype, _htypeLarge, _hUcomm, _hfrobUW1, _hPelem, hP_card,
      _huBound, _hcoh, _hTI, _hTau, _hnorm⟩
  have hS_card : Nat.card Smax = (p ^ q) * (u * c) * q :=
    section13_smax_card_formula_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hP_card
  have hPsub_card : Nat.card (P.subgroupOf Smax) = Nat.card P :=
    natCard_subgroupOf_eq P Smax hPS
  have hindex_eq : (P.subgroupOf Smax).index = (u * c) * q := by
    have hpow_pos : 0 < p ^ q := by
      rw [← hP_card]
      exact Nat.card_pos (α := P)
    apply Nat.mul_right_cancel hpow_pos
    calc
      (P.subgroupOf Smax).index * p ^ q =
          (P.subgroupOf Smax).index * Nat.card (P.subgroupOf Smax) := by
            rw [hPsub_card, hP_card]
      _ = Nat.card Smax := Subgroup.index_mul_card (H := P.subgroupOf Smax)
      _ = (p ^ q) * (u * c) * q := hS_card
      _ = (u * c) * q * p ^ q := by ring
  have hc_dvd_index : c ∣ (P.subgroupOf Smax).index := by
    rw [hindex_eq]
    exact ⟨u * q, by ring⟩
  have hcopPindex :
      Nat.Coprime (Nat.card (P.subgroupOf Smax)) (P.subgroupOf Smax).index :=
    hPHallS.card_coprime_index
  have hp_dvd_Psub : p ∣ Nat.card (P.subgroupOf Smax) := by
    rw [hPsub_card, hP_card]
    exact dvd_pow_self p (by omega : q ≠ 0)
  exact (Nat.Coprime.coprime_dvd_left hp_dvd_Psub hcopPindex).coprime_dvd_right
    hc_dvd_index

private theorem section13_theorem_13_12_p_eq_five_of_small_exception
    {p c : ℕ}
    (hpPrime : Nat.Prime p) (hp5 : 5 ≤ p) (hplt11 : p < 11)
    (hceq : c = 7) (hpc : Nat.Coprime p c) :
    p = 5 := by
  interval_cases p
  · rfl
  · have h2eq := hpPrime.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 6)
    omega
  · rw [hceq] at hpc
    norm_num at hpc
  · have h2eq := hpPrime.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 8)
    omega
  · have h3eq := hpPrime.eq_one_or_self_of_dvd 3 (by norm_num : 3 ∣ 9)
    omega
  · have h2eq := hpPrime.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 10)
    omega

private theorem section13_theorem_13_12_not_case_9_7_a_of_small_exception_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c)
    (_hp_eq : p = 5) (_hqeq : q = 3) (_hceq : c = 7) :
    ¬ case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  intro hcaseA
  rcases hcaseA with ⟨hBarU, a, hcaseA97⟩
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource
  have hUodd : Odd (Nat.card U) :=
    odd_of_card_dvd hMin.odd_order (Subgroup.card_subgroup_dvd_card U)
  have huOdd : Odd u :=
    Section9.quotientBarUCardinality_odd_of_odd_U_sec9 U C u hBarU hUodd
  have hdiv16 : u ∣ 16 := by
    simpa [_hp_eq, _hqeq] using
      (Section9.theorem_9_7_case_a_barU_card_dvd_p_minus_one_pow_sec9
        Smax P U W1 W2 ⊥ C p q a u hcaseA97 hBarU)
  have hu_one : u = 1 := by
    have hdivPow2 : u ∣ 2 ^ 4 := by
      simpa using hdiv16
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).1 hdivPow2 with
      ⟨m, _hm_le, hm_eq⟩
    have hm_zero : m = 0 := by
      by_contra hm_ne_zero
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne_zero
      have h2dvd_u : 2 ∣ u := by
        rw [hm_eq]
        exact dvd_pow_self 2 hm_pos.ne'
      have hu_even : Even u := (even_iff_two_dvd).2 h2dvd_u
      exact (Nat.not_even_iff_odd.mpr huOdd) hu_even
    simpa [hm_zero] using hm_eq
  let m : ℝ :=
    1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
      1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))
  have h11 := theorem_13_11 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d m _hsource _h10 rfl
  have hp5 : 5 ≤ p := by omega
  have huc_gt : (u : ℝ) / (c : ℝ) > ((p : ℝ) ^ 2 - 1) / 6 :=
    (h11.2.2 hp5 _hqeq).2
  rw [_hp_eq, _hceq, hu_one] at huc_gt
  norm_num at huc_gt

private theorem section13_theorem_13_12_case_9_7_b_of_small_exception_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c)
    (_hp_eq : p = 5) (_hqeq : q = 3) (_hceq : c = 7) :
    case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource with hcaseA | hcaseB
  · exact False.elim
      (section13_theorem_13_12_not_case_9_7_a_of_small_exception_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d _hsource _h10 _hpre _hp_eq _hqeq _hceq hcaseA)
  · exact hcaseB

private theorem section13_theorem_13_12_u_dvd_thirty_one_of_case_9_7_b
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hp_eq : p = 5) (hqeq : q = 3) :
    u ∣ 31 := by
  have hdiv : u ∣ (p ^ q - 1) / (p - 1) :=
    Section9.case_9_7_b_u_dvd_sec9 hcaseB
  rw [hp_eq, hqeq] at hdiv
  norm_num at hdiv
  exact hdiv

private theorem section13_coprime_c_u_of_c_eq_seven_u_dvd_thirty_one
    {c u : ℕ} (hceq : c = 7) (hu31 : u ∣ 31) :
    Nat.Coprime c u := by
  subst c
  rcases (Nat.dvd_prime (by decide : Nat.Prime 31)).mp hu31 with hu1 | hu31eq
  · simp [hu1]
  · norm_num [hu31eq]

private theorem section13_theorem_13_12_PC_eq_fitting_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    P ⊔ C = section8FittingSubgroup Smax := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hchoiceData, _hminCE⟩
  calc
    P ⊔ C = P ⊔ subgroupCentralizerIn U P := by rw [hC]
    _ = section8FittingSubgroup Smax := by
      exact (Section8.theorem_8_5_a Smax P U W1 W2 hptypeS).symm

private theorem section13_theorem_13_12_PC_card_coprime_index_of_case_9_7_b_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hcu : Nat.Coprime c u) :
    Nat.Coprime (Nat.card ((P ⊔ C).subgroupOf Smax))
      ((P ⊔ C).subgroupOf Smax).index := by
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨_hcaseB13, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD,
      hc_card, _hd_card, _hU_card, _hrest⟩
  rcases hptypeS with
    ⟨hSF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hSF with ⟨⟨hPS, _hPNormalS, _hPnil, hPHallS⟩, _hSmaxMax⟩
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig with
    ⟨_hMF, _htype, _htypeLarge, _hUcomm, _hfrobUW1, _hPelem, hP_card,
      _huBound, _hcoh, _hTI, _hTau, _hnorm⟩
  have hcaseB9 : Section9.case_9_7_b_data Smax P U W1 W2 ⊥ C p q u := by
    simpa [case_9_7_b_sourceDataForSection13] using _hcaseB
  have h92 : Section9.hypothesis_9_2_statement Smax P U W1 W2 q :=
    Section9.case_9_7_b_hypothesis_9_2_sec9 hcaseB9
  have hBarU : Section9.quotientBarUCardinality U C u :=
    Section9.case_9_7_b_barU_cardinality_sec9 hcaseB9
  have hPC_index : ((P ⊔ C).subgroupOf Smax).index = q * u :=
    Section9.HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9
      Smax P U W1 W2 C q u h92 hBarU
  have hq_pos : 0 < q :=
    (Section9.case_9_7_b_q_prime_sec9 hcaseB9).pos
  have hu_pos : 0 < u :=
    Section9.quotientBarUCardinality_card_pos_sec9 U C u hBarU
  have hqu_pos : 0 < q * u := Nat.mul_pos hq_pos hu_pos
  have hS_card : Nat.card Smax = (p ^ q) * (u * c) * q :=
    section13_smax_card_formula_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hP_card
  have hS_card_P : Nat.card Smax = Nat.card P * (u * c) * q := by
    rw [hS_card, ← hP_card]
  have hPC_card :
      Nat.card ((P ⊔ C).subgroupOf Smax) = Nat.card P * c := by
    apply Nat.mul_left_cancel hqu_pos
    calc
      (q * u) * Nat.card ((P ⊔ C).subgroupOf Smax)
          = ((P ⊔ C).subgroupOf Smax).index *
              Nat.card ((P ⊔ C).subgroupOf Smax) := by rw [hPC_index]
      _ = Nat.card Smax :=
            Subgroup.index_mul_card (H := (P ⊔ C).subgroupOf Smax)
      _ = Nat.card P * (u * c) * q := hS_card_P
      _ = (q * u) * (Nat.card P * c) := by ring
  have hPsub_card : Nat.card (P.subgroupOf Smax) = Nat.card P :=
    natCard_subgroupOf_eq P Smax hPS
  have hP_index : (P.subgroupOf Smax).index = (u * c) * q := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := P))
    calc
      (P.subgroupOf Smax).index * Nat.card P
          = (P.subgroupOf Smax).index * Nat.card (P.subgroupOf Smax) := by
            rw [hPsub_card]
      _ = Nat.card Smax := Subgroup.index_mul_card (H := P.subgroupOf Smax)
      _ = Nat.card P * (u * c) * q := hS_card_P
      _ = (u * c) * q * Nat.card P := by ring
  have hqu_dvd_indexP : q * u ∣ (P.subgroupOf Smax).index := by
    rw [hP_index]
    exact ⟨c, by ring⟩
  have hcopP_index :
      Nat.Coprime (Nat.card P) (P.subgroupOf Smax).index := by
    have hcopPsub :
        Nat.Coprime (Nat.card (P.subgroupOf Smax)) (P.subgroupOf Smax).index :=
      hPHallS.card_coprime_index
    rw [hPsub_card] at hcopPsub
    exact hcopPsub
  have hcopP_qu : Nat.Coprime (Nat.card P) (q * u) :=
    Nat.Coprime.coprime_dvd_right hqu_dvd_indexP hcopP_index
  have hq_dvd_c_sub_one : q ∣ c - 1 :=
    section13_theorem_13_12_q_dvd_c_sub_one_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hc_pos : 0 < c := by
    rw [hc_card]
    exact Nat.card_pos (α := C)
  have hc_one_le : 1 ≤ c := Nat.succ_le_of_lt hc_pos
  have hcop_c_sub_c : Nat.Coprime (c - 1) c := by
    rw [Nat.coprime_self_sub_left hc_one_le]
    exact Nat.coprime_one_left c
  have hcop_q_c : Nat.Coprime q c :=
    Nat.Coprime.of_dvd_left hq_dvd_c_sub_one hcop_c_sub_c
  have hcop_c_qu : Nat.Coprime c (q * u) :=
    hcop_q_c.symm.mul_right _hcu
  have hcop_PC_qu : Nat.Coprime (Nat.card P * c) (q * u) :=
    Nat.Coprime.mul_left hcopP_qu hcop_c_qu
  rw [hPC_card, hPC_index]
  exact hcop_PC_qu

private theorem section13_theorem_13_12_PC_isHall_of_case_9_7_b_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hcu : Nat.Coprime c u) :
    IsHallSubgroup (subgroupPrimeSet (P ⊔ C)) ((P ⊔ C).subgroupOf Smax) := by
  have hPCfit : P ⊔ C = section8FittingSubgroup Smax :=
    section13_theorem_13_12_PC_eq_fitting_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hPCleS : P ⊔ C ≤ Smax := by
    rw [hPCfit]
    exact section8FittingSubgroup_le Smax
  have hcop :
      Nat.Coprime (Nat.card ((P ⊔ C).subgroupOf Smax))
        ((P ⊔ C).subgroupOf Smax).index :=
    section13_theorem_13_12_PC_card_coprime_index_of_case_9_7_b_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource _hcaseB _hcu
  have hPCsubCard :
      Nat.card ((P ⊔ C).subgroupOf Smax) = Nat.card (↥(P ⊔ C)) :=
    natCard_subgroupOf_eq (P ⊔ C) Smax hPCleS
  refine isHallSubgroup_of (π := subgroupPrimeSet (P ⊔ C))
    (H := (P ⊔ C).subgroupOf Smax) ?_ ?_
  · intro r hr
    rw [subgroupPrimeSet]
    change r.val ∣ Nat.card (↥(P ⊔ C))
    rw [← hPCsubCard]
    exact hr
  · intro r hrmem hridx
    have hcard : r.val ∣ Nat.card ((P ⊔ C).subgroupOf Smax) := by
      rw [hPCsubCard]
      simpa [subgroupPrimeSet] using hrmem
    exact r.property.ne_one (Nat.eq_one_of_dvd_coprimes hcop hcard hridx)

private theorem section13_theorem_13_12_PC_nilpotentNormalHall_of_case_9_7_b_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (_hcu : Nat.Coprime c u) :
    section16NilpotentNormalHallIn (P ⊔ C) Smax := by
  have hPCfit : P ⊔ C = section8FittingSubgroup Smax :=
    section13_theorem_13_12_PC_eq_fitting_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource
  have hPCleS : P ⊔ C ≤ Smax := by
    rw [hPCfit]
    exact section8FittingSubgroup_le Smax
  have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
    rw [hPCfit]
    exact section8FittingSubgroup_normal_in Smax
  have hPCnil : Group.IsNilpotent (↥(P ⊔ C)) := by
    rw [hPCfit]
    exact section8FittingSubgroup_isNilpotent Smax
  exact ⟨hPCleS, hPCnormal, hPCnil,
    section13_theorem_13_12_PC_isHall_of_case_9_7_b_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _hcaseB _hcu⟩

private theorem section13_theorem_13_12_PC_nilpotentNormalHall_of_small_exception_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c)
    (_hp5 : 5 ≤ p) (_hplt11 : p < 11) (_hqeq : q = 3) (_hceq : c = 7) :
    section16NilpotentNormalHallIn (P ⊔ C) Smax := by
  have hpc : Nat.Coprime p c :=
    section13_theorem_13_12_p_c_coprime_of_small_exception_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _h10 _hpre _hp5 _hplt11 _hqeq _hceq
  have hp_eq : p = 5 :=
    section13_theorem_13_12_p_eq_five_of_small_exception
      _hpre.1 _hp5 _hplt11 _hceq hpc
  have hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section13_theorem_13_12_case_9_7_b_of_small_exception_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _h10 _hpre hp_eq _hqeq _hceq
  have hu31 : u ∣ 31 :=
    section13_theorem_13_12_u_dvd_thirty_one_of_case_9_7_b
      hcaseB hp_eq _hqeq
  have hcu : Nat.Coprime c u :=
    section13_coprime_c_u_of_c_eq_seven_u_dvd_thirty_one _hceq hu31
  exact
    section13_theorem_13_12_PC_nilpotentNormalHall_of_case_9_7_b_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _h10 hcaseB hcu

private theorem section13_theorem_13_12_small_exception_contradiction_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hcne : c ≠ 1)
    (_hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c)
    (_hp5 : 5 ≤ p) (_hplt11 : p < 11) (_hqeq : q = 3) (_hceq : c = 7) :
    False := by
  exact
    (section13_theorem_13_12_not_PC_nilpotentNormalHall_of_c_eq_seven_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _hceq)
      (section13_theorem_13_12_PC_nilpotentNormalHall_of_small_exception_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d _hsource _h10 _hpre _hp5 _hplt11 _hqeq _hceq)

private theorem section13_theorem_13_12_linearBranchFinalContradiction_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hcne : c ≠ 1)
    (hpre : Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q ∧
      u ≤ (p ^ q - 1) / (p - 1) ∧ 0 < c) :
    False := by
  have hpreOrig := hpre
  have hcLower : 2 * q + 1 ≤ c :=
    section13_theorem_13_12_c_lower_bound_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hcne hpre
  rcases hpre with ⟨_hpPrime, _hqPrime, _hpne, hp3, hq3, huBound, _hcpos⟩
  let m : ℝ :=
    1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
      1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))
  have hm :
      m = 1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := rfl
  have h10ineq : (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ) :=
    theorem_13_10 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d m hsource h10 hm
  have _h11 :
      (3 ≤ p → 7 ≤ q → (8 : ℝ) / 10 < m) ∧
        (3 ≤ p → 5 ≤ q → (7 : ℝ) / 10 < m) ∧
          (5 ≤ p → q = 3 → (49 : ℝ) / 100 < m ∧
            (u : ℝ) / (c : ℝ) > ((p : ℝ) ^ 2 - 1) / 6) :=
    theorem_13_11 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d m hsource h10 hm
  have _hq_dvd_c_sub_one : q ∣ c - 1 :=
    section13_theorem_13_12_q_dvd_c_sub_one_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have _hcSevenOrThirteen_of_q_three : q = 3 → c = 7 ∨ 13 ≤ c := by
    intro hqeq
    exact
      section13_theorem_13_12_c_eq_seven_or_thirteen_le_of_q_eq_three_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource hcne hqeq
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hp_one : 1 < p := by omega
  have hgeom_cast :
      ((((p ^ q - 1) / (p - 1) : ℕ) : ℝ)) =
        ((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) :=
    section13_real_geom_quotient_cast (p := q) (q := p) hp_one
  have hu_geom_nat :
      (u : ℝ) ≤ (((p ^ q - 1) / (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast huBound
  have hu_geom :
      (u : ℝ) ≤ ((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) := by
    simpa [hgeom_cast] using hu_geom_nat
  have hgeom_nonneg :
      0 ≤ ((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) := by
    have hnat_nonneg :
        0 ≤ (((p ^ q - 1) / (p - 1) : ℕ) : ℝ) := by positivity
    simpa [hgeom_cast] using hnat_nonneg
  have hC_le_c : (((2 * q + 1 : ℕ) : ℝ) ≤ (c : ℝ)) := by
    exact_mod_cast hcLower
  have hCpos : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  have huc_le :
      (u : ℝ) / (c : ℝ) ≤
        (((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) /
          ((2 * q + 1 : ℕ) : ℝ) :=
    section13_u_div_c_le_of_le_bounds hu_geom hC_le_c hCpos hgeom_nonneg
  have _hm_upper :
      m <
        ((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) /
            ((2 * q + 1 : ℕ) : ℝ)) *
          (q : ℝ) / ((p : ℝ) ^ (q - 1)) :=
    section13_m_lt_of_u_div_c_le hp_pos hq_pos h10ineq huc_le
  have h11a := _h11.1
  have h11b := _h11.2.1
  have h11c := _h11.2.2
  have hm_qp :
      m < ((q : ℝ) * (p : ℝ)) /
        (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) :=
    lt_trans _hm_upper (section13_m_upper_lt_qp_ratio hp_one hq_pos)
  by_cases hp_eq_three : p = 3
  · exact section13_numeric_contradiction_of_p_eq_three _hqPrime _hpne hq3
      h11a h11b hm_qp hp_eq_three
  · have hp5 : 5 ≤ p :=
      section13_five_le_of_prime_three_le_ne_three _hpPrime hp3 hp_eq_three
    have hqeq : q = 3 :=
      section13_q_eq_three_of_five_le_numeric _hqPrime hp5 hq3 h11b hm_qp
    rcases h11c hp5 hqeq with ⟨hm_gt49, _huc_gt⟩
    rcases _hcSevenOrThirteen_of_q_three hqeq with hc7 | hc13
    · have hp_lt11 : p < 11 := by
        by_contra hnot
        have hp11 : 11 ≤ p := by omega
        have hm_high49 : m < (49 : ℝ) / 100 := by
          exact lt_trans _hm_upper (by
            simpa [hqeq] using
              (section13_q_three_c_seven_upper_lt_49_100_of_eleven_le
                hp11 hqeq))
        linarith
      exact
        section13_theorem_13_12_small_exception_contradiction_of_sourceContext
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          p q u v c d hsource h10 hcne hpreOrig hp5 hp_lt11 hqeq hc7
    · have hC13_le_c : (13 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc13
      have huc_le13 :
          (u : ℝ) / (c : ℝ) ≤
            (((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) / (13 : ℝ) :=
        section13_u_div_c_le_of_le_bounds hu_geom hC13_le_c (by norm_num)
          hgeom_nonneg
      have hm_upper13 :
          m <
            ((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) / (13 : ℝ)) *
              (q : ℝ) / ((p : ℝ) ^ (q - 1)) :=
        section13_m_lt_of_u_div_c_le hp_pos hq_pos h10ineq huc_le13
      have hm_high49 : m < (49 : ℝ) / 100 :=
        lt_trans hm_upper13
          (section13_q_three_c_thirteen_upper_lt_49_100 hp5 hqeq)
      linarith

private theorem section13_theorem_13_12_ne_one_contradiction_of_linearCharacter_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (_hcne : c ≠ 1) :
    False := by
  exact section13_theorem_13_12_linearBranchFinalContradiction_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
    _hsource _h10 _hcne
    (section13_theorem_13_12_linearComparisonPrereqs_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _h10)

private theorem section13_theorem_13_12_c_eq_one_of_linearCharacter_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    c = 1 := by
  by_contra hcne
  exact False.elim
    (section13_theorem_13_12_ne_one_contradiction_of_linearCharacter_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10 hcne)

/-- Proof placeholder for `theorem_13_12_statement`. -/
public theorem theorem_13_12
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      c = 1 := by
  intro hsource
  by_cases h10 : theorem_13_10_hypothesis Smax P C Sfam p q u
  · exact section13_theorem_13_12_c_eq_one_of_linearCharacter_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  · rcases hsource with
      ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotationData⟩
    have h3 := theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d (by
        exact ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD,
          hc_card, _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS,
          _hDadeT, _hnotationData⟩)
    rcases h3.2 h10 with ⟨hC_bot, _hcaseB97, _hu⟩
    calc
      c = Nat.card C := hc_card
      _ = Nat.card (⊥ : Subgroup G) := by rw [hC_bot]
      _ = 1 := by simp
end CFSG.Section13
