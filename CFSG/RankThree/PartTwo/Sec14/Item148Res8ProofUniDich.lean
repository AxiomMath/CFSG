module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUniBasic
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofTheta
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUniDickson
public import CFSG.GH74.GLS.IVK.L2.Fixed

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_card_pow)

variable {f : ℕ} {K : Type} [Field K]

section Fields

variable (h : UnitaryFieldData 2 f K)

noncomputable abbrev barEquiv : K ≃+* K :=
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  CFSG.LieType.BorelTits.unitaryInvolution K 2 f

theorem barEquiv_apply (c : K) : barEquiv h c = h.bar c := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  rw [UnitaryFieldData.bar_apply]
  exact CFSG.LieType.BorelTits.unitaryInvolution_apply K 2 f c

theorem orderOf_barEquiv : orderOf (barEquiv h) = 2 := by
  apply orderOf_eq_prime
  · ext c
    rw [pow_two]
    show barEquiv h (barEquiv h c) = c
    rw [barEquiv_apply, barEquiv_apply, UnitaryFieldData.bar_bar]
  · intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    rw [← barEquiv_apply, h1]
    rfl

theorem fixedField_barEquiv : fixedField (barEquiv h) = h.fixedField := by
  ext c
  rw [mem_fixedField_iff, barEquiv_apply, UnitaryFieldData.mem_fixedField]

theorem card_barFixed : Nat.card h.fixedField = 2 ^ f := by
  have := h.finite
  have h1 := fixedField_card_pow (barEquiv h)
  rw [orderOf_barEquiv, h.card, fixedField_barEquiv] at h1
  exact Nat.pow_left_injective (n := 2) (by norm_num)
    (show Nat.card h.fixedField ^ 2 = (2 ^ f) ^ 2 by rw [h1, ← pow_mul, mul_comm])

theorem card_inf_barFixed {n : ℕ} (h : UnitaryFieldData 2 (3 * n) K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : Nat.card (fixedField σ ⊓ h.fixedField : Subfield K) = 2 ^ n := by
  have := h.finite
  have hcomm : Commute σ (barEquiv h) := by
    ext c
    show σ (barEquiv h c) = barEquiv h (σ c)
    rw [barEquiv_apply, barEquiv_apply, UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply,
      map_pow]
  have hτ : orderOf (σ * barEquiv h) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hσ, orderOf_barEquiv]; norm_num), hσ,
      orderOf_barEquiv]
  have hfix : fixedField (σ * barEquiv h) = fixedField σ ⊓ h.fixedField := by
    ext c
    rw [Subfield.mem_inf, mem_fixedField_iff, mem_fixedField_iff, UnitaryFieldData.mem_fixedField,
      ← barEquiv_apply]
    constructor
    · intro hc
      have hpow : ∀ k : ℕ, ((σ * barEquiv h) ^ k) c = c := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ]
          show ((σ * barEquiv h) ^ k) ((σ * barEquiv h) c) = c
          rw [show (σ * barEquiv h) c = c from hc, ih]
      have hb2 : barEquiv h ^ 2 = 1 := by rw [← orderOf_barEquiv h, pow_orderOf_eq_one]
      have hs3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
      have e3 : (σ * barEquiv h) ^ 3 = barEquiv h := by
        rw [hcomm.mul_pow, hs3, one_mul, pow_succ, hb2, one_mul]
      have e4 : (σ * barEquiv h) ^ 4 = σ := by
        rw [hcomm.mul_pow, show (4 : ℕ) = 3 + 1 by rfl, pow_succ, hs3, one_mul,
          show (3 + 1 : ℕ) = 2 * 2 by rfl, pow_mul, hb2, one_pow, mul_one]
      refine ⟨?_, ?_⟩
      · have := hpow 4
        rwa [e4] at this
      · have := hpow 3
        rwa [e3] at this
    · rintro ⟨h1, h2⟩
      show σ (barEquiv h c) = c
      rw [h2, h1]
  have h1 := fixedField_card_pow (σ * barEquiv h)
  rw [hτ, h.card, hfix] at h1
  exact Nat.pow_left_injective (by norm_num) (h1.trans (by ring))

end Fields

section Dichotomy

theorem rankOneSL_mul (v φ : Fin 3 → K) (hv : φ ⬝ᵥ v = 0) (x y : K) :
    rankOneSL v φ hv x * rankOneSL v φ hv y = rankOneSL v φ hv (x + y) := by
  apply Subtype.ext
  show (1 + x • vecMulVec v φ) * (1 + y • vecMulVec v φ) = 1 + (x + y) • vecMulVec v φ
  have hN2 : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hv, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hN2, smul_zero, add_zero, add_smul]
  abel

theorem rankOneSL_zero (v φ : Fin 3 → K) (hv : φ ⬝ᵥ v = 0) : rankOneSL v φ hv 0 = 1 := by
  apply Subtype.ext
  show 1 + (0 : K) • vecMulVec v φ = 1
  rw [zero_smul, add_zero]

theorem barVec_dot_comm (h : UnitaryFieldData 2 f K) (a b : Fin 3 → K) :
    barVec h b ⬝ᵥ a = h.bar (barVec h a ⬝ᵥ b) := by
  simp [dotProduct, barVec_apply, map_sum, map_mul, UnitaryFieldData.bar_bar, mul_comm]

variable [CharP K 2]

theorem uni_rootSet_dichotomy {n : ℕ}
    (h : UnitaryFieldData 2 (3 * n) K) (hn : 3 ≤ n) (hodd : Odd n) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hHU : H ≤ (suToSL h).range) {a b : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0)
    (hb : barVec h b ⬝ᵥ b = 0) (hab : barVec h a ⬝ᵥ b = 1)
    (hrat_a : ∀ c ∈ (fixedField σ ⊓ h.fixedField : Subfield K),
      rankOneSL a (barVec h a) ha c ∈ H)
    (hrat_b : ∀ c ∈ (fixedField σ ⊓ h.fixedField : Subfield K),
      rankOneSL b (barVec h b) hb c ∈ H) :
    (∀ c, rankOneSL a (barVec h a) ha c ∈ H → c ∈ (fixedField σ ⊓ h.fixedField : Subfield K)) ∨
      (∀ c, h.bar c = c → rankOneSL a (barVec h a) ha c ∈ H) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Fq := (fixedField σ ⊓ h.fixedField : Subfield K) with hFq
  set FQ := h.fixedField with hFQ
  have hcardFq : Nat.card Fq = 2 ^ n := card_inf_barFixed h hσ
  have hcardFQ : Nat.card FQ = 2 ^ (3 * n) := card_barFixed h
  have hba : barVec h b ⬝ᵥ a = 1 := by rw [barVec_dot_comm, hab, map_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : barVec h (0 : Fin 3 → K) = 0 := by
      ext i
      simp [barVec_apply]
    rw [h0, zero_dotProduct] at hab
    exact zero_ne_one hab
  obtain ⟨θ, hθu₀, hθl₀⟩ := exists_theta ha hb (by rw [hab]; exact one_ne_zero)
    (by rw [hba]; exact one_ne_zero)
  have hθu : ∀ x, θ (uSL x) = rankOneSL a (barVec h a) ha x := fun x => by
    rw [hθu₀, hab, inv_one, mul_one]
  have hθl : ∀ y, θ (lSL y) = rankOneSL b (barVec h b) hb y := fun y => by
    rw [hθl₀, hba, inv_one, mul_one]
  set ιQ := SpecialLinearGroup.map (n := Fin 2) FQ.subtype with hιQ
  set G := (H.comap θ).comap ιQ with hG
  have hιu : ∀ x : FQ, ιQ (uSL x) = uSL (x : K) := by
    intro x
    apply Subtype.ext
    rw [hιQ, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, uSL_coe, uSL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hιl : ∀ y : FQ, ιQ (lSL y) = lSL (y : K) := by
    intro y
    apply Subtype.ext
    rw [hιQ, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, lSL_coe, lSL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmemu : ∀ x : FQ, uSL x ∈ G ↔ rankOneSL a (barVec h a) ha (x : K) ∈ H := by
    intro x
    show θ (ιQ (uSL x)) ∈ H ↔ _
    rw [hιu, hθu]
  set S : AddSubgroup FQ :=
    { carrier := {x | rankOneSL a (barVec h a) ha (x : K) ∈ H}
      add_mem' := by
        intro x y hx hy
        show rankOneSL a (barVec h a) ha ((x : K) + y) ∈ H
        rw [← rankOneSL_mul]
        exact H.mul_mem hx hy
      zero_mem' := by
        show rankOneSL a (barVec h a) ha ((0 : FQ) : K) ∈ H
        rw [ZeroMemClass.coe_zero, rankOneSL_zero]
        exact H.one_mem
      neg_mem' := by
        intro x hx
        show rankOneSL a (barVec h a) ha (-(x : K)) ∈ H
        have e : rankOneSL a (barVec h a) ha (-(x : K)) =
            (rankOneSL a (barVec h a) ha (x : K))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, rankOneSL_mul, neg_add_cancel, rankOneSL_zero]
        rw [e]
        exact H.inv_mem hx } with hS
  have hS1 : (1 : FQ) ∈ S := by
    show rankOneSL a (barVec h a) ha ((1 : FQ) : K) ∈ H
    exact hrat_a 1 Fq.one_mem
  obtain ⟨m, hm⟩ : ∃ m, Nat.card S = 2 ^ m := by
    have hdvd := AddSubgroup.card_addSubgroup_dvd_card S
    rw [hcardFQ] at hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩
  have hFqS : ∀ c ∈ Fq, ∃ x : FQ, (x : K) = c ∧ x ∈ S := by
    intro c hc
    exact ⟨⟨c, (Subfield.mem_inf.mp hc).2⟩, rfl, hrat_a c hc⟩
  have hle1 : 2 ^ n ≤ 2 ^ m := by
    rw [← hcardFq, ← hm]
    refine Nat.card_le_card_of_injective (fun c : Fq => (⟨⟨c, (Subfield.mem_inf.mp c.2).2⟩,
      hrat_a c c.2⟩ : S)) ?_
    intro c c' hcc
    exact Subtype.ext (congrArg (fun x : S => ((x : FQ) : K)) hcc)
  have hle2 : 2 ^ m ≤ 2 ^ (3 * n) := by
    rw [← hm, ← hcardFQ]
    exact Nat.card_le_card_of_injective (fun x : S => (x : FQ)) Subtype.val_injective
  have hmn : n ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle1
  have hm3 : m ≤ 3 * n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle2
  have : CharP FQ 2 := inferInstance
  have hu : uRootAdd S ≤ G := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hmemu x).mpr hx
  have hU : ∀ x : FQ, uSL x ∈ G → x ∈ S := fun x hx => (hmemu x).mp hx
  obtain ⟨r, hr, hcardG⟩ := exists_odd_card_eq_add S hS1 hm G hu hU
  have hxG : uSL (1 : FQ) ∈ G := hu ⟨1, hS1, rfl⟩
  have hyG : lSL (1 : FQ) ∈ G := by
    show θ (ιQ (lSL 1)) ∈ H
    rw [hιl, hθl]
    exact hrat_b 1 Fq.one_mem
  have h2FQ : (1 : FQ) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hx2 : uSL (1 : FQ) ^ 2 = 1 := by
    rw [pow_two, uSL_mul, h2FQ]
    exact SpecialLinearGroup.transvection_coeff_zero _
  have hy2 : lSL (1 : FQ) ^ 2 = 1 := by
    rw [pow_two, ← SpecialLinearGroup.transvection_add, h2FQ]
    exact SpecialLinearGroup.transvection_coeff_zero _
  have hxy : uSL (1 : FQ) * lSL 1 ≠ lSL 1 * uSL 1 := by
    intro hc
    have h00 := congrFun (congrFun (congrArg
      (fun X : SpecialLinearGroup (Fin 2) FQ => (X : Matrix (Fin 2) (Fin 2) FQ)) hc) 0) 0
    have e1 : ((uSL (1 : FQ) * lSL 1 : SpecialLinearGroup (Fin 2) FQ) :
        Matrix (Fin 2) (Fin 2) FQ) = !![1, 1; 0, 1] * !![1, 0; 1, 1] := by
      rw [← uSL_coe, ← lSL_coe]
      rfl
    have e2 : ((lSL (1 : FQ) * uSL 1 : SpecialLinearGroup (Fin 2) FQ) :
        Matrix (Fin 2) (Fin 2) FQ) = !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
      rw [← uSL_coe, ← lSL_coe]
      rfl
    rw [e1, e2] at h00
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hm3' : 3 ≤ m := le_trans hn hmn
  have hdvd := sylow_exp_dvd_of_dickson (K := FQ) (f := 3 * n) (by omega) hcardFQ G hm3' hr
    hcardG hxG hyG hx2 hy2 hxy
  have h3odd : Odd (3 * n) := Nat.odd_mul.mpr ⟨by decide, hodd⟩
  rcases hdvd with ⟨k, hk⟩ | h2m
  swap
  · exfalso
    exact (Nat.not_even_iff_odd.mpr h3odd) (even_iff_two_dvd.mpr ((Dvd.intro m rfl).trans h2m))
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · omega
    · exact hk0
  have hk3 : k ≤ 3 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hk2 : k ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h3odd) ⟨m, by omega⟩
  interval_cases k
  ·
    right
    have hSm : m = 3 * n := by omega
    have htop : S = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      rw [hm, hcardFQ, hSm]
    intro c hc
    have : (⟨c, hc⟩ : FQ) ∈ S := by rw [htop]; trivial
    exact this
  · exact absurd rfl hk2
  ·
    left
    have hSm : m = n := by omega
    intro c hc
    have hbar : h.bar c = c := bar_eq_of_rankOneSL_mem h ha ha0 (hHU hc)
    set ι : Fq → S := fun c => ⟨⟨c, (Subfield.mem_inf.mp c.2).2⟩, hrat_a c c.2⟩ with hι
    have hιinj : Function.Injective ι := by
      intro c c' hcc
      exact Subtype.ext (congrArg (fun x : S => ((x : FQ) : K)) hcc)
    have hιbij : Function.Bijective ι :=
      hιinj.bijective_of_nat_card_le (by rw [hm, hcardFq, hSm])
    obtain ⟨c', hc'⟩ := hιbij.2 ⟨⟨c, hbar⟩, hc⟩
    have : (c' : K) = c := congrArg (fun x : S => ((x : FQ) : K)) hc'
    rw [← this]
    exact c'.2

end Dichotomy

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
