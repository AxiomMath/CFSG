module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2Proof1420
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res4Proof1420
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

open Proof1413 in
theorem false_of_m12Q (h1419 : Item1419R) (h1420 : Item1420R)
    (hM12 : Step1421M12R) (hM22 : Step1421M22R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) (hbot : Item145BotS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c : G}
    (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) : False := by
  have hS : Sec14Std G A c L := sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have h146' : Item146 A (lB A) := h146 G A c L hS
  have hbot' := hbot G A c L hS
  have h143' : Item143 A (lB A) := Ronan148Q.item143_of_item143Q (h143 G A c L hS)
  have hcA : c ∈ A := hD.mem_A
  have hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hM12p : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M12).Prime := by
    rw [Sec4.Census.card_m12_eq]
    norm_num
  have hcL : c ∉ L := not_mem_of_mulEquiv_simple hD hM12p φ
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φ (by rw [Sec4.Census.card_m12_eq]; norm_num)
  have hJ12 : Nat.card CFSG.Blueprint.NativeSporadic.J2 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeJ2, Sec4.Census.card_m12_eq]
    norm_num
  have hJ22 : Nat.card CFSG.Blueprint.NativeSporadic.J2 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
    rw [KFacts.KS14.card_nativeJ2, Sec4.Census.card_m22_eq]
    norm_num
  have h1222 : Nat.card CFSG.Blueprint.NativeSporadic.M12 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
    rw [Sec4.Census.card_m12_eq, Sec4.Census.card_m22_eq]
    norm_num
  have hJc : ∀ L₁ ∈ lA A c, IsEmpty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃*
      CFSG.Blueprint.NativeSporadic.J2) := by
    intro L₁ hL₁
    refine ⟨fun χ => ?_⟩
    rcases h1420 G A c₀ L₀ hR hfail c hcΓ L₁ hL₁ with hM | hM
    · obtain ⟨ψ⟩ := hM
      exact (isEmpty_mulEquiv_of_card_ne hJ12).false (χ.symm.trans ψ)
    · obtain ⟨ψ⟩ := hM
      exact (isEmpty_mulEquiv_of_card_ne hJ22).false (χ.symm.trans ψ)
  obtain ⟨h9, d, hdAL, hd1, hreal, hinj⟩ := hM12 G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩
  have hdA : d ∈ A := hdAL.1
  have hd3 : orderOf d = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA.1.2 d hdA) hd1
  obtain ⟨b, hbAL, hbd⟩ : ∃ b ∈ A ⊓ L, b ∉ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers d from hall)
    rw [h9, Nat.card_zpowers, hd3] at hle
    omega
  have hbA : b ∈ A := hbAL.1
  have hF : Frame L c b d := ⟨hD.commute hcA hbA, hD.commute hcA hdA, hD.commute hbA hdA,
    hD.orderOf_eq, hcL, hbAL.2, hdAL.2, hA.1.2 b hbA, hd3, hbd⟩
  have hc3 : c ^ 3 = 1 := hF.hc3
  have h1419c : ∀ i : ℕ, ∃ R ∈ scriptQPiStar A (lB A) L (piOf 2),
      A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c, b * d ^ i} ∧
      {F | F ∈ gammaA A (lB A) ∧ F ≤ Subgroup.closure {c, b * d ^ i}} =
        {Subgroup.zpowers c, Subgroup.closure {c, b * d ^ i} ⊓ L} := by
    intro i
    obtain ⟨R, hR', hCR⟩ := hreal (b * d ^ i) (mul_mem hbA (Subgroup.pow_mem _ hdA i))
      (hF.mul_pow_not_mem_closure i)
    obtain ⟨-, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL (Or.inr (Or.inr ⟨φ⟩)) R hR'
    rw [hCR] at hset
    exact ⟨R, hR', hCR, hset⟩
  have hpt : ∀ i : ℕ, Subgroup.zpowers (b * d ^ i) ∈ gammaA A (lB A) := by
    intro i
    obtain ⟨R, -, -, hset⟩ := h1419c i
    exact (zpowers_eq_of_set_eq hset (mem_closure_right _ _)
      (mul_mem hF.hbL (Subgroup.pow_mem _ hF.hdL i)) (hF.orderOf_mul_pow i)).2
  have hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A) := by simpa using hpt 0
  obtain ⟨U₂, hU₂, hCU₂, hset₁⟩ := h1419c 1
  rw [pow_one] at hCU₂ hset₁
  have hbdL : b * d ∈ L := mul_mem hF.hbL hF.hdL
  have heΓ : Subgroup.zpowers (c * (b * d)) ∉ gammaA A (lB A) := by
    intro he
    rcases eq_or_eq_of_set_eq hset₁ he (Subgroup.zpowers_le.mpr (mul_mem
      (mem_closure_left _ _)
      (mem_closure_right _ _))) with h1 | h1
    · exact hF.e_not_mem_zpowers (h1 ▸ Subgroup.mem_zpowers _)
    · exact hF.e_not_mem (Subgroup.mem_inf.mp (h1 ▸ Subgroup.mem_zpowers (c * (b * d)))).2
  have hfΓ : Subgroup.zpowers (c ^ 2 * (b * d)) ∉ gammaA A (lB A) := by
    intro hf
    rcases eq_or_eq_of_set_eq hset₁ hf (Subgroup.zpowers_le.mpr (mul_mem
      (Subgroup.pow_mem _ (mem_closure_left _ _) 2)
      (mem_closure_right _ _))) with h1 | h1
    · exact hF.f_not_mem_zpowers (h1 ▸ Subgroup.mem_zpowers _)
    · exact hF.f_not_mem (Subgroup.mem_inf.mp (h1 ▸ Subgroup.mem_zpowers (c ^ 2 * (b * d)))).2
  have heA : c * (b * d) ∈ A := mul_mem hcA (mul_mem hbA hdA)
  have hfA : c ^ 2 * (b * d) ∈ A := mul_mem (Subgroup.pow_mem _ hcA 2) (mul_mem hbA hdA)
  have he1 : c * (b * d) ≠ 1 := fun h1 => hF.e_not_mem_zpowers (h1 ▸ one_mem _)
  have hf1 : c ^ 2 * (b * d) ≠ 1 := fun h1 => hF.f_not_mem_zpowers (h1 ▸ one_mem _)
  have hTe := transOn_centralizer_of_not_mem_gammaA h134 h48 h415 hS hbot' h143' hJc heA he1 heΓ
  have hTf := transOn_centralizer_of_not_mem_gammaA h134 h48 h415 hS hbot' h143' hJc hfA hf1 hfΓ
  have hXU₂ := xA_le_normalizer_of_injective hS hcΓ.1 hL h3L hinj hU₂
  have hU₂0 : U₂ ≠ ⊥ := by
    intro h0
    apply hF.not_mem_closure_mul
    rw [← hCU₂, h0]
    refine ⟨hdA, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    rw [hx, one_mul, mul_one]
  have hU₂e : U₂ ≤ Subgroup.centralizer ({c * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₂]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  have hU₂f : U₂ ≤ Subgroup.centralizer ({c ^ 2 * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₂]
    exact mul_mem (Subgroup.pow_mem _ (mem_closure_left _ _) 2)
      (mem_closure_right _ _))
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  obtain ⟨Lb, hLb422⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hbΓ.1
  have hLb : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb422
  rcases h1420 G A c₀ L₀ hR hfail b hbΓ Lb hLb with hMb | hMb
  swap
  ·
    obtain ⟨ψ⟩ := hMb
    obtain ⟨w, hw, hcw⟩ := hM22 G A c₀ L₀ hR hfail b hbΓ Lb hLb ⟨ψ⟩ hcΓ.1
    have h3b : 3 ∣ Nat.card Lb :=
      three_dvd_card_of_mulEquiv ψ (by rw [Sec4.Census.card_m22_eq]; norm_num)
    have hLbL := map_conj_eq_of_zpowers_eq_map hS hw hLb h3b hcw
    have χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22 :=
      (quotThetaEquiv ((Lb.equivMapOfInjective _ (MulAut.conj w).injective).trans
        (MulEquiv.subgroupCongr hLbL))).symm.trans ψ
    exact (isEmpty_mulEquiv_of_card_ne h1222).false (φ.symm.trans χ)
  obtain ⟨ψ⟩ := hMb
  obtain ⟨-, db, hdbAL, -, hrealb, hinjb⟩ := hM12 G A c₀ L₀ hR hfail b hbΓ Lb hLb ⟨ψ⟩
  have hdbA : db ∈ A := hdbAL.1
  have h3Lb : 3 ∣ Nat.card Lb :=
    three_dvd_card_of_mulEquiv ψ (by rw [Sec4.Census.card_m12_eq]; norm_num)
  have h1419b : ∀ R ∈ scriptQPiStar A (lB A) Lb (piOf 2),
      {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R : Set G)} =
        {Subgroup.zpowers b, A ⊓ Subgroup.centralizer (R : Set G) ⊓ Lb} := fun R hR' =>
    (h1419 G A c₀ L₀ hR hfail b hbΓ Lb hLb (Or.inr (Or.inr ⟨ψ⟩)) R hR').2
  have hd_mem : d ∈ Subgroup.closure ({b, db} : Set G) := by
    by_contra hdn
    obtain ⟨R', hR', hCR'⟩ := hrealb d hdA hdn
    have hset' := h1419b R' hR'
    rw [hCR'] at hset'
    have hle1 : Subgroup.zpowers (b * d ^ 1) ≤ Subgroup.closure ({b, d} : Set G) :=
      Subgroup.zpowers_le.mpr (mul_mem (mem_closure_left _ _)
        (Subgroup.pow_mem _ (mem_closure_right _ _) 1))
    have hle2 : Subgroup.zpowers (b * d ^ 2) ≤ Subgroup.closure ({b, d} : Set G) :=
      Subgroup.zpowers_le.mpr (mul_mem (mem_closure_left _ _)
        (Subgroup.pow_mem _ (mem_closure_right _ _) 2))
    have hb0 : Subgroup.zpowers b = Subgroup.zpowers (b * d ^ 0) := by simp
    rcases eq_or_eq_of_set_eq hset' (hpt 1) hle1 with h1 | h1
    · exact hF.zpowers_ne (i := 1) (j := 0) (by norm_num) (h1.trans hb0)
    rcases eq_or_eq_of_set_eq hset' (hpt 2) hle2 with h2 | h2
    · exact hF.zpowers_ne (i := 2) (j := 0) (by norm_num) (h2.trans hb0)
    exact hF.zpowers_ne (i := 1) (j := 2) (by norm_num) (h1.trans h2.symm)
  have hdbL : db ∈ L := hF.mem_of_mem_closure (hD.commute hbA hdbA) (hA.1.2 db hdbA) hd_mem
  have hcl : Subgroup.closure ({b, db} : Set G) ≤ L := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hF.hbL
    · exact hdbL
  obtain ⟨U₁, hU₁, hCU₁⟩ := hrealb (c * d) (mul_mem hcA hdA) fun h => hF.cd_not_mem (hcl h)
  obtain ⟨U₃, hU₃, hCU₃⟩ := hrealb (c ^ 2 * d) (mul_mem (Subgroup.pow_mem _ hcA 2) hdA)
    fun h => hF.c2d_not_mem (hcl h)
  have hne : U₁ ≠ U₃ := by
    intro h13
    apply hF.not_mem_closure_cd
    rw [← hCU₁, h13, hCU₃]
    exact mem_closure_right _ _
  have hXU₃ := xA_le_normalizer_of_injective hS hbΓ.1 hLb h3Lb hinjb hU₃
  have hU₁e : U₁ ≤ Subgroup.centralizer ({c * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₁, hF.e_eq]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  have hU₃f : U₃ ≤ Subgroup.centralizer ({c ^ 2 * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₃, hF.f_eq]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  exact false_of_three hS h146' hbot' hfail hU₁ hU₃ hU₂ hne hU₂0 hXU₂ hXU₃ hU₁e hU₂e hU₂f hU₃f
    hTe hTf

theorem step1421R_ofQ (h1419 : Item1419R) (h1420 : Item1420R)
    (hM12 : Step1421M12R) (hM22 : Step1421M22R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) (hbot : Item145BotS14) : Step1421R := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  rcases h1420 G A c L hR hfail c' hc' L' hL' with hM | hM
  · obtain ⟨φ⟩ := hM
    exact (false_of_m12Q h1419 h1420 hM12 hM22 h422 h45 h134 h48 h415 h143 h146 hbot hR
      hfail hc' hL' φ).elim
  · exact hM

open Proof1413Res2 Proof1413 in
theorem false_of_m12_typedQ (h1419 : Item1419R)
    (hM12 : Step1421M12R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) (hbot : Item145BotS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) (F₀ : Subgroup G)
    (hM12pt : ∀ b : G, Subgroup.zpowers b ∈ gammaA A (lB A) → Subgroup.zpowers b ≠ F₀ →
      ∀ Lb ∈ lA A b,
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12))
    {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (hJc : ∀ L₁ ∈ lA A c,
      IsEmpty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃* CFSG.Blueprint.NativeSporadic.J2))
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) : False := by
  have hS : Sec14Std G A c L := sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have h146' : Item146 A (lB A) := h146 G A c L hS
  have hbot' := hbot G A c L hS
  have h143' : Item143 A (lB A) := Ronan148Q.item143_of_item143Q (h143 G A c L hS)
  have hcA : c ∈ A := hD.mem_A
  have hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hM12p : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M12).Prime := by
    rw [Sec4.Census.card_m12_eq]
    norm_num
  have hcL : c ∉ L := not_mem_of_mulEquiv_simple hD hM12p φ
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φ (by rw [Sec4.Census.card_m12_eq]; norm_num)
  obtain ⟨h9, d, hdAL, hd1, hreal, hinj⟩ := hM12 G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩
  have hdA : d ∈ A := hdAL.1
  have hd3 : orderOf d = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA.1.2 d hdA) hd1
  obtain ⟨b₀, hb₀AL, hb₀d⟩ : ∃ b ∈ A ⊓ L, b ∉ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers d from hall)
    rw [h9, Nat.card_zpowers, hd3] at hle
    omega
  obtain ⟨b, hbAL, hbd, hbF⟩ : ∃ b ∈ A ⊓ L, b ∉ Subgroup.zpowers d ∧ Subgroup.zpowers b ≠ F₀ := by
    by_cases h : Subgroup.zpowers b₀ = F₀
    · have hF₀ : Frame L c b₀ d := ⟨hD.commute hcA hb₀AL.1, hD.commute hcA hdA,
        hD.commute hb₀AL.1 hdA, hD.orderOf_eq, hcL, hb₀AL.2, hdAL.2, hA.1.2 b₀ hb₀AL.1, hd3, hb₀d⟩
      refine ⟨b₀ * d, mul_mem hb₀AL hdAL, fun h' => hb₀d ?_, ?_⟩
      · have h1 := mul_mem h' (inv_mem (Subgroup.mem_zpowers d))
        rwa [mul_inv_cancel_right] at h1
      · rw [← h]
        have h1 := hF₀.zpowers_ne (i := 1) (j := 0) (by norm_num)
        simpa using h1
    · exact ⟨b₀, hb₀AL, hb₀d, h⟩
  have hbA : b ∈ A := hbAL.1
  have hF : Frame L c b d := ⟨hD.commute hcA hbA, hD.commute hcA hdA, hD.commute hbA hdA,
    hD.orderOf_eq, hcL, hbAL.2, hdAL.2, hA.1.2 b hbA, hd3, hbd⟩
  have hc3 : c ^ 3 = 1 := hF.hc3
  have h1419c : ∀ i : ℕ, ∃ R ∈ scriptQPiStar A (lB A) L (piOf 2),
      A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c, b * d ^ i} ∧
      {F | F ∈ gammaA A (lB A) ∧ F ≤ Subgroup.closure {c, b * d ^ i}} =
        {Subgroup.zpowers c, Subgroup.closure {c, b * d ^ i} ⊓ L} := by
    intro i
    obtain ⟨R, hR', hCR⟩ := hreal (b * d ^ i) (mul_mem hbA (Subgroup.pow_mem _ hdA i))
      (hF.mul_pow_not_mem_closure i)
    obtain ⟨-, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL (Or.inr (Or.inr ⟨φ⟩)) R hR'
    rw [hCR] at hset
    exact ⟨R, hR', hCR, hset⟩
  have hpt : ∀ i : ℕ, Subgroup.zpowers (b * d ^ i) ∈ gammaA A (lB A) := by
    intro i
    obtain ⟨R, -, -, hset⟩ := h1419c i
    exact (zpowers_eq_of_set_eq hset (mem_closure_right _ _)
      (mul_mem hF.hbL (Subgroup.pow_mem _ hF.hdL i)) (hF.orderOf_mul_pow i)).2
  have hbΓ : Subgroup.zpowers b ∈ gammaA A (lB A) := by simpa using hpt 0
  obtain ⟨U₂, hU₂, hCU₂, hset₁⟩ := h1419c 1
  rw [pow_one] at hCU₂ hset₁
  have hbdL : b * d ∈ L := mul_mem hF.hbL hF.hdL
  have heΓ : Subgroup.zpowers (c * (b * d)) ∉ gammaA A (lB A) := by
    intro he
    rcases eq_or_eq_of_set_eq hset₁ he (Subgroup.zpowers_le.mpr (mul_mem
      (mem_closure_left _ _)
      (mem_closure_right _ _))) with h1 | h1
    · exact hF.e_not_mem_zpowers (h1 ▸ Subgroup.mem_zpowers _)
    · exact hF.e_not_mem (Subgroup.mem_inf.mp (h1 ▸ Subgroup.mem_zpowers (c * (b * d)))).2
  have hfΓ : Subgroup.zpowers (c ^ 2 * (b * d)) ∉ gammaA A (lB A) := by
    intro hf
    rcases eq_or_eq_of_set_eq hset₁ hf (Subgroup.zpowers_le.mpr (mul_mem
      (Subgroup.pow_mem _ (mem_closure_left _ _) 2)
      (mem_closure_right _ _))) with h1 | h1
    · exact hF.f_not_mem_zpowers (h1 ▸ Subgroup.mem_zpowers _)
    · exact hF.f_not_mem (Subgroup.mem_inf.mp (h1 ▸ Subgroup.mem_zpowers (c ^ 2 * (b * d)))).2
  have heA : c * (b * d) ∈ A := mul_mem hcA (mul_mem hbA hdA)
  have hfA : c ^ 2 * (b * d) ∈ A := mul_mem (Subgroup.pow_mem _ hcA 2) (mul_mem hbA hdA)
  have he1 : c * (b * d) ≠ 1 := fun h1 => hF.e_not_mem_zpowers (h1 ▸ one_mem _)
  have hf1 : c ^ 2 * (b * d) ≠ 1 := fun h1 => hF.f_not_mem_zpowers (h1 ▸ one_mem _)
  have hTe := transOn_centralizer_of_not_mem_gammaA h134 h48 h415 hS hbot' h143' hJc heA he1 heΓ
  have hTf := transOn_centralizer_of_not_mem_gammaA h134 h48 h415 hS hbot' h143' hJc hfA hf1 hfΓ
  have hXU₂ := xA_le_normalizer_of_injective hS hcΓ.1 hL h3L hinj hU₂
  have hU₂0 : U₂ ≠ ⊥ := by
    intro h0
    apply hF.not_mem_closure_mul
    rw [← hCU₂, h0]
    refine ⟨hdA, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    rw [hx, one_mul, mul_one]
  have hU₂e : U₂ ≤ Subgroup.centralizer ({c * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₂]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  have hU₂f : U₂ ≤ Subgroup.centralizer ({c ^ 2 * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₂]
    exact mul_mem (Subgroup.pow_mem _ (mem_closure_left _ _) 2)
      (mem_closure_right _ _))
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  obtain ⟨Lb, hLb422⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hbΓ.1
  have hLb : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb422
  obtain ⟨ψ⟩ := hM12pt b hbΓ hbF Lb hLb
  obtain ⟨-, db, hdbAL, -, hrealb, hinjb⟩ := hM12 G A c₀ L₀ hR hfail b hbΓ Lb hLb ⟨ψ⟩
  have hdbA : db ∈ A := hdbAL.1
  have h3Lb : 3 ∣ Nat.card Lb :=
    three_dvd_card_of_mulEquiv ψ (by rw [Sec4.Census.card_m12_eq]; norm_num)
  have h1419b : ∀ R ∈ scriptQPiStar A (lB A) Lb (piOf 2),
      {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R : Set G)} =
        {Subgroup.zpowers b, A ⊓ Subgroup.centralizer (R : Set G) ⊓ Lb} := fun R hR' =>
    (h1419 G A c₀ L₀ hR hfail b hbΓ Lb hLb (Or.inr (Or.inr ⟨ψ⟩)) R hR').2
  have hd_mem : d ∈ Subgroup.closure ({b, db} : Set G) := by
    by_contra hdn
    obtain ⟨R', hR', hCR'⟩ := hrealb d hdA hdn
    have hset' := h1419b R' hR'
    rw [hCR'] at hset'
    have hle1 : Subgroup.zpowers (b * d ^ 1) ≤ Subgroup.closure ({b, d} : Set G) :=
      Subgroup.zpowers_le.mpr (mul_mem (mem_closure_left _ _)
        (Subgroup.pow_mem _ (mem_closure_right _ _) 1))
    have hle2 : Subgroup.zpowers (b * d ^ 2) ≤ Subgroup.closure ({b, d} : Set G) :=
      Subgroup.zpowers_le.mpr (mul_mem (mem_closure_left _ _)
        (Subgroup.pow_mem _ (mem_closure_right _ _) 2))
    have hb0 : Subgroup.zpowers b = Subgroup.zpowers (b * d ^ 0) := by simp
    rcases eq_or_eq_of_set_eq hset' (hpt 1) hle1 with h1 | h1
    · exact hF.zpowers_ne (i := 1) (j := 0) (by norm_num) (h1.trans hb0)
    rcases eq_or_eq_of_set_eq hset' (hpt 2) hle2 with h2 | h2
    · exact hF.zpowers_ne (i := 2) (j := 0) (by norm_num) (h2.trans hb0)
    exact hF.zpowers_ne (i := 1) (j := 2) (by norm_num) (h1.trans h2.symm)
  have hdbL : db ∈ L := hF.mem_of_mem_closure (hD.commute hbA hdbA) (hA.1.2 db hdbA) hd_mem
  have hcl : Subgroup.closure ({b, db} : Set G) ≤ L := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hF.hbL
    · exact hdbL
  obtain ⟨U₁, hU₁, hCU₁⟩ := hrealb (c * d) (mul_mem hcA hdA) fun h => hF.cd_not_mem (hcl h)
  obtain ⟨U₃, hU₃, hCU₃⟩ := hrealb (c ^ 2 * d) (mul_mem (Subgroup.pow_mem _ hcA 2) hdA)
    fun h => hF.c2d_not_mem (hcl h)
  have hne : U₁ ≠ U₃ := by
    intro h13
    apply hF.not_mem_closure_cd
    rw [← hCU₁, h13, hCU₃]
    exact mem_closure_right _ _
  have hXU₃ := xA_le_normalizer_of_injective hS hbΓ.1 hLb h3Lb hinjb hU₃
  have hU₁e : U₁ ≤ Subgroup.centralizer ({c * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₁, hF.e_eq]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  have hU₃f : U₃ ≤ Subgroup.centralizer ({c ^ 2 * (b * d)} : Set G) := le_centralizer_of_mem (by
    rw [hCU₃, hF.f_eq]
    exact mul_mem (mem_closure_left _ _)
      (mem_closure_right _ _))
  exact false_of_three hS h146' hbot' hfail hU₁ hU₃ hU₂ hne hU₂0 hXU₂ hXU₃ hU₁e hU₂e hU₂f hU₃f
    hTe hTf

open Proof1413Res2 Proof1413 in
theorem false_of_m12_awayQ (h1419 : Item1419R)
    (h1420 : Item1420R) (hM12 : Step1421M12R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) (hbot : Item145BotS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) (F₀ : Subgroup G)
    (hM22 : ∀ b : G, Subgroup.zpowers b ∈ gammaA A (lB A) → Subgroup.zpowers b ≠ F₀ →
      ∀ Lb ∈ lA A b,
        IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M22))
    {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) : False := by
  have hJ12 : Nat.card CFSG.Blueprint.NativeSporadic.J2 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeJ2, Sec4.Census.card_m12_eq]
    norm_num
  have hJ22 : Nat.card CFSG.Blueprint.NativeSporadic.J2 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M22 := by
    rw [KFacts.KS14.card_nativeJ2, Sec4.Census.card_m22_eq]
    norm_num
  refine false_of_m12_typedQ h1419 hM12 h422 h45 h134 h48 h415 h143 h146 hbot hR hfail F₀
    (fun b hb hbF Lb hLb => ?_) hcΓ hL (fun L₁ hL₁ => ⟨fun χ => ?_⟩) φ
  · rcases h1420 G A c₀ L₀ hR hfail b hb Lb hLb with hM | hM
    · exact hM
    · obtain ⟨ψ⟩ := hM
      exact ((hM22 b hb hbF Lb hLb).false ψ).elim
  · rcases h1420 G A c₀ L₀ hR hfail c hcΓ L₁ hL₁ with hM | hM
    · obtain ⟨ψ⟩ := hM
      exact (isEmpty_mulEquiv_of_card_ne hJ12).false (χ.symm.trans ψ)
    · obtain ⟨ψ⟩ := hM
      exact (isEmpty_mulEquiv_of_card_ne hJ22).false (χ.symm.trans ψ)

open Proof1413Res2 in
theorem false_of_fixed_pointQ
    (h133 : Item133)
    (h1416 : Item1416R) (hPGL : Item1412NotPGLR) (h1419 : Item1419R) (hM12 : Step1421M12R)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A))
    {L : Subgroup G} (hL : L ∈ lA A c)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hcL : c ∉ L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hmove : ∀ f ∈ A, f ≠ 1 → Subgroup.zpowers f ≠ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G)) :
    False := by
  have hD := hR.toSec14Std.toSec13Data
  obtain ⟨R₀, hR₀⟩ := exists_mem_scriptQPiStar A L (lB A) (piOf 2)
  obtain ⟨-, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL htype R₀ hR₀
  have hmem : A ⊓ Subgroup.centralizer (R₀ : Set G) ⊓ L ∈
      {F | F ∈ gammaA A (lB A) ∧ F ≤ A ⊓ Subgroup.centralizer (R₀ : Set G)} := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨hzΓ, -⟩ := hmem
  obtain ⟨-, -, z, hz, -⟩ := hzΓ.1
  rw [hz] at hzΓ
  have hzc : Subgroup.zpowers z ≠ Subgroup.zpowers c := by
    intro h
    apply hcL
    have h1 : c ∈ Subgroup.zpowers z := h ▸ Subgroup.mem_zpowers c
    rw [← hz] at h1
    exact h1.2
  have hzA : z ∈ A := (zpowers_mem_omegaA_iff.mp hzΓ.1).1
  have hM12pt : ∀ b : G, Subgroup.zpowers b ∈ gammaA A (lB A) →
      Subgroup.zpowers b ≠ Subgroup.zpowers c → ∀ Lb ∈ lA A b,
        Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    fun b hb hbc Lb hLb => m12_of_fixed h133 h1416 hPGL hR hfail hcΓ.1 hW hmove hb hbc hLb
  have hAz : A ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hzA)
  obtain ⟨Lz, hLz422⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hzΓ.1
  have hLz : Lz ∈ lA A z := Sec12.mem_lA_of_mem_lA422 hAz hLz422
  obtain ⟨φ⟩ := hM12pt z hzΓ hzc Lz hLz
  exact false_of_m12_typedQ h1419 hM12 h422 h45 h134 h48 h415 h143 h146 hbot hR hfail
    (Subgroup.zpowers c) hM12pt hzΓ hLz (fun L₁ hL₁ => h1416 G A c₀ L₀ hR hfail z hzΓ.1 L₁ hL₁) φ

open Proof1413Res4 in
theorem le_pPrimeCoreOf_of_not_mem_omegaAQ {A : Subgroup G} (h143 : Ronan148Q.Item143Q A (lB A))
    {y : G} (hyA : y ∈ A) (hy1 : y ≠ 1) (hyΩ : Subgroup.zpowers y ∉ omegaA A)
    (hnoHJ : ∀ b : G, Subgroup.zpowers b ∈ omegaA A → ∀ Lb ∈ lA A b,
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hX : ¬ 2 ∣ Nat.card ↥(xA A)) {R : Subgroup G} (hR𝓠 : R ∈ scriptQ A (lB A))
    (hR2 : IsPGroup 2 R) (hRy : R ≤ Subgroup.centralizer ({y} : Set G)) :
    R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({y} : Set G))) A
      (piCompl 3))) (bot_mem_invariantPiSubgroups _ A (piCompl 3))
  have hΔ : delta A (lB A) (Subgroup.centralizer ({y} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rcases (h143 y hyA hy1 hyΩ Q hQ).2 with h | ⟨b, d, Lb, hb, hLb, ⟨χ⟩, -⟩
    · exact h
    · exact ((hnoHJ b hb Lb hLb).false χ).elim
  have hRΔ : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := hΔ ▸ le_delta hR𝓠 hRy
  have hXy : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.centralizer ({y} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyA))
  have hsup : pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (pPrimeCoreOf_le 3 _) hXy
  have hnormal : ((pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G))).subgroupOf
      (pPrimeCoreOf 3 (Subgroup.centralizer ({y} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (hsup.trans (le_normalizer_pPrimeCoreOf 3 _))
  have hcop : (Nat.card ↥(pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))).Coprime 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hX).symm
  exact CFSG.AGLEmbedding.le_of_le_sup_of_coprime_card_of_le hRΔ le_sup_left le_sup_right
    hnormal hR2 hcop hRΔ

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
