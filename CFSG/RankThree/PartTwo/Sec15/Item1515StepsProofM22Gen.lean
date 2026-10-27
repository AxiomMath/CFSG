module

import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def KS15M22GenImage : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
      Nat.card (((T ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 16

namespace Proof1515

variable {G : Type} [Group G] [Finite G]

theorem checkSL_m22_seven : ∀ q < 110, 2 ≤ q → q ^ 3 ∣ 1330560 →
    443520 % (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)) = 0 →
    (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)) % 7 = 0 := by
  decide +kernel

theorem checkSU_m22_seven : ∀ q < 110, 3 ≤ q → q ^ 3 ∣ 1330560 →
    443520 % (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1)) = 0 →
    (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1)) % 7 = 0 := by
  decide +kernel

theorem lt_110_of_cube_dvd {q : ℕ} (h : q ^ 3 ∣ 1330560) : q < 110 := by
  by_contra hq
  have h1 : 110 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hq) 3
  have h2 := Nat.le_of_dvd (by norm_num) h
  omega

theorem seven_dvd_of_projSL {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K) (hd : Nat.card X ∣ 443520) :
    7 ∣ Nat.card X := by
  have hc := KFacts.KS14.card_projSL_three_mul_gcd K
  rw [← Nat.card_congr e.toEquiv] at hc
  set q := Nat.card K with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hg : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hq3 : q ^ 3 ∣ 1330560 := by
    have h1 : q ^ 3 ∣ Nat.card X * Nat.gcd 3 (q - 1) := hc ▸ Dvd.intro _ rfl
    exact h1.trans (Nat.mul_dvd_mul hd (Nat.gcd_dvd_left 3 _))
  have hX : Nat.card X = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
    rw [← hc, Nat.mul_div_cancel _ hg]
  rw [hX] at hd ⊢
  exact Nat.dvd_of_mod_eq_zero (checkSL_m22_seven q (lt_110_of_cube_dvd hq3) hq2 hq3
    (Nat.mod_eq_zero_of_dvd hd))

theorem seven_dvd_of_projSU {X : Type} [Group X] (p f : ℕ) [Fact p.Prime] (hq : 2 < p ^ f)
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f) (hd : Nat.card X ∣ 443520) :
    7 ∣ Nat.card X := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hc := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  rw [← Nat.card_congr e.toEquiv] at hc
  set q := p ^ f with hqdef
  have hg : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hq3 : q ^ 3 ∣ 1330560 := by
    have h1 : q ^ 3 ∣ Nat.card X * Nat.gcd 3 (q + 1) := hc ▸ Dvd.intro _ rfl
    exact h1.trans (Nat.mul_dvd_mul hd (Nat.gcd_dvd_left 3 _))
  have hX : Nat.card X = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
    rw [← hc, Nat.mul_div_cancel _ hg]
  rw [hX] at hd ⊢
  exact Nat.dvd_of_mod_eq_zero (checkSU_m22_seven q (lt_110_of_cube_dvd hq3) hq hq3
    (Nat.mod_eq_zero_of_dvd hd))

theorem card_quot_dvd_of_eq_sup {K L Y : Subgroup G} (hKL : K ≤ L) (hKY : K ≤ Y)
    (hY : Y = K ⊔ CFSG.Open.pCoreOf 2 Y) :
    Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ∣
      Nat.card ((K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set f := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hKL) with hf
  set g := (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)).comp (Subgroup.inclusion hKY) with hg
  have hKN : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hO2 : CFSG.pCore 2 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y := pCore_two_le_pPrimeCore_three
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥Y) q
    have hy : (y : G) ∈ ((K ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hY]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at hy
    obtain ⟨k, hk, n, hn, hkn⟩ := Set.mem_mul.mp hy
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hyn : (Subgroup.inclusion hKY ⟨k, hk⟩)⁻¹ * y = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hkn, Subgroup.coe_subtype]
      group
    rw [hyn]
    exact hO2 (by exact hn')
  have hker : f.ker ≤ g.ker := by
    have hn : (f.ker.map g).Normal := f.normal_ker.map g hgs
    have hmap : f.ker.map (Subgroup.inclusion hKL) ≤ θ := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hdvd : Nat.card f.ker ∣ Nat.card θ := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKL)]
      exact Subgroup.card_dvd_of_le hmap
    have hcop : Nat.Coprime 3 (Nat.card (f.ker.map g)) :=
      Nat.Coprime.coprime_dvd_right ((Subgroup.card_map_dvd _ g).trans hdvd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore)
    have hle : f.ker.map g ≤ CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := le_sSup ⟨hn, hcop⟩
    rw [CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three, le_bot_iff,
      Subgroup.map_eq_bot_iff] at hle
    exact hle
  have h1 : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = Nat.card (↥K ⧸ g.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv).symm
  have h2 : Nat.card (↥K ⧸ g.ker) ∣ Nat.card (↥K ⧸ f.ker) := Subgroup.index_dvd_of_le hker
  have h3 : Nat.card (↥K ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h4 : f.range = (K.subgroupOf L).map (QuotientGroup.mk' θ) := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [h1, ← h4, ← h3]
  exact h2

section Seven


theorem seven_dvd_card_quot_of_m22
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h148 : Item148 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8)
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)
    {Y : Subgroup G} (hY4 : Y ∈ scriptY4 A (lB A)) (hYΔ : Y = deltaZero A (lB A) Y)
    (hd : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ∣ 443520) :
    7 ∣ Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
  have hL443 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have hnoJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' L' hc' hL'
    refine ⟨fun φJ => ?_⟩
    have hst : Sec14Std G A c' L' :=
      { h.toSec14Std with zpowers_mem_omegaA := hc', mem_lA := hL' }
    obtain ⟨Le, hLe, hJe⟩ := allPointsHJ_of_j2 h134 h48 hst ⟨φJ⟩ c h.zpowers_mem_omegaA
    obtain ⟨φe⟩ := hJe
    have h3e : 3 ∣ Nat.card Le :=
      three_dvd_card_of_thetaQuot (by rw [Nat.card_congr φe.toEquiv, hJc]; norm_num)
    have heq : Le = L := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Le hLe.1 h3e
    subst heq
    have h1 := Nat.card_congr φe.toEquiv
    rw [hL443, hJc] at h1
    omega
  have hq := isQuasisimple_quot_pPrimeCore hY4
  have hcard : ∀ {S : Type} [Mul S], (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ≃* S →
      Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = Nat.card S := fun e => Nat.card_congr e.toEquiv
  rcases cases148_of_mem_scriptY4 h148 h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ | ⟨⟨φ10⟩, -, -⟩ |
      ⟨c', L', n, m, hc', hL', hn, -, hiso', -⟩
  · rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, -, hε⟩ | ⟨hJ, -⟩
    · obtain ⟨φ⟩ := hφ
      rcases (h.chosen136.2 c' hc' L' hL').1 with hJ' | hL3 | h7 | hM | hM12
      · obtain ⟨φJ⟩ := hJ'
        exact ((hnoJ c' L' hc' hL').false φJ).elim
      · obtain ⟨p, e, hp, he, hiso⟩ := hL3
        rcases hiso with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
        · exact seven_dvd_of_projSL _ (φ.trans ψ) hd
        · by_cases hq2 : 2 < p ^ e
          · exact seven_dvd_of_projSU p e hq2 (φ.trans ψ) hd
          · exfalso
            have h2 : p ^ e = 2 := by
              have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
              omega
            obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
            have := isSolvable_projSU_two
            have hsol : Group.IsSolvable (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
              Group.isSolvable_of_isSolvable_injective (f := (φ.trans ψ).toMonoidHom)
                (φ.trans ψ).injective
            have : Nontrivial (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
              CFSG.LocalCores.isQuasisimple_nontrivial hq
            have : Group.IsPerfect (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := hq.1
            exact Group.IsPerfect.not_isSolvable _ hsol
      · obtain ⟨ψ⟩ := h7
        rw [hcard (φ.trans ψ), card_alternatingGroup_seven]
        norm_num
      · obtain ⟨ψ⟩ := hM
        rw [hcard (φ.trans ψ), KFacts.KS14.card_nativeM22]
        norm_num
      · exfalso
        obtain ⟨ψ⟩ := hM12
        rw [hcard (φ.trans ψ), KFacts.KS14.card_nativeM12] at hd
        norm_num at hd
    · obtain ⟨φ⟩ := h7
      rw [hcard φ, card_alternatingGroup_seven]
      norm_num
    · rcases hε with ⟨⟨ψ⟩⟩ | ⟨hq2, ⟨ψ⟩⟩
      · exact seven_dvd_of_projSL _ ψ hd
      · exact seven_dvd_of_projSU p f hq2 ψ hd
    · obtain ⟨φJ⟩ := hJ
      exact ((hnoJ c' L' hc' hL').false φJ).elim
  · exact ((hnoJ c' L' hc' hL').false φJ).elim
  · exfalso
    rw [hcard φ10, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hd
    norm_num at hd
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso' with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
    · exact seven_dvd_of_projSL _ ψ hd
    · refine seven_dvd_of_projSU 2 (3 * n) ?_ ψ hd
      calc 2 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Seven

theorem pCoreOf_two_le_of_mem_scriptQPiStar {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A) (h3L : 3 ∣ Nat.card L)
    {T : Subgroup G} (hT : T ∈ scriptQPiStar A (lB A)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2)) :
    CFSG.Open.pCoreOf 2 L ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := CFSG.Open.pCoreOf 2 L with hO
  obtain ⟨⟨hTq, hTH⟩, hT2⟩ := hT.prop
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := Sec16.normalizer_zpowers_le_normalizer_L h h3L
  have hLH : L ≤ H := (le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1).trans
    (centralizer_singleton_le_normalizer_zpowers c)
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    (hTH.trans hHL).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hT2' : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hTO2 : IsPGroup 2 (T ⊔ O : Subgroup G) := IsPGroup.to_sup_of_normal_right' hT2' hO2 hTO
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTq.1.2.2
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    h.toSec13Data.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hATO : A ≤ Subgroup.normalizer ((T ⊔ O : Subgroup G) : Set G) := le_normalizer_sup hAT hAO
  have hTOH : T ⊔ O ≤ H := sup_le hTH ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
  have h3' : ¬ 3 ∣ Nat.card (T ⊔ O : Subgroup G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTO2
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hinv : T ⊔ O ∈ invariantPiSubgroups H A (piCompl 3) :=
    (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mpr ⟨hTOH, h3', hATO⟩
  obtain ⟨Q, hQle, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hinv
  let := ker142_normal (LB := lB A) h.isElemAbelian.1 h.mem_A
  obtain ⟨hQq, -⟩ := h142 Q hQ
  have hTOq : T ⊔ O ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQq.1 hQle hATO
  have hmem : T ⊔ O ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨hTOq, hTOH⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hTO2⟩
  have heq := hT.eq_of_ge hmem le_sup_left
  rw [← heq]
  exact le_sup_right

end Proof1515

open Proof1515


theorem ks15M22Gen_of
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h131 : Item131)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135) (himg : KS15M22GenImage) :
    KS15M22Gen := by
  intro G _ _ A c L h hL22 Y hY hYL T hT
  obtain ⟨φL⟩ := hL22
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hL443 : Nat.card (↥L ⧸ θ) = 443520 := by
    rw [Nat.card_congr φL.toEquiv, KFacts.KS14.card_nativeM22]
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot (by rw [hL443]; norm_num)
  have : Nontrivial (↥L ⧸ θ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL443]
    norm_num
  have : Nontrivial CFSG.Blueprint.NativeSporadic.M22 := φL.symm.surjective.nontrivial
  have hθ : θ = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_multFree (h135 G A c L h.toSec13Data h.hypS_or_hypT) ⟨φL⟩ multFree_M22
  have hOT := pCoreOf_two_le_of_mem_scriptQPiStar h (h142 G A c L h) h3L hT
  have hθT : θ ≤ (T ⊓ L).subgroupOf L := by
    intro x hx
    rw [hθ] at hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hOT ⟨x, hx, rfl⟩, x.2⟩
  obtain ⟨-, h9, -⟩ := facts_of_a7_or_m22 h131 h (Or.inr ⟨φL⟩)
  set B := ((A ⊓ L).subgroupOf L).map π with hB
  have hBp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hB'p : IsPGroup 3 ((A ⊓ L).subgroupOf L) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hB9 : Nat.card B = 9 := by
    rw [← Nat.card_congr (mkEquivOfIsPGroup hB'p).toEquiv, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  set R := ((T ⊓ L).subgroupOf L).map π with hR
  have hR16 : Nat.card R = 16 := himg G A c L h ⟨φL⟩ T hT
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
  have hBN : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp
      (Late.le_normalizer_inf hAT h.toSec13Data.le_normalizer (Subgroup.mem_subgroupOf.mp ha).1) y
  have hBR : B ≤ Subgroup.normalizer (R : Set _) :=
    (Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map π)
  have hRinv : R ∈ invariantPiSubgroups ⊤ B (piOf 2) :=
    ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr
      (IsPGroup.of_card (n := 4) (by rw [hR16]; norm_num)), hBR⟩
  have hRmax : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) := by
    obtain ⟨R', hRR', hR'⟩ := Finite.exists_le_maximal
      (p := (· ∈ invariantPiSubgroups ⊤ B (piOf 2))) hRinv
    have hR'3 : R' ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3) := by
      rw [KFacts.KP4.m22_maxInvariant_threePrime_eq_two ⟨φL⟩ hB9]
      exact hR'
    obtain ⟨-, h16, -⟩ := KFacts.KP4.m22_maxInvariant_structure ⟨φL⟩ hB9 hR'3
    have hRR : R = R' := Subgroup.eq_of_le_of_card_ge hRR' (by rw [h16, hR16])
    rw [hRR]
    exact hR'
  set X := ((L ⊓ Y).subgroupOf L).map π with hX
  have hBN' : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((L ⊓ Y).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp
      (Late.le_normalizer_inf h.toSec13Data.le_normalizer hY4.1.2
        (Subgroup.mem_subgroupOf.mp ha).1) y
  have hBX : B ≤ Subgroup.normalizer (X : Set _) :=
    (Subgroup.map_mono hBN').trans (Subgroup.le_normalizer_map π)
  have hdY := card_quot_dvd_of_eq_sup (K := L ⊓ Y) (L := L) inf_le_left inf_le_right hYL
  have hX443 : Nat.card X ∣ 443520 := hL443 ▸ Subgroup.card_subgroup_dvd_card X
  have h7 := seven_dvd_card_quot_of_m22 h (h148 G A c L h) h134 h48 φL hY4 hYΔ
    (hdY.trans hX443)
  have hX7 : 7 ∣ Nat.card X := h7.trans hdY
  have htop := KFacts.KP4.m22_sup_eq_top_of_seven ⟨φL⟩ hB9 hRmax hBX hX7
  set M := ((T ⊓ L) ⊔ (L ⊓ Y)).subgroupOf L with hM
  have hMtop : M = ⊤ := by
    have h1 : R ⊔ X ≤ M.map π := sup_le
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
      (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
    have h2 : M.map π = ⊤ := top_le_iff.mp (htop ▸ h1)
    have h3 := Subgroup.comap_map_eq π M
    rw [h2, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h3
    have hθM : θ ≤ M := hθT.trans fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    rw [sup_eq_left.mpr hθM] at h3
    exact h3.symm
  intro l hl
  have hlM : (⟨l, hl⟩ : ↥L) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hlM

end CFSG.RankThree.PartTwo.Sec15
