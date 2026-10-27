module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofPL
import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped Pointwise

@[expose] noncomputable def Step1411WGammaLaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ a : G, Subgroup.zpowers a ∈ gammaA A (lB A) → ∀ La ∈ lA A a,
        ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2),
        ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2),
          S ≤ La → T ≤ La →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) S T

namespace Proof1418Res3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_pow_mul_inv_mem {M : Subgroup G} {m x : G} (hm : m ∈ M)
    (hx : x ∈ Subgroup.normalizer (M : Set G)) (n : ℕ) : (m * x) ^ n * (x ^ n)⁻¹ ∈ M := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : x ^ n ∈ Subgroup.normalizer (M : Set G) := pow_mem hx n
    have h1 : x ^ n * m * (x ^ n)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hxn m).mp hm
    have e : (m * x) ^ (n + 1) * (x ^ (n + 1))⁻¹ =
        ((m * x) ^ n * (x ^ n)⁻¹) * (x ^ n * m * (x ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact mul_mem ih h1

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {M : Subgroup G} {x : G} {a b : ℕ} (ha : x ^ a ∈ M)
    (hb : x ^ b ∈ M) (hab : Nat.Coprime a b) : x ∈ M := by
  have hab' : Nat.gcd a b = 1 := hab
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab', Nat.cast_one] at h
  have e : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

omit [Finite G] in
theorem le_of_le_sup_of_odd {M X S : Subgroup G} (hXM : X ≤ Subgroup.normalizer (M : Set G))
    (hX : ¬ 2 ∣ Nat.card X) (hS : IsPGroup 2 S) (hSMX : S ≤ M ⊔ X) : S ≤ M := by
  intro s hs
  have hs' : s ∈ ((M : Set G) * (X : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M X hXM]
    exact hSMX hs
  obtain ⟨m, hm, x, hxX, rfl⟩ := hs'
  obtain ⟨k, hk⟩ := hS ⟨m * x, hs⟩
  have hk' : (m * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : x ^ 2 ^ k ∈ M := by
    have h := mul_pow_mul_inv_mem hm (hXM hxX) (2 ^ k)
    rw [hk', one_mul] at h
    simpa using inv_mem h
  have h2 : x ^ Nat.card X ∈ M := by
    rw [orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard X hxX)]
    exact one_mem _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).mpr hX)
  exact mul_mem hm (mem_of_pow_mem_of_coprime h1 h2 hcop)

theorem fusionIsSylowIn_sup_of_odd {D O S₀ : Subgroup G}
    (hDO : D ≤ Subgroup.normalizer (O : Set G)) (hO : ¬ 2 ∣ Nat.card O)
    (hS₀ : CFSG.Open.fusionIsSylowIn 2 S₀ D) : CFSG.Open.fusionIsSylowIn 2 S₀ (D ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hS₀.1.trans le_sup_left, hS₀.2.1, fun P hPY hP hS₀P => ?_⟩
  obtain ⟨Q, hQ⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₀
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card D * Nat.card O := by
    rw [← hk]
    exact (Subgroup.card_dvd_of_le hPY).trans (card_sup_dvd_card_mul hDO)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).mpr hO)
  have hdD : 2 ^ k ∣ Nat.card D := hcop.dvd_of_dvd_mul_right hdvd
  have hdQ : 2 ^ k ∣ Nat.card (Q : Subgroup D) := Q.pow_dvd_card_of_pow_dvd_card hdD
  have hQS : Nat.card (Q : Subgroup D) = Nat.card S₀ := by
    rw [← hQ, Subgroup.card_map_of_injective D.subtype_injective]
  rw [hQS] at hdQ
  refine (Subgroup.eq_of_le_of_card_ge hS₀P ?_).symm
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos hdQ

theorem map_conj_mem_scriptQPiStar_centralizer {A : Subgroup G} {a x : G} (haA : a ∈ A)
    (hx : x ∈ xA A) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2)) :
    S.map (MulAut.conj x).toMonoidHom ∈
      scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2) := by
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hXa : xA A ≤ Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  refine maximal_map_conj (W := xA A) (fun V hV y hy => ?_) hS hx
  refine ⟨⟨rank3II_14_4_5 (isNaturalFamily_lB A) (hXA hy) hV.1.1, ?_⟩, ?_⟩
  · rw [← Proof1418Res3.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hXa hy))]
    exact Subgroup.map_mono hV.1.2
  · intro q hq
    exact hV.2 q (by rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq)

theorem exists_conj_le_of_gamma (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h1413 : Item1413CR) (h142 : Item142AllS14) (hbot : Item145BotS14) {A L : Subgroup G}
    {c : G} (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {a : G}
    (ha : Subgroup.zpowers a ∈ gammaA A (lB A)) {La : Subgroup G} (hLa : La ∈ lA A a)
    {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2)) :
    ∃ x ∈ xA A, S.map (MulAut.conj x).toMonoidHom ≤ La := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha.1 hLa
  have hRa : Sec15R G A a La := { toSec14Std := h', hypR := hR.hypR }
  have h3 : 3 ∣ Nat.card La := three_dvd_card_of_types148 (h'.chosen136.2 a ha.1 La hLa).1
  have hA3 : IsPGroup 3 A := h'.isE27.isPGroup
  set H := Subgroup.normalizer (Subgroup.zpowers a : Set G) with hHdef
  set K := k142 A (lB A) a with hKdef
  set O := pPrimeCoreOf 3 K with hOdef
  set X := xA A with hXdef
  have hK : K = La ⊔ pPrimeCoreOf 3 H ⊔ X := Proof1413Res5.eq_k_of_gamma h142 hbot hR ha hLa
  have hOodd : ¬ 2 ∣ Nat.card O :=
    Proof1413Res5.not_two_dvd_pCore_of_gamma h142 hbot hR hfail ha hLa
  have hXodd : ¬ 2 ∣ Nat.card X := Proof1418Res2.not_two_dvd_xA h422 h45 h1413 hR hfail ha
  have hSq : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hSa : S ≤ Subgroup.centralizer ({a} : Set G) := hS.prop.1.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSq.1.2.2
  have hSK : S ≤ K := le_delta hSq (hSa.trans (centralizer_singleton_le_normalizer_zpowers a))
  have hKH : K ≤ H := delta_le H
  have hKLa : K ≤ Subgroup.normalizer (La : Set G) :=
    hKH.trans (Sec17.Sec15R.normalizer_zpowers_le_normalizer_L hRa h3)
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_sSup (S := collectionIn (scriptQ A (lB A)) H) fun Q hQ => hQ.1.1.2.2
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hALa : A ≤ Subgroup.normalizer (La : Set G) := hLa.2.1
  have hXK : X ≤ K := by
    rw [hK]
    exact le_sup_right
  have hOHK : pPrimeCoreOf 3 H ≤ K := by
    rw [hK]
    exact le_sup_right.trans le_sup_left
  have hOH : pPrimeCoreOf 3 H ≤ O :=
    le_pPrimeCoreOf hOHK (hKH.trans (le_normalizer_pPrimeCoreOf 3 H))
      (coprime_card_pPrimeCoreOf 3 H)
  have hXM : X ≤ Subgroup.normalizer ((La ⊔ O : Subgroup G) : Set G) := fun x hx =>
    Proof1418Res3.mem_normalizer_sup (hKLa (hXK hx)) (hKO (hXK hx))
  have hSLO : S ≤ La ⊔ O := by
    refine le_of_le_sup_of_odd hXM hXodd hS2 (hSK.trans ?_)
    rw [hK]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hOH.trans (le_sup_right.trans le_sup_left))) le_sup_right
  have hSO : S ≤ Subgroup.normalizer (O : Set G) := hSK.trans hKO
  set Y := S ⊔ O with hYdef
  set Dd := Y ⊓ La with hDdef
  have hOLa : O ≤ Subgroup.normalizer (La : Set G) := (pPrimeCoreOf_le 3 K).trans hKLa
  have hYK : Y ≤ K := sup_le hSK (pPrimeCoreOf_le 3 K)
  have hYDO : Y ≤ Dd ⊔ O := by
    refine sup_le (fun s hs => ?_) le_sup_right
    have hs' : s ∈ ((La : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left La O hOLa]
      exact hSLO hs
    obtain ⟨l, hl, o, ho, rfl⟩ := hs'
    have hlY : l ∈ Y := by
      have e : l = l * o * o⁻¹ := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left hs) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left ⟨hlY, hl⟩) (Subgroup.mem_sup_right ho)
  have hDOY : Dd ⊔ O ≤ Y := sup_le inf_le_left le_sup_right
  have hYeq : Y = Dd ⊔ O := le_antisymm hYDO hDOY
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    Proof1418Res3.mem_normalizer_sup (hAS hx) (hAO hx)
  have hAD : A ≤ Subgroup.normalizer (Dd : Set G) := fun x hx =>
    Proof1418Res3.mem_normalizer_inf (hAY hx) (hALa hx)
  have hO3 : ¬ 3 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 K)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h
    have hdvd := h.trans (card_sup_dvd_card_mul hSO)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact Proof1418Res3.not_three_dvd_of_two hS2 h1
    · exact hO3 h1
  have hD3 : ¬ 3 ∣ Nat.card Dd := fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨S₀, hS₀, -, hAS₀⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hD3 hAD (inf_le_right : S ⊓ Dd ≤ Dd)
    (hS2.to_le inf_le_left) (fun x hx => Proof1418Res3.mem_normalizer_inf (hAS hx) (hAD hx))
  have hDO : Dd ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans (hYK.trans hKO)
  have hS₀Y : CFSG.Open.fusionIsSylowIn 2 S₀ Y := by
    rw [hYeq]
    exact fusionIsSylowIn_sup_of_odd hDO hOodd hS₀
  have hSY : CFSG.Open.fusionIsSylowIn 2 S Y := by
    refine ⟨le_sup_left, hS2, fun P hPY hP hSP => le_antisymm (fun p hp => ?_) hSP⟩
    have hp' : p ∈ ((S : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S O hSO]
      exact hPY hp
    obtain ⟨s, hs, o, ho, rfl⟩ := hp'
    have hoP : o ∈ P := by
      have e : o = s⁻¹ * (s * o) := by group
      rw [e]
      exact mul_mem (inv_mem (hSP hs)) hp
    have ho1 : o = 1 := by
      obtain ⟨j, hj⟩ := hP ⟨o, hoP⟩
      have hj' : o ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h1 : orderOf o ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
      have h2 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
      have hcop : Nat.Coprime (2 ^ j) (Nat.card O) :=
        Nat.Coprime.pow_left j ((Nat.prime_two.coprime_iff_not_dvd).mpr hOodd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    subst ho1
    simpa using hs
  obtain ⟨y, hy, hyS⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hY3 hAY hSY hS₀Y hAS hAS₀
  have hCYA : Y ⊓ Subgroup.centralizer (A : Set G) ≤ X := by
    have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr h'.isE27.1.1
    refine le_pPrimeCoreOf_centralizer (hbot G A a La h') ?_ inf_le_right
    refine Proof1413Res7.mem_scriptQ_of_point h142 h' (inf_le_left.trans (hYK.trans hKH))
      (fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))) ?_
    exact fun x hx => Proof1418Res3.mem_normalizer_inf (hAY hx) (Subgroup.le_normalizer (hAC hx))
  refine ⟨y, hCYA hy, ?_⟩
  rw [← hyS]
  exact hS₀.1.trans inf_le_right

end Proof1418Res3

open Proof1418Res3

theorem step1411WGammaLaR_of (h : Step1411WGammaR) : Step1411WGammaLaR :=
  fun G _ _ A c L hR hfail a ha _ _ S hS T hT _ _ => h G A c L hR hfail a ha S hS T hT

theorem step1411WGammaR_of_la (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h1413 : Item1413CR) (h142 : Item142AllS14) (hbot : Item145BotS14)
    (h : Step1411WGammaLaR) : Step1411WGammaR := by
  intro G _ _ A c L hR hfail a ha S hS T hT
  have hD := hR.toSec14Std.toSec13Data
  have haA : a ∈ A := (zpowers_mem_omegaA_iff.mp ha.1).1
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx haA)
  obtain ⟨La, hLa⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq ha.1
  have hLa' : La ∈ lA A a := Sec12.mem_lA_of_mem_lA422 hAa hLa
  obtain ⟨x, hx, hxS⟩ := exists_conj_le_of_gamma h422 h45 h1413 h142 hbot hR hfail ha hLa' hS
  obtain ⟨y, hy, hyT⟩ := exists_conj_le_of_gamma h422 h45 h1413 h142 hbot hR hfail ha hLa' hT
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({a} : Set G) :=
    le_inf ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _))
      ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)))
  have h1 : IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) S
      (S.map (MulAut.conj x).toMonoidHom) := ⟨x, hXW hx, rfl⟩
  have h2 : IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) T
      (T.map (MulAut.conj y).toMonoidHom) := ⟨y, hXW hy, rfl⟩
  have h3 := h G A c L hR hfail a ha La hLa' _
    (map_conj_mem_scriptQPiStar_centralizer haA hx hS) _
    (map_conj_mem_scriptQPiStar_centralizer haA hy hT) hxS hyT
  exact (h1.trans h3).trans h2.symm

end CFSG.RankThree.PartTwo.Sec14
