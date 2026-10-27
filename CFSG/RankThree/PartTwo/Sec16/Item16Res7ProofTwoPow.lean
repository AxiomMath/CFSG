module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofTwoPow
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofCUL
import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofL
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Res7TwoPow

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_le_of_normalized {L : Subgroup G} (hLs : IsSimpleGroup ↥L) {n : ℕ}
    (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n) {B P : Subgroup G}
    (hBL : B ≤ L) (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hPL : P ≤ L) (hP2 : IsPGroup 2 P) (hBP : B ≤ Subgroup.normalizer (P : Set G)) :
    P = ⊥ := by
  have hX := Proof1617.isoLThreePi_of_isSimpleGroup hLs hn hiso
  have hPcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hBel : CFSG.Open.IsElemAbelian 3 B := ⟨hB.1, hB.2⟩
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_three
    hBel (by rw [hB9]; norm_num) hBP hPcop
  rw [← hgen]
  refine iSup_eq_bot.mpr fun b => iSup_eq_bot.mpr fun hbB => iSup_eq_bot.mpr fun hb1 => ?_
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxb⟩
  rw [Subgroup.mem_bot]
  have hxb' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hxb
  obtain ⟨k, hk⟩ := hP2 ⟨x, hxP⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := ProofKSL3Two.eq_one_of_commute_two_pow hn hn3 hX (d := ⟨b, hBL hbB⟩)
    (x := ⟨x, hPL hxP⟩) (Subtype.ext (by simpa using hB.2 b hbB))
    (fun h => hb1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hxb')) (k := k)
    (Subtype.ext (by simpa using hxk))
  exact congrArg Subtype.val h1

theorem not_three_dvd_of_mod_nine {n : ℕ} (h : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) :
    ¬ 3 ∣ n := by
  rintro ⟨k, rfl⟩
  apply h
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show 3 * (m + m) = 6 * m by ring, pow_mul, Nat.pow_mod]
    norm_num
  · right
    rw [show 3 * (2 * m + 1) = 6 * m + 3 by ring, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem commutator_mem_pCoreOf {L Y R B : Subgroup G} (hLs : IsSimpleGroup ↥L) {n : ℕ}
    (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (hLY : L ≤ Y) (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y)
    (hBL : B ≤ L) (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hR2 : IsPGroup 2 R) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) {r b : G} (hr : r ∈ R) (hb : b ∈ B) :
    r * b * r⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  set N := CFSG.Open.pCoreOf 2 Y with hN
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hRN : R ≤ Subgroup.normalizer (N : Set G) :=
    hRY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hbY : b ∈ Y := hLY (hBL hb)
  have hgR : r * b * r⁻¹ * b⁻¹ ∈ R := by
    have : b * r⁻¹ * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hBR hb) r⁻¹).mp (inv_mem hr)
    rw [show r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) by group]
    exact mul_mem hr this
  have hgY : r * b * r⁻¹ * b⁻¹ ∈ Y := by
    have : r * b * r⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hRY hr) b).mp hbY
    exact mul_mem this (inv_mem hbY)
  have hgLN : r * b * r⁻¹ * b⁻¹ ∈ ((L ⊔ N : Subgroup G) : Set G) := by
    rw [← hY]
    exact hgY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L N (hLY.trans hYN)] at hgLN
  obtain ⟨l, hl, m, hm, hlm⟩ := hgLN
  have hlm' : l * m = r * b * r⁻¹ * b⁻¹ := hlm
  have hP2 : IsPGroup 2 ↥((R ⊓ Y) ⊔ N) :=
    IsPGroup.to_sup_of_normal_right' (hR2.to_le inf_le_left) hN2 (inf_le_left.trans hRN)
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := (hBL.trans hLY).trans Subgroup.le_normalizer
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := (hBL.trans hLY).trans hYN
  have hBL' : B ≤ Subgroup.normalizer (L : Set G) := hBL.trans Subgroup.le_normalizer
  have hBP : B ≤ Subgroup.normalizer ((((R ⊓ Y) ⊔ N) ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (Sec14.le_normalizer_sup (Late.le_normalizer_inf hBR hBY) hBN) hBL'
  have hP₀ : ((R ⊓ Y) ⊔ N) ⊓ L = ⊥ := eq_bot_of_le_of_normalized hLs hn hn3 hiso hBL hB hB9
    inf_le_right (hP2.to_le inf_le_left) hBP
  have hlP : l ∈ ((R ⊓ Y) ⊔ N) ⊓ L := by
    refine ⟨?_, hl⟩
    have : l = (r * b * r⁻¹ * b⁻¹) * m⁻¹ := by rw [← hlm']; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left ⟨hgR, hgY⟩) (Subgroup.mem_sup_right (inv_mem hm))
  rw [hP₀, Subgroup.mem_bot] at hlP
  rw [← hlm', hlP, one_mul]
  exact hm

omit [Finite G] in
theorem mul_conj_eq {Q : Type*} [Group Q] (σ : MulAut Q) (q : Q) :
    σ * MulAut.conj q = MulAut.conj (σ q) * σ := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

omit [Finite G] in
theorem actQuotPCore_eq_one_of_le_centralizer {L Y : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) {x : G}
    (hxN : x ∈ Subgroup.normalizer (Y : Set G))
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) : actQuotPCore Y ⟨x, hxN⟩ = 1 := by
  set N := CFSG.Open.pCoreOf 2 Y with hN
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hxNN : x ∈ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hxN
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨y, hy⟩ := y
    rw [MulAut.one_apply, Steps165.actQuotPCore_mk hxN y hy, QuotientGroup.eq,
      Step163Alt.mem_pCore_two_iff]
    have hyLN : y ∈ ((L ⊔ N : Subgroup G) : Set G) := by
      rw [← hY]
      exact hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L N (hLY.trans hYN)] at hyLN
    obtain ⟨l, hl, m, hm, hlm⟩ := hyLN
    have hlm' : l * m = y := hlm
    have hxl : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp (hxL hl)
    have hmem : x * m⁻¹ * x⁻¹ * m ∈ N :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hxNN m⁻¹).mp (inv_mem hm)) hm
    convert hmem using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hlm']
    calc (x * (l * m) * x⁻¹)⁻¹ * (l * m) = x * m⁻¹ * (x * l)⁻¹ * l * m := by group
      _ = x * m⁻¹ * (l * x)⁻¹ * l * m := by rw [hxl]
      _ = x * m⁻¹ * x⁻¹ * m := by group

theorem le_normalizer_commutator {K R A : Subgroup G}
    (hR : K ≤ Subgroup.normalizer (R : Set G)) (hA : K ≤ Subgroup.normalizer (A : Set G)) :
    K ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup G) : Set G) := fun x hx =>
  KS163TwoPowProof.mem_normalizer_of_map_le (le_of_eq (by
    rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hR hx),
      Late.map_conj_eq_of_mem_normalizer (hA hx)]))

theorem goodR163_inf_centralizer {A L Y R : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) (hLY : L ≤ Y) (hRQ : R ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hXR : xA A ≤ Subgroup.normalizer (R : Set G)) (hRA : ⁅R, A⁆ = ⊥)
    (hRY : CFSG.Open.pCoreOf 2 Y ⊓ R ≠ ⊥) :
    GoodR163 A L (R ⊓ Subgroup.centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hRQ
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRQ.1.1.1.2.2
  have hRC : R ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRA
  have hRX : R ≤ xA A :=
    (le_inf le_rfl hRC).trans (inf_centralizer_le_xA h.toSec14Std.maximal_isElemAbelian hR3)
  have hXL : xA A ≤ Subgroup.normalizer (L : Set G) :=
    xA_le_normalizer_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRX.trans hXL
  set N := CFSG.Open.pCoreOf 2 Y with hN
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hLN : L ⊓ N ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hLY.trans hYN))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right)
  have hPC : N ⊓ R ≤ R ⊓ Subgroup.centralizer (L : Set G) := by
    intro p hp
    refine ⟨hp.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 : p * l * p⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hRL hp.2) l).mp hl) (inv_mem hl)
    have h2 : p * l * p⁻¹ * l⁻¹ ∈ N := by
      have : l * p⁻¹ * l⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hYN (hLY hl)) p⁻¹).mp (inv_mem hp.1)
      rw [show p * l * p⁻¹ * l⁻¹ = p * (l * p⁻¹ * l⁻¹) by group]
      exact mul_mem hp.1 this
    have h3 : p * l * p⁻¹ * l⁻¹ = 1 := by
      have := hLN ⟨h1, h2⟩
      rw [hO, Subgroup.mem_bot] at this
      exact this
    calc l * p = (p * l * p⁻¹ * l⁻¹)⁻¹ * (p * l) := by group
      _ = p * l := by rw [h3, inv_one, one_mul]
  set R' := R ⊓ Subgroup.centralizer (L : Set G) with hR'
  have hR'1 : R' ≠ ⊥ := fun h0 => hRY (le_bot_iff.mp (h0 ▸ hPC))
  have hAR' : A ≤ Subgroup.normalizer (R' : Set G) :=
    Late.le_normalizer_inf hAR
      (h.toSec13Data.le_normalizer.trans (Proof169.normalizer_le_normalizer_centralizer L))
  have hXR' : xA A ≤ Subgroup.normalizer (R' : Set G) :=
    Late.le_normalizer_inf hXR (hXL.trans (Proof169.normalizer_le_normalizer_centralizer L))
  have hR'2 : IsPGroup 2 R' := hR2.to_le inf_le_left
  have hLR' : L ≤ Subgroup.centralizer (R' : Set G) := Subgroup.le_centralizer_iff.mp inf_le_right
  have hR'O : R' ≤ CFSG.Open.pCoreOf 2 (R' ⊔ L) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le Subgroup.le_normalizer (hLR'.trans (Subgroup.centralizer_le_normalizer _))) hR'2
  refine ⟨⟨⟨mem_scriptQ_of_le hRQ.1.1 inf_le_left hAR', le_top⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two R').mpr hR'2⟩, hXR', fun h0 => ?_⟩
  rw [h0] at hR'O
  exact hR'1 (le_bot_iff.mp hR'O)

theorem goodR163_commutator {A L Y R : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hLs : IsSimpleGroup ↥L) {n : ℕ} (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hLY : L ≤ Y) (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hRQ : R ∈ scriptQPi A (lB A) ⊤ (piOf 2))
    (hXR : xA A ≤ Subgroup.normalizer (R : Set G)) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hRA : ⁅R, A⁆ ≠ ⊥) : GoodR163 A L ⁅R, A⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hRQ
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRQ.1.1.1.2.2
  have hBel : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (h.toSec13Data.commute x.2.1 y.2.1)⟩⟩,
      fun x hx => h.toSec13Data.isElemAbelian.2 x hx.1⟩
  have hR'R : ⁅R, A⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hAR
  have hAA : A ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hAR' : A ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hAR hAA
  have hXR' : xA A ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hXR hXA
  set φ := actQuotPCore Y with hφ
  have hfix : ∀ (r : G) (hr : r ∈ R) (b : G) (hb : b ∈ A ⊓ L),
      φ ⟨r, hRY hr⟩ (((⟨b, hLY (Subgroup.mem_inf.mp hb).2⟩ : ↥Y)) : ↥Y ⧸ CFSG.pCore 2 ↥Y) =
        (((⟨b, hLY (Subgroup.mem_inf.mp hb).2⟩ : ↥Y)) : ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    intro r hr b hb
    rw [hφ, Steps165.actQuotPCore_mk (hRY hr) b (hLY (Subgroup.mem_inf.mp hb).2),
      QuotientGroup.eq, Step163Alt.mem_pCore_two_iff]
    have hbi : b⁻¹ ∈ A ⊓ L := inv_mem hb
    have hc := commutator_mem_pCoreOf hLs hn hn3 hiso hLY hY inf_le_right hBel h9 hR2 hRY
      (inf_le_left.trans hAR) hr hbi
    convert hc using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcomm : ∀ (r : G) (hr : r ∈ R) (x : G) (hx : x ∈ A),
      φ ⟨x, hYA hx⟩ * φ ⟨r, hRY hr⟩ = φ ⟨r, hRY hr⟩ * φ ⟨x, hYA hx⟩ := by
    intro r hr x hx
    set Z : Subgroup G := ((Subgroup.centralizer ({φ ⟨r, hRY hr⟩} : Set (MulAut _))).comap
      φ).map (Subgroup.normalizer (Y : Set G)).subtype with hZ
    have hcZ : c ∈ Z := by
      have hmem : (⟨c, hYA h.mem_A⟩ : ↥(Subgroup.normalizer (Y : Set G))) ∈
          (Subgroup.centralizer ({φ ⟨r, hRY hr⟩} : Set (MulAut _))).comap φ := by
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hφ,
          actQuotPCore_eq_one_of_le_centralizer hLY hY (hYA h.mem_A) h.le_centralizer,
          one_mul, mul_one]
      exact Subgroup.mem_map_of_mem _ hmem
    have hBZ : A ⊓ L ≤ Z := by
      intro b hb
      have hbA := (Subgroup.mem_inf.mp hb).1
      have hbL := (Subgroup.mem_inf.mp hb).2
      have hmem : (⟨b, hYA hbA⟩ : ↥(Subgroup.normalizer (Y : Set G))) ∈
          (Subgroup.centralizer ({φ ⟨r, hRY hr⟩} : Set (MulAut _))).comap φ := by
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hφ,
          Steps165.actQuotPCore_of_mem (hLY hbL) (hYA hbA), ← hφ, mul_conj_eq, hfix r hr b hb]
      exact Subgroup.mem_map_of_mem _ hmem
    have hAZ : A ≤ Z := by
      rw [hAeq]
      exact sup_le (Subgroup.zpowers_le.mpr hcZ) hBZ
    obtain ⟨x', hx', hxx'⟩ := hAZ hx
    have hx'eq : x' = ⟨x, hYA hx⟩ := Subtype.ext hxx'
    have hx'' : x' ∈ (Subgroup.centralizer ({φ ⟨r, hRY hr⟩} : Set (MulAut _))).comap φ := hx'
    rw [hx'eq, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hx''
    exact hx''
  have hker : ⁅R, A⁆ ≤ φ.ker.map (Subgroup.normalizer (Y : Set G)).subtype := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    have hmem : ⁅(⟨r, hRY hr⟩ : ↥(Subgroup.normalizer (Y : Set G))), ⟨x, hYA hx⟩⁆ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hcomm r hr x hx).symm
    exact Subgroup.mem_map_of_mem _ hmem
  have htriv : ∀ g ∈ ⁅R, A⁆, ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro g hg y hy
    obtain ⟨⟨g', hg'N⟩, hg1, rfl⟩ := hker hg
    exact (mem_sectionCentralizer_of_actQuotPCore_eq_one hg'N hg1).2 y hy
  have hR'O := KS163TwoPowProof.le_pCoreOf_sup_of_commutator (hR2.to_le hR'R)
    (hR'R.trans hRY) htriv
  refine ⟨⟨⟨mem_scriptQ_of_le hRQ.1.1 hR'R hAR', le_top⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hR2.to_le hR'R)⟩, hXR',
    pCoreOf_sup_ne_bot_of_le hLY hRA hR'O⟩

theorem facts_of_prod {A L : Subgroup G} {c : G} (h : Sec15R G A c L) {n : ℕ} (hn : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.toSec13Data.mem_thetaComponentsAt).1
  obtain ⟨-, h2⟩ := Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hn hiso
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨π, K, _, hKf, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hn hiso
    have hq2 : 2 < 2 ^ n := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
      omega
    exact Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hKf hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h.toSec13Data hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Sec13.card_inf_eq_nine h.toSec13Data (Sec13.isPerfect_lBar h.toSec13Data) hprod.some
  exact ⟨h9, Proof1617.eq_zpowers_sup_inf h.mem_A (le_sup_of_card_inf h hcL h9)
    h.le_centralizer⟩

end Res7TwoPow

theorem step163TwoPowNE_of_res7 (h142 : Concl142R) (h143 : Concl143S14) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h1514 : Item1514R) (hMeets : Step163Meets)
    (h1424 : Item14_24R) (hS : Step163TwoPowShape) (h138 : Item138N) : Step163TwoPowNE := by
  intro G _ _ A c L h hL hO h32 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hY⟩ := hne
  have hLY := hL Y hY
  obtain ⟨hcov, hΩ, hprod⟩ := cover_of_isL3TwoPow h (h1514 G A c L h) hMeets h32 hY hLY
  have hYA : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  obtain ⟨hsimp, n₀, hn₀, hiso₀⟩ := hS G A c L h hO h32 Y hY hYA hLY hcov hΩ hprod
  have hY3 : Y ∈ scriptY3 A (lB A) := ⟨hY.prop.2, hY.prop.1.2.2.1⟩
  obtain ⟨a, haA, hac, hRY0⟩ := h1424 G A c L h Y hY3 hYA n₀ hn₀ hiso₀ hcov
    (h153 G A c L h Y hY).2.2 hsimp hΩ
  have ha1 : a ≠ 1 := fun h1 => hac (by rw [h1]; exact one_mem _)
  have hRQ := pCoreOf_delta_mem_scriptQPi (h142 G A c L h) (h143 G A c L h.toSec14Std) haA ha1
  have hXR := xA_le_normalizer_pCoreOf_delta (A := A) haA
  by_cases hRA : ⁅CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))), A⁆ = ⊥
  · exact ⟨_, Res7TwoPow.goodR163_inf_centralizer h hO hLY hRQ hXR hRA hRY0⟩
  ·
    obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer (h153 G A c L h) (hobs G A c L h) hY
    obtain ⟨w, hw, hRw⟩ := exists_conj_le_normalizer (h1411 G A c L h) hS₀ hS₀Y hRQ
    have hY' := map_conj_mem_scriptY0Star hw hY
    have hLY' := hL _ hY'
    obtain ⟨hcov', -, -⟩ := cover_of_isL3TwoPow h (h1514 G A c L h) hMeets h32 hY' hLY'
    rw [inf_of_le_right hLY'] at hcov'
    have hY'A : A ≤ Subgroup.normalizer
        ((Y.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := hY'.prop.1.1.2
    obtain ⟨n, hn, hiso⟩ := h32
    have hn3 : ¬ 3 ∣ n := Res7TwoPow.not_three_dvd_of_mod_nine
      (not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hn hiso hprod)
    obtain ⟨h9, hAeq⟩ := Res7TwoPow.facts_of_prod h hn hiso hprod
    exact ⟨_, Res7TwoPow.goodR163_commutator h hsimp hn hn3 hiso hAeq h9 hLY' hcov' hY'A hRQ
      hXR hRw hRA⟩

end CFSG.RankThree.PartTwo.Sec16
