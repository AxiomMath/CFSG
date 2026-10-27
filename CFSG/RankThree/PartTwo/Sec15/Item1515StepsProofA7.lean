module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA10
public import Certificates.Certificate2195
public import Certificates.Certificate2202
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3157
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1515

variable {G : Type} [Group G] [Finite G]

theorem not_isLThreeEpsAt_of_card_2520 {X : Type} [Group X] (hX : Nat.card X = 2520) (p f : ℕ)
    [Fact p.Prime] : ¬ IsLThreeEpsAt X p f :=
  KFacts.KS14.not_isLThreeEpsAt_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSL_a7)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) Proof1514.checkSU_a7) p f

omit [Finite G] in
theorem conj_eq_of_mem_normalizer_zpowers_of_pow {c w : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hw : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) {k : ℕ} (hwk : w ^ 3 ^ k = 1) :
    w * c * w⁻¹ = c := by
  have hmem : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
  rcases Sec13.eq_of_mem_zpowers_of_pow_three hc3 hmem with h1 | h1 | h1
  · exfalso
    apply hc1
    have : c = w⁻¹ * (w * c * w⁻¹) * w := by group
    rw [this, h1]
    group
  · exact h1
  · exfalso
    have hpow : ∀ n : ℕ, w ^ n * c * (w ^ n)⁻¹ = c ^ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc w ^ (n + 1) * c * (w ^ (n + 1))⁻¹ = w * (w ^ n * c * (w ^ n)⁻¹) * w⁻¹ := by group
          _ = w * c ^ 2 ^ n * w⁻¹ := by rw [ih]
          _ = (w * c * w⁻¹) ^ 2 ^ n := by rw [conj_pow]
          _ = c ^ 2 ^ (n + 1) := by rw [h1, ← pow_mul, pow_succ, mul_comm]
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have hmod : ∀ j : ℕ, 2 ^ (2 * j + 1) % 3 = 2 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add]
        omega
    have h3 := hpow (3 ^ k)
    rw [hwk, one_mul, inv_one, mul_one] at h3
    have hc' : c ^ 2 ^ 3 ^ k = c ^ 2 := by
      rw [← pow_mod_orderOf, orderOf_eq_prime hc3 hc1, hj, hmod j]
    apply hc1
    have h4 : c = c ^ 2 := h3.trans hc'
    calc c = c ^ 2 * c⁻¹ := by group
      _ = c * c⁻¹ := by rw [← h4]
      _ = 1 := mul_inv_cancel c

theorem facts_of_a7_or_m22
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  have hD := h.toSec13Data
  have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 ∨
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 := by
    rcases hL with hφ | hφ <;> obtain ⟨φ⟩ := hφ
    · exact Or.inl (by rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_seven])
    · exact Or.inr (by rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22])
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨hcL, h9, hprod, -⟩ |
      ⟨-, -, hMJ, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · exact ⟨hcL, h9, hprod⟩
  · exfalso
    rcases hMJ with hψ | hψ <;> obtain ⟨ψ⟩ := hψ
    · obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
      rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeM12] at hcard
      omega
    · obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
      rw [Nat.card_congr χ.toEquiv, KFacts.KS14.card_nativeJ2] at hcard
      omega
  · exfalso
    obtain ⟨⟨p, e, hp, -, hiso⟩, -, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    rcases hL with hφ | hφ <;> obtain ⟨φ⟩ := hφ
    · exact Proof1514.not_isoLThreePi_of_card_2520 (by rw [Nat.card_congr φ.toEquiv,
        card_alternatingGroup_seven]) p e hiso
    · exact KFacts.KS14.not_isoLThreePi_M22 p e (isoLThreePi_congr φ hiso)
  · exact (h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA hcL').elim

theorem false_of_wStarS4
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hW : WStarS4 A) : False := by
  have hD := h.toSec13Data
  obtain ⟨hcL, h9, -⟩ := facts_of_a7_or_m22 h131 h hL
  obtain ⟨σ, hσ1, hσ3⟩ : ∃ σ : wStar A, σ ≠ 1 ∧ σ ^ 3 = 1 := by
    rcases hW with he | he <;> obtain ⟨e⟩ := he
    · refine ⟨e.symm (Equiv.swap 0 1 * Equiv.swap 1 2), fun h1 => ?_, ?_⟩
      · rw [MulEquiv.symm_apply_eq, map_one] at h1
        revert h1
        decide
      · rw [← map_pow, MulEquiv.symm_apply_eq, map_one]
        decide
    · refine ⟨e.symm (1, Equiv.swap 0 1 * Equiv.swap 1 2), fun h1 => ?_, ?_⟩
      · rw [MulEquiv.symm_apply_eq, map_one] at h1
        have := congrArg Prod.snd h1
        revert this
        decide
      · rw [← map_pow, MulEquiv.symm_apply_eq, map_one, Prod.pow_mk, one_pow]
        congr 1
        decide
  obtain ⟨w₀, hw₀N, -, hw₀σ⟩ := Sec4.mem_autIn_iff.mp σ.2
  set n := orderOf w₀ with hn
  have hn0 : n ≠ 0 := (orderOf_pos w₀).ne'
  obtain ⟨k, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  set w := w₀ ^ m with hwdef
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hw₀N m
  have hwk : w ^ 3 ^ k = 1 := by
    rw [hwdef, ← pow_mul, mul_comm, ← hnm, hn, pow_orderOf_eq_one]
  have hwσ : A.normalizerMonoidHom ⟨w, hwN⟩ = (σ : MulAut A) ^ m := by
    rw [← hw₀σ, ← map_pow]
    rfl
  have hσm : (σ : MulAut A) ^ m ≠ 1 := by
    intro h1
    have h1' : σ ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])
    have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    have hdvd : orderOf σ ∣ Nat.gcd 3 m := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσ3)
      (orderOf_dvd_of_pow_eq_one h1')
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hσ1 hdvd
  have hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    normalizer_le_of_omegaA_eq hΩ hwN
  have h3L : 3 ∣ Nat.card L := by
    rcases hL with hφ | hφ <;> obtain ⟨φ⟩ := hφ
    · exact three_dvd_card_of_mulEquiv φ (by rw [card_alternatingGroup_seven]; norm_num)
    · exact three_dvd_card_of_mulEquiv φ (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h h3L hwH
  obtain ⟨-, hZ, hinn, hpow3, hcomm3⟩ :=
    KFacts.KS14.ks18A7M22 (↥L ⧸ aschbacherSolvableCore 3 ↥L) hL
  set τ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwL⟩) with hτ
  have hτk : τ ^ 3 ^ k = 1 := by
    have h1 : (⟨w, hwL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hwk)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨x, hx⟩ := hinn τ ⟨k, hτk⟩
  have hxk : x ^ 3 ^ k = 1 := by
    apply KFacts.KS14.conj_injective_of_center_eq_bot hZ
    rw [map_pow, ← hx, hτk, map_one]
  have hx3 : x ^ 3 = 1 := hpow3 x ⟨k, hxk⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set E := ((A ⊓ L).subgroupOf L).map π with hE
  have hτE : ∀ y ∈ (A ⊓ L).subgroupOf L, τ (π y) = π ⟨w * y * w⁻¹,
      (Subgroup.mem_normalizer_iff.mp hwL y).mp y.2⟩ := fun y _ => rfl
  have hxE : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set _) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 : x * π y * x⁻¹ = τ (π y) := by rw [hx, MulAut.conj_apply]
    rw [h1, hτE y hy]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hy).1
    exact ⟨(Subgroup.mem_normalizer_iff.mp hwN _).mp hyA,
      (Subgroup.mem_normalizer_iff.mp hwL _).mp y.2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3g : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hE3 : IsPGroup 3 E := by
    refine IsPGroup.map ?_ π
    intro y
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hyA : ((y : ↥L) : G) ∈ A := (Subgroup.mem_subgroupOf.mp y.2).1
    simpa using hD.isElemAbelian.2 _ hyA
  have hQ := IsPGroup.to_sup_of_normal_right' hx3g hE3 hxE
  have hcomm := hcomm3 _ hQ
  have hfix : ∀ y ∈ (A ⊓ L).subgroupOf L, τ (π y) = π y := by
    intro y hy
    have hyE : π y ∈ Subgroup.zpowers x ⊔ E :=
      Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    have hxQ : x ∈ Subgroup.zpowers x ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hc := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x, hxQ⟩ : ↥(Subgroup.zpowers x ⊔ E)) ⟨π y, hyE⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hx, MulAut.conj_apply, hc, mul_inv_cancel_right]
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hcentAL : A ⊓ L ≤ Subgroup.centralizer ({w} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyL : (⟨y, hy.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
    have h1 := hfix _ hyL
    rw [hτE _ hyL, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    set u : ↥L := (⟨w * y * w⁻¹, (Subgroup.mem_normalizer_iff.mp hwL y).mp hy.2⟩ : ↥L)⁻¹ *
      ⟨y, hy.2⟩ with hu
    have huθ : u ∈ aschbacherSolvableCore 3 ↥L := h1
    have huA : (u : G) ∈ A := by
      rw [hu]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact A.mul_mem (A.inv_mem ((Subgroup.mem_normalizer_iff.mp hwN y).mp hy.1)) hy.1
    have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 _ huA)
    have hu1 : u = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hu3) with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · have hθdvd := Subgroup.orderOf_dvd_natCard _ huθ
        rw [h2] at hθdvd
        exact absurd hθdvd hθ3
    have h2 := congrArg Subtype.val hu1
    rw [hu] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    have h3 : w * y * w⁻¹ = y := inv_mul_eq_one.mp h2
    calc y * w = (w * y * w⁻¹) * w := by rw [h3]
      _ = w * y := by group
  have hwc : w * c * w⁻¹ = c :=
    conj_eq_of_mem_normalizer_zpowers_of_pow (hD.isElemAbelian.2 c hD.mem_A) hD.ne_one hwH hwk
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    calc c * w = (w * c * w⁻¹) * w := by rw [hwc]
      _ = w * c := by group
  have hAa := eq_sup_of_card_nine hD h9 (fun h1 => hcL h1.2)
  have hAC : A ≤ Subgroup.centralizer ({w} : Set G) := hAa ▸ sup_le hcC hcentAL
  apply hσm
  rw [← hwσ]
  ext a
  rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
  have := Subgroup.mem_centralizer_singleton_iff.mp (hAC a.2)
  calc w * (a : G) * w⁻¹ = (a : G) * w * w⁻¹ := by rw [this]
    _ = a := mul_inv_cancel_right _ _

end Proof1515

open Proof1515


theorem step1515A7Trans_of (h148 : Item148R) (hbot : Item145BotS14) : Step1515A7Trans := by
  intro G _ _ A c L h hL7 hWS hT Y hY hm
  obtain ⟨φL⟩ := hL7
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [card_alternatingGroup_seven]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) := by
    intro c' L' hc' hL'
    obtain ⟨e⟩ := nonempty_thetaQuot_equiv_of_transOmega h.toSec14Std h3L hT.2 hc' hL'
    exact ⟨e.trans φL⟩
  have hcard : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 2520 := by
    intro c' L' hc' hL'
    obtain ⟨e⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven]
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ | ⟨h10, -, -⟩ |
      ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨φ7⟩ := hpt c' L' hc' hL'
    rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inl (nonempty_quot_pCore_two_equiv_of_multFree hY4 ⟨φ.trans φ7⟩
        multFree_alternatingGroup_seven)
    · exact Or.inl (nonempty_quot_pCore_two_equiv_of_multFree hY4 h7
        multFree_alternatingGroup_seven)
    · exact (Proof1514.not_isoLThreePi_of_card_2520 (hcard c' L' hc' hL') p (f * e) hiso).elim
    · obtain ⟨φJ⟩ := hJ
      have h1 := hcard c' L' hc' hL'
      rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
      omega
  · have h1 := hcard c' L' hc' hL'
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
    omega
  · exact Or.inr (nonempty_quot_pCore_two_equiv_of_multFree hY4 h10
      multFree_alternatingGroup_ten)
  · exact (not_isLThreeEpsAt_of_card_2520 (hcard c' L' hc' hL') 2 (n * m) hε).elim

theorem step1515A7Omega_of
    (h148 : Item148R) (hbot : Item145BotS14) (h131 : Item131)
    (h135 : Item135) :
    Step1515A7Omega := by
  intro G _ _ A c L h hL7 hΩ Y hY hm
  obtain ⟨φL⟩ := hL7
  obtain ⟨X, hX4, hXLY⟩ := hm
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_mulEquiv φL (by rw [card_alternatingGroup_seven]; norm_num)
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have hL2520 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
    rw [Nat.card_congr φL.toEquiv, card_alternatingGroup_seven]
  have key : ∀ Z ∈ scriptY4 A (lB A),
      Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* alternatingGroup (Fin 7)) := by
    intro Z hZ4
    have hZΔ := eq_deltaZero_of_mem_scriptY4 hbot h hZ4
    rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hZ4 hZΔ with
      ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', ⟨φJ⟩, -⟩ | ⟨-, -, hWS⟩ |
        ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
    · obtain rfl := hpt c' L' hc' hL'
      rcases hcases with hφ | ⟨-, h7⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨hJ, -⟩
      · obtain ⟨φ⟩ := hφ
        exact ⟨φ.trans φL⟩
      · exact h7
      · exact (Proof1514.not_isoLThreePi_of_card_2520 hL2520 p (f * e) hiso).elim
      · obtain ⟨φJ⟩ := hJ
        rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
        omega
    · obtain rfl := hpt c' L' hc' hL'
      rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hL2520
      omega
    · exact (false_of_wStarS4 h131 h (Or.inl ⟨φL⟩) hΩ hWS).elim
    · obtain rfl := hpt c' L' hc' hL'
      exact (not_isLThreeEpsAt_of_card_2520 hL2520 2 (n * m) hε).elim
  have hXY : X ≤ Y := hXLY.trans inf_le_right
  have hXL : X ≤ L := hXLY.trans inf_le_left
  obtain ⟨φX⟩ := key X hX4
  have hX2520 : Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = 2520 := by
    rw [Nat.card_congr φX.toEquiv, card_alternatingGroup_seven]
  obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY.prop.1 (key Y hY.prop.1)
    multFree_alternatingGroup_seven
  have hYX : Y = X ⊔ CFSG.Open.pCoreOf 2 Y := eq_sup_pCoreOf_two_of_card hXY (by
    rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven, hX2520])
  have hLX : L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype :=
    eq_sup_theta_of_card hXL (by rw [hL2520, hX2520])
  have : Nontrivial (alternatingGroup (Fin 7)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_alternatingGroup_seven]
    norm_num
  have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    theta_eq_pCore_two_of_multFree (h135 G A c L h.toSec13Data h.hypS_or_hypT) ⟨φL⟩
      multFree_alternatingGroup_seven
  have hθO : (aschbacherSolvableCore 3 ↥L).map L.subtype = CFSG.Open.pCoreOf 2 L := by
    rw [hθ]
    rfl
  constructor
  · refine le_antisymm ?_ (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
    calc Y = X ⊔ CFSG.Open.pCoreOf 2 Y := hYX
      _ ≤ (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y := sup_le_sup_right (le_inf hXY hXL) _
  · refine le_antisymm ?_ (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
    calc L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype := hLX
      _ = X ⊔ CFSG.Open.pCoreOf 2 L := by rw [hθO]
      _ ≤ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := sup_le_sup_right (le_inf hXL hXY) _

end CFSG.RankThree.PartTwo.Sec15
