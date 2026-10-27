module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof159
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item154PiProofPoint
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTen
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPClassification
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import Certificates.Certificate2201
import Certificates.Certificate2202

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

private theorem mul_conj_inv_mem_centralizer {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h27 : Nat.card A = 27) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) {k : ℕ} (hwk : w ^ 3 ^ k = 1)
    (hcen : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9) {a : G}
    (ha : a ∈ A) : a * (w * a⁻¹ * w⁻¹) ∈ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨φ, hφ, hφk⟩ : ∃ φ : MulAut A, (∀ x : A, ((φ x : A) : G) = w * (x : G) * w⁻¹) ∧
      φ ^ 3 ^ k = 1 := by
    refine ⟨A.normalizerMonoidHom ⟨w, hwA⟩, fun x => Sec4.normalizerMonoidHom_apply_coe hwA x, ?_⟩
    rw [← map_pow]
    have h1 : (⟨w, hwA⟩ : Subgroup.normalizer (A : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hwk)
    rw [h1, map_one]
  obtain ⟨T, hT⟩ : ∃ T : A →* A, ∀ x : A, T x = x⁻¹ * φ x := by
    refine ⟨{ toFun := fun x => x⁻¹ * φ x
              map_one' := by simp
              map_mul' := fun x y => ?_ }, fun x => rfl⟩
    apply Subtype.ext
    have hc := hcomm _ (mul_mem (inv_mem x.2) (φ x).2) _ (inv_mem y.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, mul_inv_rev]
    calc (y : G)⁻¹ * (x : G)⁻¹ * (((φ x : A) : G) * ((φ y : A) : G))
        = ((y : G)⁻¹ * ((x : G)⁻¹ * ((φ x : A) : G))) * ((φ y : A) : G) := by group
      _ = (((x : G)⁻¹ * ((φ x : A) : G)) * (y : G)⁻¹) * ((φ y : A) : G) := by rw [← hc]
      _ = (x : G)⁻¹ * ((φ x : A) : G) * ((y : G)⁻¹ * ((φ y : A) : G)) := by group
  have hker_map : T.ker.map A.subtype = A ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : T x = 1 := MonoidHom.mem_ker.mp hx
      have hG1 : (x : G)⁻¹ * ((φ x : A) : G) = 1 := by
        have := congrArg Subtype.val ((hT x).symm.trans hx1)
        simpa using this
      have hwx : w * (x : G) * w⁻¹ = (x : G) := by
        rw [← hφ x]
        exact (inv_mul_eq_one.mp hG1).symm
      have hxw : (x : G) * w = w * (x : G) := (mul_inv_eq_iff_eq_mul.mp hwx).symm
      exact Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxw⟩
    · intro hy
      obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyw : (y : G) * w = w * (y : G) := Subgroup.mem_centralizer_singleton_iff.mp hyC
      refine Subgroup.mem_map.mpr ⟨⟨y, hyA⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hT]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hφ]
      rw [← hyw]
      group
  have hker_card : Nat.card T.ker = 9 := by
    rw [← Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective, hker_map]
    exact hcen
  have hI_card : Nat.card T.range = 3 := by
    have h1 := Subgroup.card_mul_index T.ker
    rw [Subgroup.index_ker, hker_card, h27] at h1
    omega
  have hstable : ∀ y ∈ T.range, φ y ∈ T.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    refine MonoidHom.mem_range.mpr ⟨φ x, ?_⟩
    rw [hT, hT, map_mul, map_inv]
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank in
  have hfix := map_eq_self_of_pow_eq_one_of_card_three hI_card φ hφk hstable
  have hz : w * a⁻¹ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwA a⁻¹).mp (inv_mem ha)
  have hTa : (T ⟨a, ha⟩)⁻¹ ∈ T.range := inv_mem (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
  have hfa' := congrArg Subtype.val (hfix _ hTa)
  rw [hφ] at hfa'
  have hTG : (((T ⟨a, ha⟩)⁻¹ : A) : G) = (a⁻¹ * (w * a * w⁻¹))⁻¹ := by
    rw [hT]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ, Subgroup.coe_mk]
  rw [hTG] at hfa'
  have hwe := mul_inv_eq_iff_eq_mul.mp hfa'
  have hae : a * (w * a⁻¹ * w⁻¹) = (a⁻¹ * (w * a * w⁻¹))⁻¹ := by
    rw [hcomm a ha _ hz]
    group
  rw [Subgroup.mem_centralizer_singleton_iff, hae]
  exact hwe.symm

theorem isoLThreePi_two_of_ctx159 {A L₀ L : Subgroup G} {c₀ : G} (ctx : Ctx159 G A c₀ L₀)
    (e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀) {k : ℕ}
    (hk : 1 ≤ k) (hε : IsLThreeEpsAt (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 k) :
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 k := by
  have hperf₀ : Group.IsPerfect (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀) :=
    (CFSG.RankThree.PartTwo.Sec12.isQuasisimple_thetaQuot_of_mem
      ctx.toSec15R.toSec14Std.toSec13Data.mem_thetaComponentsAt).1
  have hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases ctx.types with hL3 | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · obtain ⟨p, f, hp, hf, hπ⟩ := hL3
    exact Proof154Pi.isoLThreePi_two_of_isoLThreePi hperf hk hf hε
      (Proof1511.isoLThreePi_of_mulEquiv e.symm hπ)
  · have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 :=
      (Nat.card_congr (e.trans ψ).toEquiv).trans
        KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    exact (Item148Rank.not_isLThreeEpsAt_of_card_2520 hcard 2 k hε).elim
  · have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 :=
      (Nat.card_congr (e.trans ψ).toEquiv).trans KFacts.KS14.card_nativeM22
    exact (KFacts.KS14.not_isLThreeEpsAt_of_card hcard
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22)
      2 k hε).elim

section Certs


theorem ctx159_point {A L₀ L : Subgroup G} {c₀ c : G} (ctx : Ctx159 G A c₀ L₀)
    (hΩ : Subgroup.zpowers c ∈ omegaA A) (hL : L ∈ lA A c) :
    Sec15R G A c L ∧ A ⊓ L = A ⊓ L₀ ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      (∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c) ∧
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀) := by
  have hD0 : Sec13Data G A c₀ L₀ := ctx.toSec15R.toSec14Std.toSec13Data
  obtain ⟨w, hw, hcw⟩ : ∃ w ∈ Subgroup.normalizer (A : Set G),
      Subgroup.zpowers c = (Subgroup.zpowers c₀).map (MulAut.conj w).toMonoidHom := by
    have h := hΩ
    rw [ctx.omegaA_eq] at h
    exact h
  have hR : Sec15R G A c L := Proof1511.sec15R_point ctx.toSec15R hΩ hL
  obtain ⟨f, hfA, hfL, hfc⟩ :=
    Proof1511.exists_mem_inf_not_mem_of_card_nine hD0.card_zpowers ctx.card_inf
  have hLeq : L = L₀.map (MulAut.conj w).toMonoidHom :=
    Proof1511.eq_map_conj_of_mem_lA hD0 hfA hfL hfc hw hcw hL
  have hAL : A ⊓ L = A ⊓ L₀ := by
    rw [hLeq]
    have hmapB : (A ⊓ L₀).map (MulAut.conj w).toMonoidHom = A ⊓ L₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (ctx.normalizer_le_inf hw)
    have h1 := Subgroup.map_inf_eq A L₀ (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
    rw [Proof1511.map_conj_eq_self hw, hmapB] at h1
    exact h1.symm
  have hcL : c ∉ L := hR.hypS.2.2 c hΩ L hL
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    rw [hAL]
    exact ctx.card_inf
  have hsup : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Sec13.eq_sup_of_card_nine hR.toSec14Std.toSec13Data h9 (fun h => hcL h.2)
  have hsec : ∀ a ∈ A, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a haA haC
    have h1 := hR.toSec14Std.toSec13Data.sectionCentralizer_eq
    rw [Sec13.sectionCentralizer_eq_inf hR.toSec14Std.toSec13Data.le_normalizer] at h1
    have h2 : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := ⟨haA, haC⟩
    rw [h1] at h2
    exact h2
  have hiso : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      ↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀) := by
    subst hLeq
    let e : ↥L₀ ≃* ↥(L₀.map (MulAut.conj w).toMonoidHom) :=
      L₀.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
    exact ⟨(QuotientGroup.congr _ _ e
      (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)).symm⟩
  exact ⟨hR, hAL, hsup, hsec, hiso⟩

theorem commutator_mem_inf {A L₀ : Subgroup G} {c₀ c w : G} (ctx : Ctx159 G A c₀ L₀)
    (hw : IsW159 A L₀ w) (hΩ : Subgroup.zpowers c ∈ omegaA A) :
    c * w * c⁻¹ * w⁻¹ ∈ A ⊓ L₀ ∧ c * w * c⁻¹ * w⁻¹ ≠ 1 := by
  have hD0 : Sec13Data G A c₀ L₀ := ctx.toSec15R.toSec14Std.toSec13Data
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD0.commute hx hy
  have h27 : Nat.card A = 27 := hD0.card_eq
  have h9 : Nat.card (A ⊓ L₀ : Subgroup G) = 9 := ctx.card_inf
  obtain ⟨k, hk⟩ := hw.2.1
  have hcA : c ∈ A := hΩ.1 (Subgroup.mem_zpowers c)
  obtain ⟨x, hx, hcx⟩ : ∃ x ∈ Subgroup.normalizer (A : Set G),
      Subgroup.zpowers c = (Subgroup.zpowers c₀).map (MulAut.conj x).toMonoidHom := by
    have h := hΩ
    rw [ctx.omegaA_eq] at h
    exact h
  have hc₀L : c₀ ∉ L₀ := ctx.hypS.2.2 c₀ ctx.zpowers_mem_omegaA L₀ ctx.mem_lA
  have hsup₀ : A = Subgroup.zpowers c₀ ⊔ (A ⊓ L₀) :=
    Sec13.eq_sup_of_card_nine hD0 h9 (fun h => hc₀L h.2)
  have hmapB : (A ⊓ L₀).map (MulAut.conj x).toMonoidHom = A ⊓ L₀ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (ctx.normalizer_le_inf hx)
  have hsup : A = Subgroup.zpowers c ⊔ (A ⊓ L₀) := by
    have h := congrArg (fun H : Subgroup G => H.map (MulAut.conj x).toMonoidHom) hsup₀
    rw [Subgroup.map_sup, Proof1511.map_conj_eq_self hx, hmapB, ← hcx] at h
    exact h
  have hinf : A ⊓ Subgroup.centralizer ({w} : Set G) = A ⊓ L₀ :=
    IsW159.inf_centralizer_eq hw h27 h9
  have hcen : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 := by
    rw [hinf]
    exact h9
  have hdcen : c * (w * c⁻¹ * w⁻¹) ∈ Subgroup.centralizer ({w} : Set G) :=
    mul_conj_inv_mem_centralizer hcomm h27 hw.1 hk hcen hcA
  have hdA : c * (w * c⁻¹ * w⁻¹) ∈ A :=
    mul_mem hcA ((Subgroup.mem_normalizer_iff.mp hw.1 c⁻¹).mp (inv_mem hcA))
  have hd_eq : c * w * c⁻¹ * w⁻¹ = c * (w * c⁻¹ * w⁻¹) := by group
  refine ⟨?_, fun hd1 => ?_⟩
  · rw [hd_eq, ← hinf]
    exact ⟨hdA, hdcen⟩
  have hcw : c * w = w * c := by
    have h1 : c * w * c⁻¹ = w := mul_inv_eq_one.mp hd1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hzc : Subgroup.zpowers c ≤ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcw)
  have hBc : A ⊓ L₀ ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [← hinf]
    exact inf_le_right
  have hle : A ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [hsup]
    exact sup_le hzc hBc
  apply hw.2.2.2
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
