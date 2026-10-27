module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6Proof1419
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofOneR
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofL3
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12Q
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofSimple
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
import CFSG.Sporadic.Mathieu.M12
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.RankThree.Asc83Table.PermTables
public import Certificates.Certificate18952
public import Certificates.Certificate8165
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.GH74.M12.Hyp (G12)

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

open Proof1413Res3 in
theorem ne_bot_of_mem_scriptQPiStarC (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c : G}
    (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (h3 : 3 ∣ Nat.card L) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L)) {R : Subgroup G}
    (hR' : R ∈ scriptQPiStar A (lB A) L (piOf 2)) : R ≠ ⊥ := by
  intro h0
  have hD := (Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL).toSec13Data
  have hall : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2), S = ⊥ := by
    intro S hS
    have hSinv : S ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3) := ⟨hS.prop.1.2, hS.prop.1.1.1.2.1, hS.prop.1.1.1.2.2⟩
    have hSc := le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq hSinv
    have hS2 := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hSL := le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ hL h3 hAa hSc
      hS.prop.1.1.1.2.2 hS2
    have hmem := Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hSL
      hS.prop.1.1.1.2.2 hS2
    have h1 := hR'.2 hmem (by rw [h0]; exact bot_le)
    rw [h0] at h1
    exact le_bot_iff.mp h1
  apply hcΓ.2
  intro S hS T hT
  rw [hall S hS, hall T hT]
  exact isConjIn_refl _ _

open Proof1413Res3 in
theorem exists_m12_equivC
    (h1413 : Item1413CR)
    (h135 : Item135) (h131 : Item131) {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G}
    (hR : Sec15R G A c₀ L₀) (hfail : Fail1411 A (lB A)) {c : G}
    (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A)) {L : Subgroup G} (hL : L ∈ lA A c)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :
    ∃ χ : ↥L ≃* G12, (A.subgroupOf L).map χ.toMonoidHom = Toolkit.M12.basisA.sub := by
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  obtain ⟨-, h9, hAa, hS3⟩ := m12_point_facts h131 hD φ
  have hθ := theta_eq_bot_of_gammaC h1413 h135 hR hfail hcΓ hL (Or.inl ⟨φ⟩)
  have ψ : ↥L ≃* G12 := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φ)
  exact Proof1413Res2.exists_equiv_basisA hD.le_centralizer hD.isElemAbelian hD.mem_A hAa h9
    hS3 ψ

end Proof1413Res6

open Proof1413Res3 Proof1413Res6 in
theorem step1419OneL3R_of_c
    (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (hK : KS1419LThreePi) : Step1419OneL3R := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL hL3 hnPGL R hR'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have hcA : c ∈ A := hD.mem_A
  have htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inr (Or.inl hL3)
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL hnPGL
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_card_inf h9
  have hR0 : R ≠ ⊥ := ne_bot_of_mem_scriptQPiStarC h1413 h142 hbot hR hfail hcΓ hL h3 hAa hR'
  have hQ : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
    obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with
        ⟨-, -, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hP, -⟩ | ⟨hcL', -⟩
    · rcases hcase with ⟨-, hQ⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
      · exact hQ
      · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
      · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
    · rcases hcase with hφ | hφ
      · obtain ⟨φ⟩ := hφ
        obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
        exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
      · obtain ⟨φ⟩ := hφ
        obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
        exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
    · exact absurd hP hnPGL
    · exact absurd hcL' hcL
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hD.isElemAbelian.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ebar := (A.subgroupOf L).map π with hEbar
  have hE9 : Nat.card Ebar = 9 := by rw [hEbar, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L
        hD.isElemAbelian)
  have hpt : ∀ z ∈ Ebar, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', ⟨Subgroup.mem_subgroupOf.mp hy', y'.2⟩, fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  have htrans : ∀ y₀ ∈ Ebar, y₀ ≠ 1 → ∀ y₁ ∈ Ebar, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (Ebar : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
    intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
    obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
    obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
    obtain ⟨w, hwL, hwN, hw⟩ :=
      exists_conj_eq_of_autIn hc3 hcL hLc hAa hB h9 hQ hy₀ hy₁ hy₀1 hy₁1
    refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
      have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := by
        rw [Subgroup.inf_subgroupOf_right]
      rw [hEq] at hwN'
      exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
  have hRL : R ≤ L := hR'.prop.1.2
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR'.prop
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR'.prop.1.1.1.2.2
  have hθodd : ¬ 2 ∣ Nat.card θ := odd_card_thetaC h1413 hR hfail hcΓ hL
  have hRθ : ∀ (x : G) (hxL : x ∈ L), x ∈ R → π ⟨x, hxL⟩ = 1 → x = 1 := by
    intro x hxL hxR hx1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    have h1 : (⟨x, hxL⟩ : ↥L) = 1 :=
      eq_one_of_mem_of_odd (P := R.subgroupOf L) hR2.comap_subtype hθodd
        (Subgroup.mem_subgroupOf.mpr hxR) hx1
    exact congrArg Subtype.val h1
  set Rbar := (R.subgroupOf L).map π with hRbar
  have hRbar2 : IsPGroup 2 Rbar := hR2.comap_subtype.map π
  have hmemR : ∀ (x : G) (hxL : x ∈ L), x ∈ R → π ⟨x, hxL⟩ ∈ Rbar := fun x hxL hxR =>
    ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxR, rfl⟩
  have hRbar0 : Rbar ≠ ⊥ := by
    intro h0
    apply hR0
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 := hmemR x (hRL hx) hx
    rw [h0, Subgroup.mem_bot] at h1
    exact hRθ x (hRL hx) hx h1
  have hERbar : Ebar ≤ Subgroup.normalizer (Rbar : Set (↥L ⧸ θ)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have h1 : (b : G) * r * (b : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hAR (Subgroup.mem_subgroupOf.mp hb)) _).mp hrR
    refine ⟨b * r * b⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hC3 := hK _ hL3 Ebar hEe hE9 htrans Rbar hRbar2 hRbar0 hERbar
  have hcent : ∀ (e : G) (heL : e ∈ L), e ∈ A →
      π ⟨e, heL⟩ ∈ Subgroup.centralizer (Rbar : Set (↥L ⧸ θ)) →
        e ∈ Subgroup.centralizer (R : Set G) := by
    intro e heL heA he
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrL := hRL hr
    have h1 := Subgroup.mem_centralizer_iff.mp he _ (hmemR r hrL hr)
    have hxR : r * e * r⁻¹ * e⁻¹ ∈ R := by
      have h2 : e * r⁻¹ * e⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hAR heA) _).mp (inv_mem hr)
      have h3 := mul_mem hr h2
      rwa [← mul_assoc, ← mul_assoc] at h3
    have hxL : r * e * r⁻¹ * e⁻¹ ∈ L :=
      mul_mem (mul_mem (mul_mem hrL heL) (inv_mem hrL)) (inv_mem heL)
    have hπx : π ⟨r * e * r⁻¹ * e⁻¹, hxL⟩ = 1 := by
      have h4 : (⟨r * e * r⁻¹ * e⁻¹, hxL⟩ : ↥L) =
          ⟨r, hrL⟩ * ⟨e, heL⟩ * (⟨r, hrL⟩ : ↥L)⁻¹ * (⟨e, heL⟩ : ↥L)⁻¹ := rfl
      rw [h4, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hx1 := hRθ _ hxL hxR hπx
    calc r * e = r * e * r⁻¹ * e⁻¹ * (e * r) := by group
      _ = e * r := by rw [hx1, one_mul]
  have hcent' : ∀ (e : G) (heL : e ∈ L), e ∈ Subgroup.centralizer (R : Set G) →
      π ⟨e, heL⟩ ∈ Subgroup.centralizer (Rbar : Set (↥L ⧸ θ)) := by
    intro e heL he
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp he _ (Subgroup.mem_subgroupOf.mp hr)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  have hnt : Nontrivial (Ebar ⊓ Subgroup.centralizer (Rbar : Set (↥L ⧸ θ)) : Subgroup _) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hC3]
    norm_num
  obtain ⟨z, hz, hz1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp hnt
  obtain ⟨y, hyAL, hy1, hyL, rfl⟩ := hpt z hz.1 hz1
  have hyC : y ∈ Subgroup.centralizer (R : Set G) := hcent y hyL hyAL.1 hz.2
  have hne : A ⊓ Subgroup.centralizer (R : Set G) ≠ A := by
    intro h
    have hle : Ebar ≤ Ebar ⊓ Subgroup.centralizer (Rbar : Set (↥L ⧸ θ)) := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨⟨b, hb, rfl⟩, hcent' b b.2 ?_⟩
      have hbA : (b : G) ∈ A := Subgroup.mem_subgroupOf.mp hb
      rw [← h] at hbA
      exact hbA.2
    have h1 := Subgroup.card_le_of_le hle
    rw [hC3, hE9] at h1
    omega
  have hcC : c ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hRL hr))
  exact isHyperplane_of_mem hA.2 hD.orderOf_eq hcL inf_le_left hne ⟨hcA, hcC⟩ ⟨hyAL.1, hyC⟩
    hyL hy1

open Proof1413Res3 Proof1413Res6

theorem item1419OneR_of_c
    (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (h131 : Item131) (hPGL : Item1412NotPGLR) (hL3 : Step1419OneL3R) : Item1419OneR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL htype R hR'
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  have hPGLc := hPGL G A c₀ L₀ hR hfail c hcΓ L hL
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL hPGLc
  have hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
      R ∈ scriptQPi A (lB A) L (piOf 2) := fun R hRL hAR hR2 =>
    Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hRL hAR hR2
  rcases htype with hA7 | hL3' | hM12
  · obtain ⟨φ⟩ := hA7
    have hθ := theta_eq_bot_of_gammaC h1413 h135 hR hfail hcΓ hL (Or.inr (Or.inl ⟨φ⟩))
    have ψ : ↥L ≃* ↥(alternatingGroup (Fin 7)) := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hθ.symm).trans φ)
    exact a7_family hD.le_centralizer hD.isElemAbelian hD.mem_A hD.orderOf_eq hcL hD.card_eq
      hAa h9 ψ hQ hR'
  · exact hL3 G A c₀ L₀ hR hfail c hcΓ L hL hL3' hPGLc R hR'
  · obtain ⟨φ⟩ := hM12
    obtain ⟨χ, hχ⟩ := exists_m12_equivC h1413 h135 h131 hR hfail hcΓ hL φ
    obtain ⟨i, -, hB⟩ := m12_family hD.le_centralizer hD.isElemAbelian hD.mem_A hD.orderOf_eq hcL
      hD.card_eq hAa χ hχ hQ hR'
    exact hB

theorem step1419InvR_of_c
    (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (h131 : Item131) : Step1419InvR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL htype hPGLc R hR'
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL hPGLc
  rcases htype with hA7 | hL3 | hM12
  · obtain ⟨t, ht, htinv⟩ := exists_inv_of_order_four_type h131 hD hcL (Or.inl hA7) hPGLc
    exact ⟨t, ht, fun x hx => htinv x ⟨hx.1.1, hx.2⟩⟩
  · obtain ⟨t, ht, htinv⟩ := exists_inv_of_order_four_type h131 hD hcL (Or.inr hL3) hPGLc
    exact ⟨t, ht, fun x hx => htinv x ⟨hx.1.1, hx.2⟩⟩
  · obtain ⟨φ⟩ := hM12
    have hQ : ∀ R : Subgroup G, R ≤ L → A ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 R →
        R ∈ scriptQPi A (lB A) L (piOf 2) := fun R hRL hAR hR2 =>
      Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hRL hAR hR2
    obtain ⟨χ, hχ⟩ := exists_m12_equivC h1413 h135 h131 hR hfail hcΓ hL φ
    obtain ⟨i, hRi, hB⟩ := m12_family hD.le_centralizer hD.isElemAbelian hD.mem_A hD.orderOf_eq
      hcL hD.card_eq hAa χ hχ hQ hR'
    exact m12_inv hD.le_centralizer hD.isElemAbelian hD.mem_A hD.orderOf_eq hcL hD.card_eq hAa
      χ hχ hRi hB

theorem item1419R_of_c
    (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h1418 : Item1418R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hKL3 : KS1419LThreePi) : Item1419R :=
  have hOne := item1419OneR_of_c h1413 h135 h142 h131 hPGL
    (step1419OneL3R_of_c h1413 h142 hbot h131 hKL3)
  item1419R_of_parts hOne (item1419TwoR_of_c h1413 h142 hbot h131 h133 h1416 hPGL h1418 h422 h45
    hOne (step1419InvR_of_c h1413 h135 h142 h131))

end CFSG.RankThree.PartTwo.Sec14
