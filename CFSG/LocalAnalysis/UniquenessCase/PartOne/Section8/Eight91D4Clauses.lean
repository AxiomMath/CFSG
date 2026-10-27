module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Heis
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.RankThree.PartTwo.Sec12.Item122
import CFSG.RankThree.PartTwo.Sec12.Hering129LSL3
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (DerInf8)
open CFSG.ABGLocalTools (IsSylowOf)

namespace R891D4Setup

variable {X : Type} [Group X] [Finite X] {n : ℕ} {S B : Subgroup X}

omit [Finite X] in
private theorem r891_perfect_of_sl3Two {R : Subgroup X} {n : ℕ} (h : R891SL3Two ↥R n)
    (hn : 2 ≤ n) : ⁅R, R⁆ = R := by
  have hq : CFSG.Open.IsQuasisimple ↥R := by
    rcases h with ⟨h1, _⟩ | ⟨_, _, hTC⟩ | ⟨_, _, hTC⟩
    · omega
    · exact hTC.1
    · exact hTC.1
  have hmap := congrArg (Subgroup.map R.subtype) hq.1
  simpa only [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    Subgroup.range_subtype] using hmap

private theorem r891_x_eq_layer (h : R891D4Setup n S B) {P : Subgroup X}
    {s : X} (hZ : ZOf P = zpowers s) {R : Subgroup X} (hR : R891D4Layer n s R) :
    R891X (⊤ : Subgroup X) (ZOf P) n = R := by
  have hcent : Subgroup.centralizer ((ZOf P : Subgroup X) : Set X) =
      Subgroup.centralizer ({s} : Set X) := by
    rw [hZ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [R891X]
  by_cases hn : n = 1
  · rw [if_pos hn, top_inf_eq, hcent]
    exact hR.opp_eq hn
  · rw [if_neg hn, top_inf_eq, hcent]
    have hn1 : 1 ≤ n := h.one_le
    have hn2 : 2 ≤ n := by omega
    exact derInf8_eq_of_perfect hR.le_centralizer
      (r891_perfect_of_sl3Two hR.sl3Two hn2) hR.commutator_mem

private theorem r891_center_eq_zpowers {R : Subgroup X} {s : X} (hsR : s ∈ R)
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hcentR : R ≤ Subgroup.centralizer ({s} : Set X))
    (hcard : Nat.card (Subgroup.center ↥R) = 3) :
    Subgroup.center ↥R = Subgroup.zpowers (⟨s, hsR⟩ : ↥R) := by
  have hsR_ord : orderOf (⟨s, hsR⟩ : ↥R) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hs3 hs1
  have hmem : (⟨s, hsR⟩ : ↥R) ∈ Subgroup.center ↥R := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcentR y.2)
  have hle : Subgroup.zpowers (⟨s, hsR⟩ : ↥R) ≤ Subgroup.center ↥R :=
    Subgroup.zpowers_le.mpr hmem
  have hcard' : Nat.card (Subgroup.center ↥R) ≤
      Nat.card (Subgroup.zpowers (⟨s, hsR⟩ : ↥R)) := by
    rw [Nat.card_zpowers, hsR_ord, hcard]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard').symm

private theorem r891_exists_threeB_inverting (h : R891D4Setup n S B) :
    ∃ t ∈ B, t ^ 3 = 1 ∧ t ≠ 1 ∧ ∃ j ∈ B, j * t * j⁻¹ = t⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eB⟩⟩ := h.sl2B
  let : Field L := hLfield
  let : Finite L := hLfin
  let eB' : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) L := eB
  have h3dvd : 3 ∣ Nat.card B := by
    rw [h.card_B]
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
    exact dvd_mul_of_dvd_right h3 (2 ^ n)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3dvd
  let t : X := (x : X)
  have htB : t ∈ B := x.2
  have ht_ord : orderOf t = 3 := by
    change orderOf (x : X) = 3
    rw [Subgroup.orderOf_coe, hx]
  have ht3 : t ^ 3 = 1 := by
    rw [← ht_ord]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht_ord
    omega
  have hchar : CharP L 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hLcard
  let : CharP L 2 := hchar
  obtain ⟨a, ha2, hax⟩ :=
    CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv (eB' x)
  let j : X := (eB'.symm a : ↥B)
  have hjB : j ∈ B := (eB'.symm a).2
  have hjt : j * t * j⁻¹ = t⁻¹ := by
    have h' : (eB'.symm a * x * (eB'.symm a)⁻¹ : ↥B) = x⁻¹ := by
      apply eB'.injective
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply,
        inv_eq_of_mul_eq_one_right ha2] using hax
    have := congrArg Subtype.val h'
    simpa only [j, t, Subgroup.coe_mul, Subgroup.coe_inv] using this
  exact ⟨t, htB, ht3, ht1, j, hjB, hjt⟩

private theorem r891_extraspecial_conj (h : R891D4Setup n S B) {P : Subgroup X}
    (hP : IsSylowOf 3 P ⊤) {s : X} (hZ : ZOf P = zpowers s)
    {R : Subgroup X} (hR : R891D4Layer n s R) :
    ∃ R' : Subgroup X, R' ≤ R891X (⊤ : Subgroup X) (ZOf P) n ∧ R' ≤ P ∧
      IsExtraspecialExpP 3 1 ↥R' ∧ ZOf P ≤ R' := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hres : R891X (⊤ : Subgroup X) (ZOf P) n = R :=
    r891_x_eq_layer h hZ hR
  have hsZ : s ∈ ZOf P := by
    rw [hZ]
    exact Subgroup.mem_zpowers s
  have hsc : s ∈ Subgroup.centralizer (P : Set X) := (Subgroup.mem_inf.mp hsZ).2
  have hPcent : P ≤ Subgroup.centralizer ({s} : Set X) := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hsc p hp)
  have hPsyl : IsSylowOf 3 P (Subgroup.centralizer ({s} : Set X)) :=
    hP.of_le hPcent le_top
  obtain ⟨E₀, hE₀center, hE₀extra⟩ :=
    exists_isExtraspecialExpP_of_isSLThreePiAt (Q := ↥R) (q := 2 ^ n) hR.slThreePi
  let E : Subgroup X := E₀.map R.subtype
  have hER : E ≤ R := Subgroup.map_subtype_le E₀
  have hcenter_mem : (⟨s, hR.mem⟩ : ↥R) ∈ Subgroup.center ↥R := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hR.le_centralizer y.2)
  have hsE : s ∈ E := Subgroup.mem_map.mpr ⟨⟨s, hR.mem⟩, hE₀center hcenter_mem, rfl⟩
  have hEcent : E ≤ Subgroup.centralizer ({s} : Set X) := fun x hx =>
    hR.le_centralizer (hER hx)
  have hE₀card : Nat.card ↥E₀ = 3 ^ 3 := by
    unfold IsExtraspecialExpP at hE₀extra
    simpa using hE₀extra.1
  have hEcard : Nat.card ↥E = 3 ^ 3 := by
    rw [show E = E₀.map R.subtype from rfl,
      Subgroup.card_map_of_injective R.subtype_injective, hE₀card]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) hEcard
  obtain ⟨c, hcC, hcP⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf
    (p := 3) (G := X) (K := Subgroup.centralizer ({s} : Set X)) (R := P) (Q := E)
    hPsyl hEcent hEp
  let R' : Subgroup X := E.map (MulAut.conj c⁻¹).toMonoidHom
  have hcC' : c⁻¹ ∈ Subgroup.centralizer ({s} : Set X) := Subgroup.inv_mem _ hcC
  have hconj : ∀ y : X, (MulAut.conj c⁻¹) y = c⁻¹ * y * c := fun y => by
    rw [MulAut.conj_apply, inv_inv]
  have hR'P : R' ≤ P := by
    rintro x ⟨y, hy, rfl⟩
    change (MulAut.conj c⁻¹) y ∈ P
    rw [hconj]
    exact hcP y hy
  have hR'R : R' ≤ R := by
    rintro x ⟨y, hy, rfl⟩
    have hyR : y ∈ R := hER hy
    have hyC : y ∈ Subgroup.centralizer ({s} : Set X) := hEcent hy
    have hcommR : c⁻¹ * y * c * y⁻¹ ∈ R := by
      simpa only [inv_inv] using hR.commutator_mem c⁻¹ hcC' y hyC
    change (MulAut.conj c⁻¹) y ∈ R
    rw [hconj]
    have h1 : c⁻¹ * y * c = c⁻¹ * y * c * y⁻¹ * y := by group
    rw [h1]
    exact Subgroup.mul_mem R hcommR hyR
  let eE : ↥E₀ ≃* ↥E := Subgroup.equivMapOfInjective E₀ R.subtype R.subtype_injective
  let eR' : ↥E ≃* ↥R' := Subgroup.equivMapOfInjective E
    (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
  have hR'extra : IsExtraspecialExpP 3 1 ↥R' :=
    isExtraspecialExpP_of_mulEquiv (eE.trans eR').symm hE₀extra
  have hfix : (MulAut.conj c⁻¹) s = s := by
    rw [MulAut.conj_apply, inv_inv, Subgroup.mem_centralizer_singleton_iff.mp hcC']
    group
  have hsR' : s ∈ R' := Subgroup.mem_map.mpr ⟨s, hsE, hfix⟩
  have hZR' : ZOf P ≤ R' := by
    rw [hZ]
    exact Subgroup.zpowers_le.mpr hsR'
  exact ⟨R', by rwa [hres], hR'P, hR'extra, hZR'⟩

theorem sylow_clauses (h : R891D4Setup n S B) {P : Subgroup X} (hP : IsSylowOf 3 P ⊤) {s : X}
    (hs : s ∈ S) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hZ : ZOf P = zpowers s) :
    (∃ R : Subgroup X, R ≤ R891X (⊤ : Subgroup X) (ZOf P) n ∧ R ≤ P ∧
        IsExtraspecialExpP 3 1 ↥R ∧ ZOf P ≤ R) ∧
      R891SL3Two ↥(R891X (⊤ : Subgroup X) (ZOf P) n) n ∧
      ∀ φ : MulAut X, (ZOf P).map φ.toMonoidHom ≤ R891X (⊤ : Subgroup X) (ZOf P) n →
        (ZOf P).map φ.toMonoidHom = ZOf P := by
  classical
  obtain ⟨R, hR⟩ := h.layer s hs hs3 hs1
  have hres : R891X (⊤ : Subgroup X) (ZOf P) n = R :=
    r891_x_eq_layer h hZ hR
  refine ⟨r891_extraspecial_conj h hP hZ hR, ?sl3, ?weak⟩
  · rw [hres]
    exact hR.sl3Two
  ·
    intro φ hφ
    have hφR : (ZOf P).map φ.toMonoidHom ≤ R := by rwa [hres] at hφ
    have hsZ : s ∈ ZOf P := by
      rw [hZ]
      exact Subgroup.mem_zpowers s
    have hs'R : φ s ∈ R := hφR (Subgroup.mem_map_of_mem φ.toMonoidHom hsZ)
    let s' : X := φ s
    have hs'3 : s' ^ 3 = 1 := by
      change (φ s) ^ 3 = 1
      rw [← map_pow, hs3, map_one]
    have hs'1 : s' ≠ 1 := by
      intro h1
      apply hs1
      apply φ.injective
      rw [map_one]
      simpa only [s'] using h1
    have hSL3Pi : CFSG.RankThree.PartTwo.Sec4.IsSLThreePi ↥R := ⟨2 ^ n, hR.slThreePi⟩
    have hZcenter : Nat.card (Subgroup.center ↥R) = 3 :=
      CFSG.RankThree.PartTwo.Sec12.card_center_eq_three_of_isSLThreePi hSL3Pi
    have hcenter_eq : Subgroup.center ↥R = Subgroup.zpowers (⟨s, hR.mem⟩ : ↥R) :=
      r891_center_eq_zpowers hR.mem hs3 hs1 hR.le_centralizer hZcenter
    by_cases hcentral : (⟨s', hs'R⟩ : ↥R) ∈ Subgroup.center ↥R
    ·
      have hzp : s' ∈ Subgroup.zpowers s := by
        rw [hcenter_eq] at hcentral
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcentral
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hle : Subgroup.zpowers s' ≤ Subgroup.zpowers s := Subgroup.zpowers_le.mpr hzp
      have hcard : Nat.card (Subgroup.zpowers s) ≤ Nat.card (Subgroup.zpowers s') := by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hs'3 hs'1,
          orderOf_eq_prime hs3 hs1]
      have hEq : Subgroup.zpowers s' = Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge hle hcard
      calc (ZOf P).map φ.toMonoidHom = (Subgroup.zpowers s).map φ.toMonoidHom := by rw [hZ]
        _ = Subgroup.zpowers (φ s) := MonoidHom.map_zpowers φ.toMonoidHom s
        _ = Subgroup.zpowers s := by simpa only [s'] using hEq
        _ = ZOf P := by rw [hZ]
    ·
      exfalso
      have ha3 : (⟨s', hs'R⟩ : ↥R) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hs'3
      obtain ⟨t, htB, ht3, ht1, j₀, hj₀B, hj₀inv⟩ := r891_exists_threeB_inverting h
      have htC : t ∈ Subgroup.centralizer ({s} : Set X) := by
        rw [h.cent] at htB
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp htB s hs).symm
      have hj₀C : j₀ ∈ Subgroup.centralizer ({s} : Set X) := by
        rw [h.cent] at hj₀B
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hj₀B s hs).symm
      have htR : t ∈ R := by
        have hcomm : j₀ * t * j₀⁻¹ * t⁻¹ ∈ R := hR.commutator_mem j₀ hj₀C t htC
        have hinv : t⁻¹ * t⁻¹ = t := by
          have ht2 : t⁻¹ = t * t := by
            apply inv_eq_of_mul_eq_one_right
            simpa only [pow_three] using ht3
          calc t⁻¹ * t⁻¹ = (t * t) * (t * t) := by rw [ht2]
            _ = t := by
                  have h1 : (t * t) * (t * t) = (t * t * t) * t := by group
                  have ht3' : t * t * t = 1 := by
                    simpa only [pow_three'] using ht3
                  rw [h1, ht3', one_mul]
        have htj : j₀ * t * j₀⁻¹ * t⁻¹ = t := by
          rw [hj₀inv]
          exact hinv
        exact htj ▸ hcomm
      have ht_notcenter : (⟨t, htR⟩ : ↥R) ∉ Subgroup.center ↥R := by
        intro htc
        have htS : t ∈ S := by
          have hzp : t ∈ Subgroup.zpowers s := by
            rw [hcenter_eq] at htc
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htc
            rw [Subgroup.mem_zpowers_iff]
            exact ⟨k, by simpa using congrArg Subtype.val hk⟩
          exact Subgroup.zpowers_le.mpr hs hzp
        have htbot : t ∈ S ⊓ B := Subgroup.mem_inf.mpr ⟨htS, htB⟩
        rw [h.inf_eq_bot] at htbot
        exact ht1 (Subgroup.mem_bot.mp htbot)
      have hb3 : (⟨t, htR⟩ : ↥R) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using ht3
      have hn1 : 1 ≤ n := h.one_le
      let r : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
      have hr : r.card = 2 ^ n := TauCeti.PrimePower.card_def r
      have hQ : CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt ↥R r.card := by
        rw [hr]
        exact hR.slThreePi
      obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129L.exists_conj_of_isSLThreePiAt
        (Q := ↥R) (r := r) hQ (a := ⟨s', hs'R⟩) (b := ⟨t, htR⟩) ha3 hb3 hcentral
        ht_notcenter
      have hgX : (g : X) * s' * (g : X)⁻¹ = t := by
        simpa using congrArg Subtype.val hg
      let ψ : MulAut X := MulAut.conj (g : X) * φ
      have hψs : ψ s = t := by
        change MulAut.conj (g : X) (φ s) = t
        rw [MulAut.conj_apply]
        simpa only [s'] using hgX
      have hmap : (Subgroup.zpowers s).map ψ.toMonoidHom = Subgroup.zpowers t := by
        rw [MonoidHom.map_zpowers]
        change Subgroup.zpowers (ψ s) = Subgroup.zpowers t
        rw [hψs]
      exact h.map_zpowers_ne hs hs3 hs1 htB ht3 ht1 ψ hmap

end R891D4Setup

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
