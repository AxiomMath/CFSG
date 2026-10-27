module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425Three
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankContract
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowU58
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Move
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Transfer
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA9
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLUsed
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166
import CFSG.ClassicalInvolution.Balance.PassTwoFinal

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11
open scoped MatrixGroups

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem map_le_centralizer_isSubnormal [Finite X] (e : X ≃* Y) {z : X} {J : Subgroup X}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set X))
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set X))).IsSubnormal) :
    J.map (e : X →* Y) ≤ Subgroup.centralizer ({e z} : Set Y) ∧
      ((J.map (e : X →* Y)).subgroupOf (Subgroup.centralizer ({e z} : Set Y))).IsSubnormal := by
  set C := Subgroup.centralizer ({z} : Set X)
  have hC : C.map (e : X →* Y) = Subgroup.centralizer ({e z} : Set Y) :=
    map_centralizer_singleton_equiv e z
  refine ⟨hC ▸ Subgroup.map_mono hJC, ?_⟩
  let eC : C ≃* Subgroup.centralizer ({e z} : Set Y) :=
    (C.equivMapOfInjective _ e.injective).trans (MulEquiv.subgroupCongr hC)
  have hmap := hJs.map (f := (eC : C →* Subgroup.centralizer ({e z} : Set Y))) eC.surjective
  have heq : (J.subgroupOf C).map (eC : C →* Subgroup.centralizer ({e z} : Set Y)) =
      (J.map (e : X →* Y)).subgroupOf (Subgroup.centralizer ({e z} : Set Y)) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hxJ, hxy⟩
      refine ⟨x, hxJ, ?_⟩
      have := congrArg Subtype.val hxy
      exact this
    · rintro ⟨x, hxJ, rfl⟩
      exact ⟨⟨x, hJC hxJ⟩, hxJ, rfl⟩
  rwa [heq] at hmap

end Transport

section G2

open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


variable {F : Type} [Field F]

theorem false_of_threeB [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {z : adjointGroup .G2 F} (hzM : z ∈ g2LongSL2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J) (hzJ : z ∈ J) : False := by
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨hcomm, -⟩ := g2ThreeBCent_holds F hchar h4 z hzM hz3 hz1
  have hJS : J ≤ g2ShortSL2 F :=
    le_of_commutators_mem hJC (Subgroup.isPerfect_iff.mp hJq.1) hcomm
  have hzS := hJS hzJ
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := F)
  have hZ : Subgroup.center (g2ShortSL2 F) = ⊥ := by
    rw [← Subgroup.map_center_eq e, CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.map_bot]
  have hzc : (⟨z, hzS⟩ : g2ShortSL2 F) ∈ Subgroup.center (g2ShortSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (g2Short_commute_g2Long g.2 hzM)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hz1 (congrArg Subtype.val hzc)

theorem isSLThreePiAt_of_threeA_odd [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (ho : Odd n) {z : adjointGroup .G2 F} (hzS : z ∈ g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal) :
    IsSLThreePiAt J (2 ^ n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' F
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  have hmod : 2 ^ n % 3 = 2 := by
    obtain ⟨m, rfl⟩ := ho
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : 3 ∣ Nat.card F + 1 := by
    rw [hF]
    omega
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hF h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (2 ^ n) ^ 2 := by rw [natCard_quadratic hdeg, hF]
  have hq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro hq
    have h2 : 2 ^ n = 2 := (Prod.mk.inj hq).2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨hSU, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hq
  have hCq : CFSG.IsQuasisimple (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU
  have heq := eq_of_le_of_isQuasisimple hJC le_rfl hJs hCq hJq
  exact ⟨L, inferInstance, inferInstance, Or.inr ⟨hL, hmod, ⟨(MulEquiv.subgroupCongr heq).trans e⟩⟩⟩

section Split

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LieType.HighestRoot CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo

theorem exists_sl3_threeA [Finite F] (h31 : 3 ∣ Nat.card F - 1) {z : adjointGroup .G2 F}
    (hzS : z ∈ g2ShortSL2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ (m : adjointGroup .G2 F) (φ : SL(3, F) →* adjointGroup .G2 F), Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 F)) ∧
      ∀ a ∈ Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 F)),
        ∀ b ∈ Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 F)),
          a * b * a⁻¹ * b⁻¹ ∈ φ.range := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hzS
  have hinj := rhoV_injective (K := F)
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := F)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hz1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom F))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m : adjointGroup .G2 F := ⟨rhoV F P, by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ F _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ F _))⟩
  have hmz : ((m * z * m⁻¹ : adjointGroup .G2 F) : ModGL .G2 F) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [coe_conj, ← hA, ← rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := F)
  have hKer := rootCharKernel_threeA (K := F) ht3
  refine ⟨m, φ, hφinj, ?_, fun x hx y hy => ?_⟩
  ·
    refine range_le_of_a2y φ hφ _ fun γ hγ c => ?_
    rw [mem_centralizer_iff_toral hmz, mem_toralCentralizer]
    refine ⟨(a2y γ c).2, ?_⟩
    rw [coe_a2y hγ]
    have hmem : g2CommRoot (a2pos (γ 0, γ 1)) ∈ rootCharKernel (Pi.mulSingle g2ir t) := by
      rw [hKer]
      exact a2_long_roots hγ
    rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
  ·
    have hx' := (mem_centralizer_iff_toral hmz).mp hx
    have hy' := (mem_centralizer_iff_toral hmz).mp hy
    rw [toralCentralizer_threeA ht3] at hx' hy'
    have h := commutator_mem_of_mem_sup torus_comm
      (torusGroup_le_normalizer_rootSpan (K := F) fun α hα => isRoot_of_long hα) hx' hy'
    have hle : rootSpan .G2 F {g2a, -g2a, g2b, -g2b, g2c, -g2c} ≤
        φ.range.map (adjointGroup .G2 F).subtype := by
      refine iSup₂_le fun α hα => fun g hg => ?_
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
      obtain ⟨γ, hγ, rfl⟩ := exists_a2_root hα
      set s := (rootOperatorFamily .G2).pinnedFamilySign (g2CommRoot (a2pos (γ 0, γ 1)))
      refine ⟨φ (CFSG.LieType.Steinberg.SL.x 2 F γ ((s : F) * c)), ⟨_, rfl⟩, ?_⟩
      rw [Subgroup.coe_subtype, hφ γ hγ, coe_a2y hγ, ← mul_assoc,
        (rootOperatorFamily .G2).pinnedFamilySign_mul_self F, one_mul]
    obtain ⟨w, hw, hwe⟩ := hle h
    have : w = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_subtype] at hwe
      rw [hwe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [← this]
    exact hw

end Split

theorem isSLThreePiAt_of_threeA_even [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (he : Even n) {z : adjointGroup .G2 F} (hzS : z ∈ g2ShortSL2 F) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) {J : Subgroup (adjointGroup .G2 F)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal) :
    IsSLThreePiAt J (2 ^ n) := by
  have hmod : 2 ^ n % 3 = 1 := by
    obtain ⟨m, rfl⟩ := he
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have h31 : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨m, φ, hφinj, hNC, hcomm⟩ := exists_sl3_threeA h31 hzS hz3 hz1
  set e := MulAut.conj m with he'
  obtain ⟨hJ'C, hJ's⟩ := map_le_centralizer_isSubnormal e hJC hJs
  have hez : e z = m * z * m⁻¹ := rfl
  rw [hez] at hJ'C hJ's
  have eJ : J ≃* J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) :=
    J.equivMapOfInjective _ e.injective
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hNq : CFSG.IsQuasisimple φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective hφinj)
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  have hJ'N := le_of_commutators_mem hJ'C (Subgroup.isPerfect_iff.mp hJ'q.1) hcomm
  have heq := eq_of_le_of_isQuasisimple hJ'N hNC hJ's hNq hJ'q
  exact ⟨F, inferInstance, inferInstance, Or.inl ⟨hF, hmod, ⟨eJ.trans
    ((MulEquiv.subgroupCongr heq).trans ((MonoidHom.ofInjective hφinj).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)))⟩⟩⟩

theorem isSLThreePiAt_g2 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (z : adjointGroup .G2 F) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (J : Subgroup (adjointGroup .G2 F))
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 F)))).IsSubnormal)
    (hzJ : z ∈ J) : IsSLThreePiAt J (2 ^ n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds F hchar h4 z hz3 hz1
  set e := MulAut.conj g with he'
  obtain ⟨hJ'C, hJ's⟩ := map_le_centralizer_isSubnormal e hJC hJs
  have eJ : J ≃* J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) :=
    J.equivMapOfInjective _ e.injective
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hez : e z = g * z * g⁻¹ := rfl
  have hz'3 : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz'1 : e z ≠ 1 := by
    rw [Ne, map_eq_one_iff _ e.injective]
    exact hz1
  have hz'J : e z ∈ J.map (e : adjointGroup .G2 F →* adjointGroup .G2 F) := ⟨z, hzJ, rfl⟩
  refine isSLThreePiAt_of_mulEquiv eJ ?_
  rcases hg with hS | hM
  · rw [← hez] at hS
    rcases Nat.even_or_odd n with hev | hodd
    · exact isSLThreePiAt_of_threeA_even hF hev hS hz'3 hz'1 hJ'C hJ'q hJ's
    · exact isSLThreePiAt_of_threeA_odd hF hn hodd hS hz'3 hz'1 hJ'C hJ'q hJ's
  · rw [← hez] at hM
    exact (false_of_threeB h4 hM hz'3 hz'1 hJ'C hJ'q hz'J).elim

noncomputable def adjointQuotientEquivG2 (F : Type) [Field F] [Finite F] :
    AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
  (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
    QuotientGroup.quotientBot

end G2

section Row


theorem noThreeCover_adjointQuotient_g2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : NoThreeCover (AdjointQuotient .G2 F) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · have hF4 : Nat.card F = 4 := by
      rw [hF, show n = 2 by omega]
      norm_num
    have hM := (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.g2_four_card_griessHopfMultiplier
      hF4).2
    haveI : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 F)) :=
      Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
    exact Ronan148L.noThreeCover_of_hopf (MulEquiv.refl _) (by rw [hM]; norm_num)
  · have h5 : 5 ≤ Nat.card F := by
      rw [hF]
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have hM := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier h5).2
    haveI : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 F)) :=
      Finite.of_subsingleton
    have h1 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 F)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hM, ⟨1⟩⟩
    exact Ronan148L.noThreeCover_of_hopf (MulEquiv.refl _) (by rw [h1]; norm_num)

theorem rowOf425_g2 : ∀ q : TauCeti.PrimePower, q.p = 2 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
      RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hq S _ _ _ _ ⟨eSX⟩
  have h3q : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  obtain ⟨F, _, _, hF, ⟨eA⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 eSX
  have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hq2]
  have hn : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent ≤ 1 := by omega
    have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    rw [hq2] at h3q
    omega
  refine row425_of_three (eA.trans (adjointQuotientEquivG2 F))
    (NoThreeCover.of_mulEquiv eA (noThreeCover_adjointQuotient_g2 hF2 hn)) (p := q.p)
    (f := q.exponent) ?_ ?_
  · intro X _ ⟨eXS⟩
    exact Or.inl ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hq hq2 (eXS.trans eSX)⟩
  · intro z hz3 hz1 J hJC hJq hJs hzJ
    rw [hq2]
    exact isSLThreePiAt_g2 hF2 hn z hz3 hz1 J hJC hJq hJs hzJ

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
