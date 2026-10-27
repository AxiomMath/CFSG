module

public import CFSG.Walter.W67.Section5.P56AbAut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.Walter.Defs
public import CFSG.Walter.W67.Section5.Lemma53
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PStableIso
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_2
import CFSG.Walter.Bender1970.S1.QdNotInvolved
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate42
public import Certificates.Certificate43
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Walter.W67.Sec56

open P56Ab
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_quadratic
    (hab : HasAbelianSylowTwo G) {R V : Subgroup G}
    (hR3 : IsPGroup 3 R) (hR1 : R ≠ ⊥) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hVN : V ≤ Subgroup.normalizer (R : Set G))
    (hq : ∀ v ∈ V, ∀ m ∈ R, v * (m⁻¹ * (v * m * v⁻¹)) * v⁻¹ = m⁻¹ * (v * m * v⁻¹)) :
    ∃ M : Subgroup G, V ≤ M ∧ M ≤ Subgroup.normalizer (R : Set G) ∧
      (∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.normalizer (M : Set G)) ∧
      R ⊓ Subgroup.centralizer (M : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Γ := Subgroup.normalizer (R : Set G) with hΓdef
  set φ : Γ →* MulAut R := conjAut Γ R le_rfl with hφdef
  set P : Subgroup Γ := R.subgroupOf Γ with hPdef
  have hPn : P.Normal := Subgroup.normal_in_normalizer
  have hPp : IsPGroup 3 P := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  have hst : Glauberman.pStableLocal 3 Γ := by
    have hab' : HasAbelianSylowTwo Γ := BenderSuzuki.HasAbelianSylow.subgroup hab Γ
    have hstabQ : Glauberman.pStable 3 ((⊤ : Subgroup Γ) ⧸ (⊥ : Subgroup (⊤ : Subgroup Γ))) :=
      (Glauberman.lemma6_3 (by norm_num)).mp (qd_not_involved_of_hasAbelianSylowTwo hab'
        (by norm_num)) ⊤ ⊥
    have hstab : Glauberman.pStable 3 Γ :=
      (Glauberman.pStable_iso (QuotientGroup.quotientBot.trans Subgroup.topEquiv)).mp hstabQ
    refine Glauberman.pStableLocal_of_core_ne_bot 3 hstab ?_
    intro hbot
    have hle : P ≤ pCore 3 Γ := le_sSup ⟨hPn, hPp⟩
    rw [hbot] at hle
    apply hR1
    rw [eq_bot_iff]
    intro m hm
    have := hle (show (⟨m, Subgroup.le_normalizer hm⟩ : Γ) ∈ P from hm)
    rw [Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hcorePn : (pPrimeCore 3 Γ ⊔ P).Normal := by
    have : (pPrimeCore 3 Γ).Normal := Subgroup.sSup_normal _ fun _ hK => hK.1
    exact Subgroup.sup_normal _ _
  set N' := Subgroup.normalizer (P : Set Γ) with hN'
  set C' := Subgroup.centralizer (P : Set Γ) with hC'
  have hN'top : ∀ y : Γ, y ∈ N' := fun y => by
    rw [hN', Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact Subgroup.mem_top _
  let f : N' →* φ.range := φ.rangeRestrict.comp N'.subtype
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, rfl⟩⟩
    exact ⟨⟨y, hN'top y⟩, rfl⟩
  have hker : C'.subgroupOf N' = f.ker := by
    ext y
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change (y : Γ) ∈ C' ↔ φ.rangeRestrict y = 1
    rw [← Subtype.coe_inj, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, hφdef,
      conjAut_eq_one_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h m hm
      exact (congrArg Subtype.val (h ⟨m, Subgroup.le_normalizer hm⟩ hm)).symm
    · intro h m hm
      exact Subtype.ext (h m hm).symm
  let e : (N' ⧸ C'.subgroupOf N') ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hmap := pCore_map_iso 3 e
  set O := pCore 3 φ.range with hOdef
  have hVO : ∀ v (hv : v ∈ V), φ.rangeRestrict ⟨v, hVN hv⟩ ∈ O := by
    intro v hv
    set x' : Γ := ⟨v, hVN hv⟩ with hx'
    set W : Subgroup Γ := (R ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf Γ
    have hPW : ⁅P, Subgroup.zpowers x'⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro m hm z hz
      obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers x')
      have hmR : (m : G) ∈ R := hm
      set u : G := (m : G)⁻¹ * (v * m * v⁻¹) with hu
      have huR : u ∈ R := R.mul_mem (R.inv_mem hmR)
        ((Subgroup.mem_normalizer_iff.mp (hVN hv) m).mp hmR)
      have hux : v * u * v⁻¹ = u := hq v hv m hmR
      have hxu : v * u = u * v := by
        calc v * u = v * u * v⁻¹ * v := by group
          _ = u * v := by rw [hux]
      have hpow : ∀ k : ℕ, v ^ k * (m : G) * (v ^ k)⁻¹ = m * u ^ k := by
        have hstep : v * (m : G) * v⁻¹ = m * u := by rw [hu]; group
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hcomm : v * u ^ k * v⁻¹ = u ^ k := by
            rw [(Commute.pow_right (show Commute v u from hxu) k).eq, mul_inv_cancel_right]
          calc v ^ (k + 1) * (m : G) * (v ^ (k + 1))⁻¹ =
                v * (v ^ k * (m : G) * (v ^ k)⁻¹) * v⁻¹ := by group
            _ = (v * m * v⁻¹) * (v * u ^ k * v⁻¹) := by rw [ih]; group
            _ = m * u ^ (k + 1) := by rw [hstep, hcomm, pow_succ', mul_assoc]
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅m, x' ^ k⁆ : Γ) : G) = (u ^ k)⁻¹ := by
        rw [commutatorElement_def]
        push_cast
        change (m : G) * v ^ k * (m : G)⁻¹ * (v ^ k)⁻¹ = (u ^ k)⁻¹
        have hmu : (m : G) * u ^ k = u ^ k * m := hRc _ hmR _ (R.pow_mem huR k)
        calc (m : G) * v ^ k * (m : G)⁻¹ * (v ^ k)⁻¹ =
              m * (v ^ k * (m : G) * (v ^ k)⁻¹)⁻¹ := by group
          _ = (u ^ k)⁻¹ := by rw [hpow, hmu]; group
      rw [hcoe]
      refine Subgroup.mem_inf.mpr ⟨R.inv_mem (R.pow_mem huR k), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [show (u ^ k)⁻¹ * v = v * (u ^ k)⁻¹ by
        rw [← (Commute.inv_left (Commute.pow_left (show Commute v u from hxu).symm k)).eq]]
    have hWZ : ⁅W, Subgroup.zpowers x'⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw z hz
      obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers x')
      rw [Subgroup.mem_bot]
      obtain ⟨-, hwC⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
      have hwx : (w : G) * v = v * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
      apply Subtype.ext
      rw [commutatorElement_def]
      push_cast
      change (w : G) * v ^ k * (w : G)⁻¹ * (v ^ k)⁻¹ = 1
      rw [(Commute.pow_right (show Commute (w : G) v from hwx) k).eq]
      group
    have hquad : ⁅⁅P, Subgroup.zpowers x'⁆, Subgroup.zpowers x'⁆ = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.commutator_mono hPW le_rfl).trans hWZ.le)
    have h := hst P hPp hcorePn x' (hN'top x') hquad
    have h2 : e (QuotientGroup.mk' (C'.subgroupOf N') ⟨x', hN'top x'⟩) ∈ O := by
      rw [← hmap]
      exact ⟨_, h, rfl⟩
    exact h2
  have hO3 : IsPGroup 3 O := pCore_isPGroup
  let : MulAction O R := MulAction.compHom R (φ.range.subtype.comp O.subtype)
  have hR3' : 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hR1 (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 3 hk0
  have h1fix : (1 : R) ∈ MulAction.fixedPoints O R := fun o => by
    change ((o : φ.range) : MulAut R) 1 = 1
    exact map_one _
  obtain ⟨r, hrfix, hr1⟩ :=
    hO3.exists_fixed_point_of_prime_dvd_card_of_fixed_point R hR3' h1fix
  set M₀ : Subgroup Γ := O.comap φ.rangeRestrict with hM₀def
  refine ⟨M₀.map Γ.subtype, fun v hv => ⟨⟨v, hVN hv⟩, hVO v hv, rfl⟩,
    Subgroup.map_subtype_le _, fun g hg => ?_, ?_⟩
  · apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    change φ.rangeRestrict (⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact (pCore_normal (p := 3) (G := φ.range)).conj_mem _ hm _
  · intro hbot
    apply hr1
    have hrM : (r : G) ∈ R ⊓ Subgroup.centralizer ((M₀.map Γ.subtype : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨r.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      have h1 := congrArg Subtype.val (hrfix ⟨φ.rangeRestrict m, hm⟩)
      change ((φ m r : R) : G) = r at h1
      rw [hφdef, conjAut_apply_coe] at h1
      change (m : G) * r = r * m
      calc (m : G) * r = (m : G) * r * (m : G)⁻¹ * m := by group
        _ = r * m := by rw [h1]
    rw [hbot, Subgroup.mem_bot] at hrM
    exact (Subtype.ext hrM).symm

end CFSG.Walter.W67.Sec56
