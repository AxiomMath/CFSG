module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
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
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 CFSG.SeitzReduction.E6Pilot
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag

section Sylow


theorem exists_conj_le_xHat {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ f) (h3 : 3 ∣ ℓ ^ f + 1) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [CharP Ω ℓ] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) {X : Subgroup (ModGL Tag.E6 Ω)}
    (hXR : X ≤ TwistedDiag.Rgrp Ω Fr) (hX : IsPGroup 3 X) :
    ∃ k ∈ TwistedDiag.thetaFixed Fr, ∃ r ∈ TwistedDiag.Rgrp Ω Fr,
      X.map (MulAut.conj (k * g⁻¹ * r)).toMonoidHom ≤
        xHat Tag.E6 Ω modelHomE6.range ⊓ TwistedDiag.thetaFixed Fr := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero Ω ℓ, zero_pow (by omega)]
  obtain ⟨hfinR, -, -, -, hRnum⟩ := cgrp_facts hf K hK σ hσ h3 Ω Fr hFr
  haveI : Finite (TwistedDiag.Rgrp Ω Fr) := hfinR
  let φ : TwistedDiag.thetaFixed Fr → TwistedDiag.Rgrp Ω Fr := fun x =>
    ⟨g * (x : ModGL Tag.E6 Ω) * g⁻¹,
      (mem_thetaFixed_iff_conj Fr hg hgn (x : ModGL Tag.E6 Ω)).1 x.2⟩
  let ψ : TwistedDiag.Rgrp Ω Fr → TwistedDiag.thetaFixed Fr := fun y =>
    ⟨g⁻¹ * (y : ModGL Tag.E6 Ω) * g,
      (mem_thetaFixed_iff_conj Fr hg hgn _).2 (by
        rw [show g * (g⁻¹ * (y : ModGL Tag.E6 Ω) * g) * g⁻¹ = (y : ModGL Tag.E6 Ω) by
          group]
        exact y.2)⟩
  have hleft : Function.LeftInverse ψ φ := fun x =>
    Subtype.ext (by simp only [φ, ψ]; group)
  have hright : Function.RightInverse ψ φ := fun y =>
    Subtype.ext (by simp only [φ, ψ]; group)
  let e : TwistedDiag.thetaFixed Fr ≃ TwistedDiag.Rgrp Ω Fr :=
    { toFun := φ, invFun := ψ, left_inv := hleft, right_inv := hright }
  have hThetaCard : Nat.card (TwistedDiag.thetaFixed Fr) = numTwistedE6 (ℓ ^ f) := by
    rw [Nat.card_congr e, hRnum]
  have hFinTheta : Finite (TwistedDiag.thetaFixed Fr) :=
    Finite.of_injective e e.injective
  let N : Subgroup (ModGL Tag.E6 Ω) := monomialSubgroup Tag.E6 Ω ⊓ TwistedDiag.thetaFixed Fr
  have hNleTheta : N ≤ TwistedDiag.thetaFixed Fr := inf_le_right
  have hNleMono : N ≤ monoHat Tag.E6 Ω := inf_le_left.trans monomial_le_monoHat
  have hNcard : Nat.card N = (ℓ ^ f + 1) ^ 6 * 51840 :=
    card_monomial_thetaFixed Fr hFr hq0
  have hNidx : ¬ 3 ∣ N.relIndex (TwistedDiag.thetaFixed Fr) := by
    refine CFSG.HardMathSupport.Lang.E6Descent.three_not_dvd_of_mul_eq_twisted (ℓ ^ f) _
      hq2 h3 ?_
    have h := Subgroup.relIndex_mul_card N (TwistedDiag.thetaFixed Fr)
    rw [inf_of_le_left hNleTheta, hNcard, hThetaCard] at h
    exact h
  let S : Subgroup (WeylGroup Tag.E6) := modelHomE6.range
  let P : Subgroup (ModGL Tag.E6 Ω) := xHat Tag.E6 Ω S ⊓ N
  have hSidx : S.index = 640 := by
    have h := Subgroup.card_mul_index S
    rw [show Nat.card S = 81 from card_range_modelHomE6, card_weylGroup_E6] at h
    omega
  let ψN : N →* WeylGroup Tag.E6 := (psiHat Tag.E6 Ω).comp (Subgroup.inclusion hNleMono)
  have hψN : Function.Surjective ψN := by
    intro w
    obtain ⟨m, hm, hmw⟩ := exists_lift Fr hFr w
    refine ⟨⟨m, hm⟩, ?_⟩
    show psiHat Tag.E6 Ω (Subgroup.inclusion hNleMono ⟨m, hm⟩) = w
    have hsub : (Subgroup.inclusion hNleMono ⟨m, hm⟩ : monoHat Tag.E6 Ω) =
        (⟨m, monomial_le_monoHat hm.1⟩ : monoHat Tag.E6 Ω) := Subtype.ext rfl
    rw [hsub]
    exact psiHat_eq hmw
  have hPsub : P.subgroupOf N = S.comap ψN := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨hxm, hxS⟩ := mem_xHat.mp hx.1
      have hsub : (Subgroup.inclusion hNleMono x : monoHat Tag.E6 Ω) =
          ⟨(x : ModGL Tag.E6 Ω), hxm⟩ := Subtype.ext rfl
      show psiHat Tag.E6 Ω (Subgroup.inclusion hNleMono x) ∈ S
      rw [hsub]
      exact hxS
    · intro hxS
      have hxS' : psiHat Tag.E6 Ω (Subgroup.inclusion hNleMono x) ∈ S := hxS
      have hsub : (Subgroup.inclusion hNleMono x : monoHat Tag.E6 Ω) =
          ⟨(x : ModGL Tag.E6 Ω), hNleMono x.2⟩ := Subtype.ext rfl
      rw [hsub] at hxS'
      exact ⟨mem_xHat.mpr ⟨hNleMono x.2, hxS'⟩, x.2⟩
  have hPN : P.relIndex N = 640 := by
    change (P.subgroupOf N).index = 640
    rw [hPsub, Subgroup.index_comap_of_surjective S hψN, hSidx]
  have hPidx : ¬ 3 ∣ P.relIndex (TwistedDiag.thetaFixed Fr) := by
    rw [← Subgroup.relIndex_mul_relIndex P N (TwistedDiag.thetaFixed Fr)
      (inf_le_right : P ≤ N) hNleTheta, hPN]
    intro hdvd
    rcases (Nat.prime_three.dvd_mul).mp hdvd with h | h
    · norm_num at h
    · exact hNidx h
  let Y : Subgroup (ModGL Tag.E6 Ω) := X.map (MulAut.conj g⁻¹).toMonoidHom
  have hYle : Y ≤ TwistedDiag.thetaFixed Fr := by
    rintro _ ⟨x, hx, rfl⟩
    refine (mem_thetaFixed_iff_conj Fr hg hgn (g⁻¹ * x * g)).2 ?_
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hXR hx
  have hYp : IsPGroup 3 Y := hX.map (MulAut.conj g⁻¹).toMonoidHom
  have hEp : IsPGroup 3 (Y.subgroupOf (TwistedDiag.thetaFixed Fr)) :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYle).symm
  obtain ⟨k', hk'⟩ :=
    TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hPidx hEp
  refine ⟨(k' : ModGL Tag.E6 Ω), k'.2, 1, one_mem _, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hyTheta : g⁻¹ * x * g ∈ TwistedDiag.thetaFixed Fr := hYle ⟨x, hx, rfl⟩
  have hyY : (⟨g⁻¹ * x * g, hyTheta⟩ : TwistedDiag.thetaFixed Fr) ∈
      Y.subgroupOf (TwistedDiag.thetaFixed Fr) := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x, hx, rfl⟩
  have hmapmem : (MulAut.conj k').toMonoidHom
      (⟨g⁻¹ * x * g, hyTheta⟩ : TwistedDiag.thetaFixed Fr) ∈
      (Y.subgroupOf (TwistedDiag.thetaFixed Fr)).map (MulAut.conj k').toMonoidHom :=
    ⟨_, hyY, rfl⟩
  have hmem := hk' hmapmem
  have hmemP : (k' : ModGL Tag.E6 Ω) * (g⁻¹ * x * g) * (k' : ModGL Tag.E6 Ω)⁻¹ ∈ P := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    simpa using h
  rw [mul_one]
  have hgoal : ((k' : ModGL Tag.E6 Ω) * g⁻¹) * x * ((k' : ModGL Tag.E6 Ω) * g⁻¹)⁻¹ =
      (k' : ModGL Tag.E6 Ω) * (g⁻¹ * x * g) * (k' : ModGL Tag.E6 Ω)⁻¹ := by group
  change (MulAut.conj ((k' : ModGL Tag.E6 Ω) * g⁻¹)) x ∈
    xHat Tag.E6 Ω modelHomE6.range ⊓ TwistedDiag.thetaFixed Fr
  rw [MulAut.conj_apply, hgoal]
  exact ⟨hmemP.1, hNleTheta hmemP.2⟩

end Sylow

section Weyl


theorem torus_or_cyclic {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL Tag.E6 Ω)} (hE : IsElemAbelian 3 E)
    (hEX : E ≤ xHat Tag.E6 Ω modelHomE6.range) (hc : 3 ^ 5 ≤ Nat.card E) :
    (∀ e ∈ E, ∃ v, e = rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v)) ∨
      ∃ i, E ≤ xHat Tag.E6 Ω (Subgroup.zpowers (gE6 i)) := by
  classical
  have hEM : E ≤ monoHat Tag.E6 Ω := hEX.trans (xHat_le_monoHat _)
  let ψE : E →* WeylGroup Tag.E6 := (psiHat Tag.E6 Ω).comp (Subgroup.inclusion hEM)
  let B : Subgroup (WeylGroup Tag.E6) := ψE.range
  have hBS : B ≤ modelHomE6.range := by
    rintro b ⟨e, rfl⟩
    obtain ⟨hx, hS⟩ := mem_xHat.mp (hEX e.2)
    have hsub : (⟨(e : ModGL Tag.E6 Ω), hEM e.2⟩ : monoHat Tag.E6 Ω) =
        ⟨(e : ModGL Tag.E6 Ω), hx⟩ := Subtype.ext rfl
    show psiHat Tag.E6 Ω ⟨(e : ModGL Tag.E6 Ω), hEM e.2⟩ ∈ modelHomE6.range
    rw [hsub]
    exact hS
  have hBea : IsElemAbelian 3 B :=
    isElemAbelian_range (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ψE
  by_cases hB : B = ⊥
  · left
    intro e he
    have hmemB : ψE ⟨e, he⟩ ∈ B := ⟨⟨e, he⟩, rfl⟩
    rw [hB] at hmemB
    have hpsi : psiHat Tag.E6 Ω ⟨(e : ModGL Tag.E6 Ω), hEM he⟩ = 1 := by
      have hmem' : psiHat Tag.E6 Ω (Subgroup.inclusion hEM ⟨e, he⟩) = 1 :=
        Subgroup.mem_bot.mp hmemB
      have hsub : (Subgroup.inclusion hEM ⟨e, he⟩ : monoHat Tag.E6 Ω) =
          ⟨(e : ModGL Tag.E6 Ω), hEM he⟩ := Subtype.ext rfl
      rw [hsub] at hmem'
      exact hmem'
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hpsi
    have hb3 : b ^ 3 = 1 := by
      have h1 : rootDiagUnit Tag.E6 (b ^ 3) = 1 := by
        rw [← rootDiagUnit_pow, ← hb]
        exact hE.2 e he
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨v, hv⟩ := exists_zetaVec_eq (p := 3) hζo hζ hb3
    exact ⟨v, by rw [show e = rootDiagUnit Tag.E6 b from hb, hv]⟩
  · rcases refined_E6 B hBS hBea hB with hlt | ⟨i, hi⟩
    · exfalso
      have hex : ∀ k : ψE.ker, ∃ x : Fin Tag.E6.rank → ZMod 3,
          (∀ b' ∈ B, adAct Tag.E6 3 b' x = x) ∧
            ((k : E) : ModGL Tag.E6 Ω) = rootDiagUnit Tag.E6 (zetaVec ζ hζ x) := by
        intro k
        have hpsi : psiHat Tag.E6 Ω
            ⟨((k : E) : ModGL Tag.E6 Ω), hEM (k : E).2⟩ = 1 := MonoidHom.mem_ker.mp k.2
        obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hpsi
        have hb3 : b ^ 3 = 1 := by
          have h1 : rootDiagUnit Tag.E6 (b ^ 3) = 1 := by
            rw [← rootDiagUnit_pow, ← hb]
            exact hE.2 (k : E) (k : E).2
          exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
        obtain ⟨x, hx⟩ := exists_zetaVec_eq (p := 3) hζo hζ hb3
        refine ⟨x, ?_, ?_⟩
        · intro b' hb'
          obtain ⟨e, rfl⟩ := hb'
          have hcomm' : (e : ModGL Tag.E6 Ω) * ((k : E) : ModGL Tag.E6 Ω) =
              ((k : E) : ModGL Tag.E6 Ω) * (e : ModGL Tag.E6 Ω) :=
            TableB.IsElemAbelian.comm hE e.2 (k : E).2
          have hcalc : rootDiagUnit Tag.E6
              (zetaVec ζ hζ (adAct Tag.E6 3 (ψE e) x)) =
                rootDiagUnit Tag.E6 (zetaVec ζ hζ x) := by
            rw [← weylTuple_zetaVec]
            have hc := conj_rootDiagUnit_of_mem_monoHat
              (x := (⟨((e : E) : ModGL Tag.E6 Ω), hEM e.2⟩ : monoHat Tag.E6 Ω))
              (zetaVec ζ hζ x)
            rw [show psiHat Tag.E6 Ω
              (⟨((e : E) : ModGL Tag.E6 Ω), hEM e.2⟩ : monoHat Tag.E6 Ω) = ψE e from rfl] at hc
            rw [← hc]
            rw [show rootDiagUnit Tag.E6 (zetaVec ζ hζ x) =
              ((k : E) : ModGL Tag.E6 Ω) by rw [hx, ← hb]]
            calc (e : ModGL Tag.E6 Ω) * ((k : E) : ModGL Tag.E6 Ω) *
                  (e : ModGL Tag.E6 Ω)⁻¹ =
                ((k : E) : ModGL Tag.E6 Ω) * (e : ModGL Tag.E6 Ω) *
                  (e : ModGL Tag.E6 Ω)⁻¹ := by rw [hcomm']
              _ = ((k : E) : ModGL Tag.E6 Ω) := by rw [mul_inv_cancel_right]
          exact zetaVec_injective hζo hζ (rootDiagUnit_injective hcalc)
        · rw [hb, hx]
      let Φ : ψE.ker → {x : Fin Tag.E6.rank → ZMod 3 //
          ∀ b' ∈ B, adAct Tag.E6 3 b' x = x} :=
        fun k => ⟨(hex k).choose, (hex k).choose_spec.1⟩
      have hΦ : Function.Injective Φ := by
        intro k₁ k₂ h
        have hx : (hex k₁).choose = (hex k₂).choose := by
          simpa [Φ] using congrArg Subtype.val h
        apply Subtype.ext
        apply Subtype.ext
        rw [(hex k₁).choose_spec.2, (hex k₂).choose_spec.2, hx]
      have hcardker : Nat.card ψE.ker ≤ Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          ∀ b' ∈ B, adAct Tag.E6 3 b' x = x} :=
        Nat.card_le_card_of_injective Φ hΦ
      have hEcard := Subgroup.card_ker_mul_card_range ψE
      have hle : Nat.card E ≤ Nat.card B * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          ∀ b' ∈ B, adAct Tag.E6 3 b' x = x} := by
        rw [← hEcard]
        calc Nat.card ψE.ker * Nat.card B ≤
              Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
                ∀ b' ∈ B, adAct Tag.E6 3 b' x = x} * Nat.card B :=
              Nat.mul_le_mul_right _ hcardker
          _ = Nat.card B * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
                ∀ b' ∈ B, adAct Tag.E6 3 b' x = x} := Nat.mul_comm _ _
      exact absurd hc (not_le.mpr (lt_of_le_of_lt hle hlt))
    · right
      refine ⟨i, ?_⟩
      intro e he
      rw [mem_xHat]
      refine ⟨hEM he, ?_⟩
      have hmem : ψE ⟨e, he⟩ ∈ B := ⟨⟨e, he⟩, rfl⟩
      rw [hi] at hmem
      have hmem' : psiHat Tag.E6 Ω (Subgroup.inclusion hEM ⟨e, he⟩) ∈
          Subgroup.zpowers (gE6 i) := hmem
      have hsub : (Subgroup.inclusion hEM ⟨e, he⟩ : monoHat Tag.E6 Ω) =
          ⟨(e : ModGL Tag.E6 Ω), hEM he⟩ := Subtype.ext rfl
      rw [hsub] at hmem'
      exact hmem'

end Weyl

end CFSG.StandardType.NoOffTwE6Three
