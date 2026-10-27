module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParO8Core
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParO8Geom
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8Model
import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.Sec18.SylowWStar
public import CFSG.RankThree.PartTwo.Sec19.Item194Five
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.Item203OneProof
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartTwo.Sec19 (IsProperParabolic)
open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.Open (StatedOmega StatedQuadMinus StatedProj)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivProjImage)
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

local notation "𝔽₂" => GaloisField 2 1

theorem kfO8_model (b c : 𝔽₂) (hbc : ∀ s : 𝔽₂, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (↥(projOmegaMinus 3 𝔽₂ b c) ≃* ↥kfO8G0) ∧
      IsSimpleGroup ↥(projOmegaMinus 3 𝔽₂ b c) := by
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible_gf2 hbc
  have hP : CFSG.PGLModel.projImage (StatedOmega (StatedQuadMinus 4 𝔽₂ 1 1)) =
      projOmegaMinus 3 𝔽₂ 1 1 := CFSG.PGLModel.projImage_statedOmegaMinus 4 𝔽₂ 1 1
  let e1 : ↥(projOmegaMinus 3 𝔽₂ 1 1) ≃* StatedProj (StatedOmega (StatedQuadMinus 4 𝔽₂ 1 1)) :=
    (statedProjEquivProjImage _ hP).symm
  let e2 := statedProjEquivSelf (StatedOmega (StatedQuadMinus 4 𝔽₂ 1 1))
  let e3 : ↥(StatedOmega (StatedQuadMinus 4 𝔽₂ 1 1)) ≃* ↥kfO8G0 :=
    tailOmegaEquiv (minusTailIsometry 4 𝔽₂ 1 1) (coe_quadMinus 4 𝔽₂ 1 1)
      (commutator_orthogonalGroup_quadMinus (by norm_num) kfO8_hirr)
  refine ⟨⟨(e1.trans e2).trans e3⟩, ?_⟩
  haveI := isSimpleGroup_statedProj_statedOmega_quadMinus (n := 4) (b := (1 : 𝔽₂)) (c := 1)
    (by norm_num) kfO8_hirr
  exact MulEquiv.isSimpleGroup e1

private theorem kfParO8_notFive_oTwoP (H : Type) [Group H] [Finite H] :
    ¬ 5 ∣ Nat.card (Sec4.oTwoP 3 H) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hy3 : (QuotientGroup.mk' (CFSG.pCore 2 H)) (y : H) ∈ CFSG.pCore 3 (H ⧸ CFSG.pCore 2 H) :=
    y.2
  have hy5 : (y : H) ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hw1 : (QuotientGroup.mk' (CFSG.pCore 2 H)) (y : H) = 1 := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := H ⧸ CFSG.pCore 2 H)) ⟨_, hy3⟩
    have hk' : ((QuotientGroup.mk' (CFSG.pCore 2 H)) (y : H)) ^ 3 ^ k = 1 :=
      congrArg Subtype.val hk
    have h5' : ((QuotientGroup.mk' (CFSG.pCore 2 H)) (y : H)) ^ 5 = 1 := by
      rw [← map_pow, hy5, map_one]
    have hcop : Nat.Coprime (3 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
      (orderOf_dvd_of_pow_eq_one h5'))
  have hyK : (y : H) ∈ CFSG.pCore 2 H := (QuotientGroup.eq_one_iff (y : H)).1 hw1
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨_, hyK⟩
  have hj' : (y : H) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hdvd : orderOf (y : H) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  rw [Subgroup.orderOf_coe, hy] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
  omega

private theorem kfParO8_sylow_top {X : Type} [Group X] [Finite X] (T : Sylow 2 X) :
    IsSylowOf 2 (T : Subgroup X) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨le_top, T.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T.not_dvd_index⟩

private theorem kfParO8_conj_eq_one {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h2 : 2 ^ 12 ∣ Nat.card X) (x : X) (hx : MulAut.conj x = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxc : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := DFunLike.congr_fun hx g
    rw [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · rwa [h, Subgroup.mem_bot] at hxc
  · exfalso
    have hdvd : 2 ∣ Nat.card X := (Dvd.intro_left _ (by norm_num : 2 ^ 12 = 2 * 2 ^ 11)).trans h2
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    haveI : (Subgroup.zpowers y).Normal := ⟨fun n hn g => by
      have hc := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top n) g
      rwa [hc, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with h' | h'
    · have : y = 1 := by
        have := Subgroup.mem_zpowers y
        rwa [h', Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hy
      omega
    · have hc : Nat.card X = 2 := by
        rw [← hy, ← Nat.card_zpowers, h', Subgroup.card_top]
      rw [hc] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega

private theorem kfParO8_notNonempty_alt {X : Type} [Group X] [Finite X]
    (h2 : 2 ^ 12 ∣ Nat.card X) : ¬ Nonempty (X ≃* alternatingGroup (Fin 10)) := by
  rintro ⟨e⟩
  have : Nat.card X = 1814400 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [this] at h2
  omega

theorem kfParO8_of_data {X : Type} [Group X] [Finite X] (hd : KFParO8Data X)
    (hc : ∀ x : X, MulAut.conj x = 1 → x = 1)
    (hA : ¬ Nonempty (X ≃* alternatingGroup (Fin 10))) : NoSquareInvertingInParabolic X := by
  intro P D hP hDH hD3 hD9 hDO t htP htN hinv
  have hprop : IsProperParabolic P := by
    rcases hP with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact (hA h).elim
  obtain ⟨-, T, hTN⟩ := hprop
  set ψ : X →* MulAut X := MulAut.conj with hψdef
  have hψ : Function.Injective ψ := (injective_iff_map_eq_one ψ).2 hc
  set H : Subgroup (MulAut X) := P.map ψ with hH
  set Yh : Subgroup (MulAut X) := (Sec4.oTwoP 3 ↥H).map H.subtype with hYh
  have hYhH : Yh ≤ H := Subgroup.map_subtype_le _
  have hHrange : H ≤ ψ.range := by rintro _ ⟨p, hp, rfl⟩; exact ⟨p, rfl⟩
  haveI hOn : (Sec4.oTwoP 3 ↥H).Normal := by
    unfold Sec4.oTwoP
    infer_instance
  have hYhN : ∀ h ∈ H, ∀ z ∈ Yh, h * z * h⁻¹ ∈ Yh := by
    intro h hh z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨⟨h, hh⟩ * z' * ⟨h, hh⟩⁻¹, hOn.conj_mem z' hz' ⟨h, hh⟩, by simp⟩
  set E : Subgroup X := D.comap ψ with hE
  set Y : Subgroup X := Yh.comap ψ with hY
  have hEY : E ≤ Y := fun e he => hDO he
  have hYP : Y ≤ P := by
    intro y hy
    obtain ⟨p, hp, hpe⟩ := hYhH (Subgroup.mem_comap.1 hy)
    rwa [← hψ hpe]
  have hYn : ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y := by
    intro p hp y hy
    rw [Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact hYhN (ψ p) ⟨p, hp, rfl⟩ _ hy
  have hmapY : Y.map ψ = Yh := by
    rw [hY, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (hYhH.trans hHrange)
  have hY5 : ¬ 5 ∣ Nat.card Y := by
    rw [← Subgroup.card_map_of_injective hψ, hmapY, hYh,
      Subgroup.card_map_of_injective H.subtype_injective]
    exact kfParO8_notFive_oTwoP _
  have hmapE : E.map ψ = D := by
    rw [hE, Subgroup.map_comap_eq]
    exact inf_eq_right.2 (hDH.trans hHrange)
  have hE9 : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hψ, hmapE]
    exact hD9
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    apply hψ
    rw [map_pow, map_one]
    exact hD3.2 _ he
  obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 htP
  have htN' : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    rw [Subgroup.mem_comap] at he ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 htN _).1 he
  have hinv' : ∀ e ∈ E, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹ := by
    intro e he
    apply hψ
    have := hinv (ψ e) he
    simpa [map_mul, map_inv, map_pow] using this
  exact kfParO8_core hd ⟨T, kfParO8_sylow_top T, hTN⟩ hYP hYn hY5 hEY hE3 hE9 hyP htN' hinv'

theorem kfPar_O8m {X : Type} [Group X] [Finite X]
    (hX : ∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) :
    NoSquareInvertingInParabolic X := by
  obtain ⟨b, c, hbc, ⟨e₁⟩⟩ := hX
  obtain ⟨⟨e₂⟩, hsimple⟩ := kfO8_model b c hbc
  let e : X ≃* ↥kfO8G0 := e₁.trans e₂
  haveI : IsSimpleGroup X := MulEquiv.isSimpleGroup e₁
  have h2 : 2 ^ 12 ∣ Nat.card X := by
    rw [Nat.card_congr e.toEquiv]
    exact kfO8_two_pow_dvd
  exact kfParO8_of_data (KFParO8Data.of_mulEquiv e kfO8_data) (kfParO8_conj_eq_one h2)
    (kfParO8_notNonempty_alt h2)

end CFSG.RankThree.PartTwo.Late
