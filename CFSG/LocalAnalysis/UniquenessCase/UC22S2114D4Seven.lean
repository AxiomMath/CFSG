module

public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4Syl
import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
import CFSG.LieType.Chevalley.GraphFixedRankOneImage
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
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
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
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
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.D4Seven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.Sec53F.TriD4 (d4_sylow d4_H_le d4_B_eq d4_U_inf_H d4_H_comm)

local notation "𝕩" => xPar (rootOperatorFamily d4)

variable {K : Type} [Field K]

@[expose] def longIdx : Finset ℕ := {2, 8, 19, 21, 22, 23}

theorem lt_of_mem_longIdx {k : ℕ} (hk : k ∈ longIdx) :
    k < (Tag.rootCertificate d4).roots.length := by
  simp only [longIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rho_d4Root_of_mem_longIdx {k : ℕ} (hk : k ∈ longIdx) : rho (d4Root k) = d4Root k := by
  simp only [longIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem outer_eq_of_rho_eq {γ : Fin d4.rank → ℤ} (hγ : rho γ = γ) :
    γ (nd 1) = γ (nd 0) ∧ γ (nd 3) = γ (nd 0) := by
  have hr : ∀ j, rho γ j = γ (rhoPerm.symm j) := fun j => rfl
  have h0 : rhoPerm.symm (nd 0) = nd 3 := by decide
  have h1 : rhoPerm.symm (nd 1) = nd 0 := by decide
  have e0 := congrFun hγ (nd 0)
  have e1 := congrFun hγ (nd 1)
  rw [hr, h0] at e0
  rw [hr, h1] at e1
  exact ⟨e1.symm, e0⟩

theorem prod_d4 {M : Type*} [CommMonoid M] (f : Fin d4.rank → M) :
    ∏ j, f j = f (nd 0) * f (nd 1) * f (nd 2) * f (nd 3) :=
  Fin.prod_univ_four f

theorem rootChar_eq_one_of_rho_eq (a₀ a₁ a₃ : Kˣ) (hN : a₀ * a₁ * a₃ = 1)
    {γ : Fin d4.rank → ℤ} (hγ : rho γ = γ) :
    rootChar (d4Tuple (a₀ ^ 2) (a₁ ^ 2) 1 (a₃ ^ 2)) γ = 1 := by
  obtain ⟨h1, h3⟩ := outer_eq_of_rho_eq hγ
  rw [rootChar, prod_d4]
  change (a₀ ^ 2) ^ γ (nd 0) * (a₁ ^ 2) ^ γ (nd 1) * 1 ^ γ (nd 2) * (a₃ ^ 2) ^ γ (nd 3) = 1
  rw [h1, h3, one_zpow, mul_one, ← mul_zpow, ← mul_zpow, ← mul_pow, ← mul_pow, hN, one_pow,
    one_zpow]

theorem orderOf_uSL_mul_vSL {F : Type} [Field F] (h2 : (2 : F) = 0) :
    orderOf (uSL (1 : F) * vSL 1) = 3 := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hA : ((uSL (1 : F) * vSL 1 : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change !![(1 : F), 1; 0, 1] * !![(1 : F), 0; 1, 1] = _
    rw [Matrix.mul_fin_two]
    simp [h11]
  have hA3 : (uSL (1 : F) * vSL 1) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hA, Matrix.SpecialLinearGroup.coe_one, pow_succ,
      pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [h11]
  have hA1 : uSL (1 : F) * vSL 1 ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp only [hA, Matrix.SpecialLinearGroup.coe_one] at h01
    simp at h01
  exact orderOf_eq_prime hA3 hA1

theorem not_seven_dvd_two_pow_sub_one {f : ℕ} (hf : IsPowTwo f) : ¬ 7 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have hm := uc22s2114_two_pow_two_pow_mod k
  have h1 : 1 ≤ 2 ^ 2 ^ k := Nat.one_le_two_pow
  omega

private theorem isSylowTwoOf_map_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hU.2.1.map _, ?_⟩
  have h := hU.2.2
  rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
  rw [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective e.bijective]
  exact h

section TorusUnits

variable (σ : K ≃+* K)

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

theorem sigmaU_eq_pow {q : ℕ} (hσ : ∀ c, σ c = c ^ q) (a : Kˣ) : σu a = a ^ q :=
  Units.ext (by simp [hσ])

theorem torus_seven {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = q) (h7 : ¬ 7 ∣ q - 1)
    (h7' : 7 ∣ q ^ 2 + q + 1) {a : Kˣ} {b : (trialityFixedField K σ.toRingHom)ˣ}
    (ha : a ^ 7 = 1) (hb : b ^ 7 = 1) : b = 1 ∧ a * σu a * σu (σu a) = 1 := by
  refine ⟨?_, ?_⟩
  · have h1 : orderOf b ∣ 7 := orderOf_dvd_of_pow_eq_one hb
    have h2 : orderOf b ∣ q - 1 := by
      rw [← hk, ← Nat.card_units]
      exact orderOf_dvd_natCard b
    have hcop : Nat.Coprime 7 (q - 1) := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  · rw [sigmaU_eq_pow σ hσ, sigmaU_eq_pow σ hσ, ← pow_mul, ← pow_succ', ← pow_add]
    obtain ⟨m, hm⟩ := h7'
    rw [show q + 1 + q * q = q ^ 2 + q + 1 by ring, hm, pow_mul, ha, one_pow]

theorem trialityTorusHom_eq_of_norm (a : Kˣ) (hN : a * σu a * σu (σu a) = 1) :
    trialityTorusHom σ (a, 1) = rootDiagUnit d4 (d4Tuple (a ^ 2) (σu a ^ 2) 1 (σu (σu a) ^ 2)) := by
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, map_one, inv_one, mul_one, mul_one,
    mul_one, one_pow, mul_one, hN, inv_one]

end TorusUnits

section SylowConj

variable [Finite K] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

private theorem exists_conj_of_sylow_two {S₁ S₂ : Subgroup ↥C₀} (h₁ : IsSylowTwoOf S₁ ⊤)
    (h₂ : IsSylowTwoOf S₂ ⊤) : ∃ g : ↥C₀, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hidx : ∀ S : Subgroup ↥C₀, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 ↥C₀ := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 ↥C₀ := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C₀ P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 ↥C₀ => (T : Subgroup ↥C₀)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

end SylowConj

theorem coe_xPar_eq_pinnedX [CharP K 2] {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    ((𝕩 γ c : adjointGroup d4 K) : ModGL d4 K) = pinnedX d4 K γ c := by
  rw [xPar_of_isRoot hγ, RootOperatorFamily.coe_eltElement,
    (rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ c]
  congr 1
  rcases (rootOperatorFamily d4).pinnedFamilySign_eq γ with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem rootDiagUnit_conj_xPar [CharP K 2] (c : Fin d4.rank → Kˣ) {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) (t : K) :
    rootDiagUnit d4 c * ((𝕩 γ t : adjointGroup d4 K) : ModGL d4 K) * (rootDiagUnit d4 c)⁻¹ =
      ((𝕩 γ ((rootChar c γ : Kˣ) * t) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [coe_xPar_eq_pinnedX hγ, coe_xPar_eq_pinnedX hγ]
  exact rootDiagUnit_conj_pinnedX c hγ t

section Torus

variable [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

omit [Finite K]
  in
theorem commute_xPar_of_norm (a : Kˣ) (hN : a * σu a * σu (σu a) = 1) {γ : Fin d4.rank → ℤ}
    (hγr : IsRoot d4 γ) (hγ : rho γ = γ) (t : K) :
    trialityTorusHom σ (a, 1) * ((𝕩 γ t : adjointGroup d4 K) : ModGL d4 K) =
      ((𝕩 γ t : adjointGroup d4 K) : ModGL d4 K) * trialityTorusHom σ (a, 1) := by
  rw [trialityTorusHom_eq_of_norm σ a hN]
  have h := rootDiagUnit_conj_xPar (d4Tuple (a ^ 2) (σu a ^ 2) 1 (σu (σu a) ^ 2)) hγr t
  rw [rootChar_eq_one_of_rho_eq _ _ _ hN hγ, Units.val_one, one_mul] at h
  calc _ = rootDiagUnit d4 (d4Tuple (a ^ 2) (σu a ^ 2) 1 (σu (σu a) ^ 2)) *
        ((𝕩 γ t : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 (d4Tuple (a ^ 2) (σu a ^ 2) 1 (σu (σu a) ^ 2)))⁻¹ *
        rootDiagUnit d4 (d4Tuple (a ^ 2) (σu a ^ 2) 1 (σu (σu a) ^ 2)) := by group
    _ = _ := by rw [h]

end Torus

theorem commutator_xPar_of_repCheck {k₁ k₂ k : ℕ} {C : ℤ}
    (hcheck : RootOps.repCheck d4 k₁ k₂ [(1, 1, k, C)] = true)
    (h₁ : k₁ < (Tag.rootCertificate d4).roots.length)
    (h₂ : k₂ < (Tag.rootCertificate d4).roots.length)
    (h : k < (Tag.rootCertificate d4).roots.length) (s t : K) :
    ⁅𝕩 (d4Root k₁) s, 𝕩 (d4Root k₂) t⁆ = 𝕩 (d4Root k) ((C : K) * s * t) := by
  have key := commutator_eltElement_of_repCheck (τ := d4)
    (RootOps.d4_allValid : RootOps.allValid d4 = true) hcheck h
    (α := ⟨d4Root k₁, isRoot_d4Root h₁⟩) (β := ⟨d4Root k₂, isRoot_d4Root h₂⟩)
    (RootOps.rootPos_eq h₁ rfl) (RootOps.rootPos_eq h₂ rfl) s t
  have hr : RootOps.rootAt d4 k h = ⟨d4Root k, isRoot_d4Root h⟩ := Subtype.ext rfl
  rw [commutatorElement_def, xPar_of_isRoot (isRoot_d4Root h₁),
    xPar_of_isRoot (isRoot_d4Root h₂), xPar_of_isRoot (isRoot_d4Root h), key, hr]

theorem exists_commutator_long [CharP K 2] {k : ℕ} (hk : k ∈ longIdx) (t : K) :
    ∃ k₁ ∈ longIdx, ∃ k₂ ∈ longIdx, 𝕩 (d4Root k) t = ⁅𝕩 (d4Root k₁) t, 𝕩 (d4Root k₂) 1⁆ := by
  have hneg : ∀ s : K, ((-1 : ℤ) : K) * s * 1 = s := fun s => by
    rw [Int.cast_neg, Int.cast_one, neg_one_mul, CharTwo.neg_eq, mul_one]
  have hpos : ∀ s : K, ((1 : ℤ) : K) * s * 1 = s := fun s => by
    rw [Int.cast_one, one_mul, mul_one]
  simp only [longIdx, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨22, by decide, 21, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 22) (k₂ := 21) (k := 2) (C := 1)
      (by decide +kernel) (by decide) (by decide) (by decide), hpos]
  · refine ⟨23, by decide, 19, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 23) (k₂ := 19) (k := 8) (C := -1)
      (by decide +kernel) (by decide) (by decide) (by decide), hneg]
  · refine ⟨22, by decide, 8, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 22) (k₂ := 8) (k := 19) (C := -1)
      (by decide +kernel) (by decide) (by decide) (by decide), hneg]
  · refine ⟨23, by decide, 2, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 23) (k₂ := 2) (k := 21) (C := 1)
      (by decide +kernel) (by decide) (by decide) (by decide), hpos]
  · refine ⟨2, by decide, 19, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 2) (k₂ := 19) (k := 22) (C := 1)
      (by decide +kernel) (by decide) (by decide) (by decide), hpos]
  · refine ⟨8, by decide, 21, by decide, ?_⟩
    rw [commutator_xPar_of_repCheck (k₁ := 8) (k₂ := 21) (k := 23) (C := -1)
      (by decide +kernel) (by decide) (by decide) (by decide), hneg]

section Model

variable [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

omit [CharP K 2] in
theorem xPar_mem_C₀ {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : ℕ} (hk : k ∈ longIdx) {t : K} (ht : σ t = t) :
    ((𝕩 (d4Root k) t : adjointGroup d4 K) : ModGL d4 K) ∈ C₀ := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := sigma_three_of_card hK hσ'
  have hmem := xPar_d4Root_mem_twistedGroup hσ3 (lt_of_mem_longIdx hk)
    (rho_d4Root_of_mem_longIdx hk) ht
  have hC0 : C₀ = (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf K hK σ.toRingHom
      hσ').2.2.1.symm.trans (commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 hK hσ')
  rw [hC0]
  exact ⟨_, hmem, rfl⟩

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

@[expose] noncomputable def longA2 : Subgroup ↥C₀ :=
  Subgroup.closure {x | ∃ k ∈ longIdx, ∃ t : K, σ t = t ∧
    (x : ModGL d4 K) = ((𝕩 (d4Root k) t : adjointGroup d4 K) : ModGL d4 K)}

omit [Finite K]
  in
theorem longA2_le_centralizer (a : Kˣ) (hN : a * σu a * σu (σu a) = 1) {h : ↥C₀}
    (hh : (h : ModGL d4 K) = trialityTorusHom σ (a, 1)) :
    longA2 σ ≤ Subgroup.centralizer {h} := by
  rw [longA2, Subgroup.closure_le]
  rintro x ⟨k, hk, t, -, hx⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hh, hx]
  exact (commute_xPar_of_norm σ a hN (isRoot_d4Root (lt_of_mem_longIdx hk))
    (rho_d4Root_of_mem_longIdx hk) t).symm

theorem longA2_perfect {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : ⁅longA2 σ, longA2 σ⁆ = longA2 σ := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  conv_lhs => rw [longA2]
  rw [Subgroup.closure_le]
  rintro x ⟨k, hk, t, ht, hx⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := exists_commutator_long hk t
  let y : ↥C₀ := ⟨_, xPar_mem_C₀ σ hf hK hσ hk₁ ht⟩
  let z : ↥C₀ := ⟨_, xPar_mem_C₀ σ hf hK hσ hk₂ (map_one σ)⟩
  have hy : y ∈ longA2 σ := Subgroup.subset_closure ⟨k₁, hk₁, t, ht, rfl⟩
  have hz : z ∈ longA2 σ := Subgroup.subset_closure ⟨k₂, hk₂, 1, map_one σ, rfl⟩
  have hxyz : x = ⁅y, z⁆ := by
    apply Subtype.ext
    rw [hx, he]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, y, z]
  rw [SetLike.mem_coe, hxyz]
  exact Subgroup.commutator_mem_commutator hy hz

theorem two_dvd_card_longA2 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : 2 ∣ Nat.card (longA2 σ) := by
  have hk : (2 : ℕ) ∈ longIdx := by decide
  let y : ↥C₀ := ⟨_, xPar_mem_C₀ σ hf hK hσ hk (map_one σ)⟩
  have hy : y ∈ longA2 σ := Subgroup.subset_closure ⟨2, hk, 1, map_one σ, rfl⟩
  have hroot := isRoot_d4Root (lt_of_mem_longIdx hk)
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
    change ((𝕩 (d4Root 2) 1 * 𝕩 (d4Root 2) 1 : adjointGroup d4 K) : ModGL d4 K) = 1
    rw [← xPar_add, CharTwo.add_self_eq_zero, xPar_zero]
    rfl
  have hy1 : y ≠ 1 := by
    intro h
    have h' := congrArg (fun w : ↥C₀ => (w : ModGL d4 K)) h
    simp only [Subgroup.coe_one, y] at h'
    have h'' : 𝕩 (d4Root 2) (1 : K) = 𝕩 (d4Root 2) 0 := by
      rw [xPar_zero]
      exact Subtype.ext h'
    exact one_ne_zero (xPar_injective hroot h'')
  have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard _ hy

theorem exists_orderOf_three_longA2 (hσ3 : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ z ∈ longA2 σ, orderOf z = 3 := by
  have hk2 : (2 : ℕ) ∈ longIdx := by decide
  have hk8 : (8 : ℕ) ∈ longIdx := by decide
  let y : ↥C₀ := ⟨_, xPar_mem_C₀ σ hf hK hσ hk2 (map_one σ)⟩
  let w : ↥C₀ := ⟨_, xPar_mem_C₀ σ hf hK hσ hk8 (map_one σ)⟩
  have hy : y ∈ longA2 σ := Subgroup.subset_closure ⟨2, hk2, 1, map_one σ, rfl⟩
  have hw : w ∈ longA2 σ := Subgroup.subset_closure ⟨8, hk8, 1, map_one σ, rfl⟩
  refine ⟨y * w, mul_mem hy hw, ?_⟩
  set a₁ : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩
  have hcard : (TwistTag.D4.orbit a₁).card = 1 := by decide
  have hmin : TwistTag.D4.orbitMin a₁ = nd 2 := Fin.ext (D4_orbitMin_of_card_eq_one hcard)
  set φ := orbitRankOneHom TwistTag.D4 K σ.toRingHom a₁
  have hφ : Function.Injective φ := orbitRankOneHom_injective_D4 hσ3 a₁
  have h2 : (2 : orbitField TwistTag.D4 K σ.toRingHom a₁) = 0 :=
    Subtype.ext (by simp [CharTwo.two_eq_zero])
  have hd2 : d4Root 2 = Pi.single (nd 2) 1 := by decide
  have hd8 : d4Root 8 = -Pi.single (nd 2) 1 := by decide
  have hY : (orbitY TwistTag.D4 K σ.toRingHom a₁ 1 : ModGL TwistTag.D4.tag K) =
      yUnit TwistTag.D4.tag K (TwistTag.D4.orbitMin a₁) 1 := by
    rw [coe_orbitY, hcard]
    simp
  have hyw : ((y * w : ↥C₀) : ModGL d4 K) = φ (uSL 1 * vSL 1) := by
    rw [map_mul, orbitRankOneHom_uSL, orbitRankOneHom_vSL, coe_orbitX_of_card_eq_one hcard, hY,
      hmin, Subgroup.coe_mul]
    change ((𝕩 (d4Root 2) 1 : adjointGroup d4 K) : ModGL d4 K) *
        ((𝕩 (d4Root 8) 1 : adjointGroup d4 K) : ModGL d4 K) = _
    rw [coe_xPar_eq_pinnedX (isRoot_d4Root (lt_of_mem_longIdx hk2)),
      coe_xPar_eq_pinnedX (isRoot_d4Root (lt_of_mem_longIdx hk8)), hd2, hd8, pinnedX_single,
      pinnedX_neg_single]
    rfl
  rw [← orderOf_injective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      Subtype.val_injective (y * w)]
  change orderOf ((y * w : ↥C₀) : ModGL d4 K) = 3
  rw [hyw, orderOf_injective φ hφ, orderOf_uSL_mul_vSL h2]

local notation "𝒰" => Subgroup.subgroupOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) C₀
local notation "ℋ" => Subgroup.subgroupOf (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) C₀

theorem exists_conj_mem_torus {y : ↥C₀} (hy : orderOf y = 7) {P : Subgroup ↥C₀}
    (hP : IsSylowTwoOf P ⊤) (hyP : y ∈ Subgroup.normalizer (P : Set ↥C₀)) :
    ∃ g : ↥C₀, g⁻¹ * y * g ∈ ℋ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨g₁, hg₁⟩ := exists_conj_of_sylow_two σ (d4_sylow σ) hP
  set B : Subgroup ↥C₀ := Subgroup.normalizer ((𝒰 : Subgroup ↥C₀) : Set ↥C₀) with hBdef
  have hy₁ : g₁⁻¹ * y * g₁ ∈ B := by
    rw [hBdef, Subgroup.mem_normalizer_iff]
    intro u
    rw [← hg₁] at hyP
    have hyP' := Subgroup.mem_normalizer_iff.mp hyP (g₁ * u * g₁⁻¹)
    have e : ∀ v : ↥C₀, v ∈ (𝒰 : Subgroup ↥C₀).map (MulAut.conj g₁).toMonoidHom ↔
        g₁⁻¹ * v * g₁ ∈ (𝒰 : Subgroup ↥C₀) := by
      intro v
      constructor
      · rintro ⟨w, hw, rfl⟩
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        rwa [show g₁⁻¹ * (g₁ * w * g₁⁻¹) * g₁ = w by group]
      · intro hv
        refine ⟨g₁⁻¹ * v * g₁, hv, ?_⟩
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
    rw [e, e] at hyP'
    have e1 : g₁⁻¹ * (g₁ * u * g₁⁻¹) * g₁ = u := by group
    have e2 : g₁⁻¹ * (y * (g₁ * u * g₁⁻¹) * y⁻¹) * g₁ =
        g₁⁻¹ * y * g₁ * u * (g₁⁻¹ * y * g₁)⁻¹ := by group
    rw [e1, e2] at hyP'
    exact hyP'
  have hHB : (ℋ : Subgroup ↥C₀) ≤ B := d4_H_le σ
  have hBeq : B = (𝒰 : Subgroup ↥C₀) ⊔ ℋ := by
    refine le_antisymm (fun g hg => ?_) (sup_le Subgroup.le_normalizer hHB)
    obtain ⟨u, hu, h, hh, rfl⟩ := d4_B_eq σ g hg
    exact Subgroup.mul_mem_sup hu hh
  have hdisj : Disjoint (𝒰 : Subgroup ↥C₀) ℋ := by
    rw [Subgroup.disjoint_def]
    exact fun hx hxH => d4_U_inf_H σ _ hx hxH
  have hcard : Nat.card B = Nat.card (𝒰 : Subgroup ↥C₀) * Nat.card ℋ := by
    rw [hBeq]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hHB hdisj
  have hU2 : IsPGroup 2 (𝒰 : Subgroup ↥C₀) := (d4_sylow σ).2.1
  obtain ⟨a, ha⟩ := hU2.exists_card_eq
  have hrel : (ℋ : Subgroup ↥C₀).relIndex B = 2 ^ a := by
    have h1 := Subgroup.relIndex_mul_card (ℋ : Subgroup ↥C₀) B
    rw [inf_eq_left.2 hHB, hcard, ha] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  obtain ⟨P₇, hP₇⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 (ℋ : Subgroup ↥C₀)
  have hP₇B : CFSG.ABGLocalTools.IsSylowOf 7 P₇ B := by
    obtain ⟨hle, hp, hnd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP₇
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hle.trans hHB, hp, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P₇ ℋ B hle hHB, hrel]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
    · exact hnd h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)) (by norm_num)
  have hz7 : IsPGroup 7 (Subgroup.zpowers (⟨_, hy₁⟩ : ↥B)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    have h := orderOf_injective (MulAut.conj g₁⁻¹).toMonoidHom (MulAut.conj g₁⁻¹).injective y
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] at h
    exact h.trans hy
  obtain ⟨Q', hQ'⟩ := hz7.exists_le_sylow
  have hQ : CFSG.ABGLocalTools.IsSylowOf 7 ((Q' : Subgroup ↥B).map B.subtype) B := ⟨Q', rfl⟩
  have hyQ : g₁⁻¹ * y * g₁ ∈ (Q' : Subgroup ↥B).map B.subtype :=
    ⟨⟨_, hy₁⟩, hQ' (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨k, -, hk⟩ := hP₇B.exists_mem_conj hQ
  refine ⟨g₁ * k, ?_⟩
  have := hP₇.le ((hk _).1 hyQ)
  rwa [show (g₁ * k)⁻¹ * y * (g₁ * k) = k⁻¹ * (g₁⁻¹ * y * g₁) * k by group]

theorem centralizer_of_torus_seven (hσ3 : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f) (h7 : ¬ 7 ∣ 2 ^ f - 1)
    (h7' : 7 ∣ (2 ^ f) ^ 2 + 2 ^ f + 1) {h : ↥C₀} (hhH : h ∈ ℋ) (hh : orderOf h = 7) :
    (∃ S : Subgroup ↥C₀, S ≤ Subgroup.centralizer {h} ∧ ⁅S, S⁆ = S ∧ 2 ∣ Nat.card S) ∧
      (∃ z ∈ Subgroup.centralizer ({h} : Set ↥C₀), orderOf z = 3) ∧
      (3 ∣ 2 ^ f - 1 → ∃ A : Subgroup ↥C₀, A ≤ Subgroup.centralizer {h} ∧
        CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2) := by
  have hT : (h : ModGL d4 K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hhH)).1
  obtain ⟨⟨a, b⟩, hab⟩ := exists_trialityTorusHom_eq hσ3 hT
  have h7p : (a, b) ^ 7 = 1 := by
    apply trialityTorusHom_injective (σ := σ)
    rw [map_pow, hab, map_one, ← Subgroup.coe_pow, ← hh, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨hb1, hN⟩ := torus_seven σ (q := 2 ^ f) hσ hk h7 h7' (congrArg Prod.fst h7p)
    (congrArg Prod.snd h7p)
  subst hb1
  have hcent : longA2 σ ≤ Subgroup.centralizer {h} := longA2_le_centralizer σ a hN hab.symm
  refine ⟨⟨longA2 σ, hcent, longA2_perfect σ hf hK hσ, two_dvd_card_longA2 σ hf hK hσ⟩, ?_, ?_⟩
  · obtain ⟨z, hz, hz3⟩ := exists_orderOf_three_longA2 σ hσ3 hf hK hσ
    exact ⟨z, hcent hz, hz3⟩
  · intro h3
    obtain ⟨A, hAH, hAe, hAc⟩ :=
      uc22s218_d4_model_elemAbelian σ Nat.prime_three hσ3 hK hk h3
    refine ⟨A, fun x hx => ?_, hAe, hAc⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact d4_H_comm σ x (hAH hx) h hhH

end Model

theorem centralizer_seven_of_is3D4 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hY : Is3D4 Y f)
    (hf : IsPowTwo f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {y : Y}
    (hyU : y ∈ Subgroup.normalizer (U : Set Y)) (hy : orderOf y = 7) :
    (∃ S : Subgroup Y, S ≤ Subgroup.centralizer {y} ∧ ⁅S, S⁆ = S ∧ 2 ∣ Nat.card S) ∧
      (∃ z ∈ Subgroup.centralizer ({y} : Set Y), orderOf z = 3) ∧
      (3 ∣ 2 ^ f - 1 → ∃ A : Subgroup Y, A ≤ Subgroup.centralizer {y} ∧
        CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2) := by
  obtain ⟨hf1, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  set y₀ := e y
  have hP := isSylowTwoOf_map_mulEquiv e hU
  have hy₀P : y₀ ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    obtain ⟨u, rfl⟩ := e.surjective x
    have key : ∀ v : Y, e v ∈ U.map e.toMonoidHom ↔ v ∈ U := fun v =>
      ⟨fun ⟨w, hw, hwv⟩ => (e.injective hwv) ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
    rw [show y₀ * e u * y₀⁻¹ = e (y * u * y⁻¹) by rw [map_mul, map_mul, map_inv], key, key]
    exact Subgroup.mem_normalizer_iff.1 hyU u
  have hy₀ : orderOf y₀ = 7 := by rw [MulEquiv.orderOf_eq, hy]
  obtain ⟨g, hg⟩ := exists_conj_mem_torus σ hy₀ hP hy₀P
  have hgo : orderOf (g⁻¹ * y₀ * g) = 7 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y₀
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] at h
    exact h.trans hy₀
  have h7' : 7 ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 := (uc22s2114_seven_factorization hf).1
  obtain ⟨⟨S, hSc, hSp, hS2⟩, ⟨z, hzc, hz3⟩, hA⟩ := centralizer_of_torus_seven σ hσ3 hf1 hK hσ hk
    (not_seven_dvd_two_pow_sub_one hf) h7' hg hgo
  let ψ : Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.trans (MulAut.conj g⁻¹)
  have hψ : ψ y = g⁻¹ * y₀ * g := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hcomm : ∀ x, x ∈ Subgroup.centralizer ({g⁻¹ * y₀ * g} : Set _) →
      ψ.symm x ∈ Subgroup.centralizer ({y} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hψ, hx]
  refine ⟨⟨S.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩, ⟨ψ.symm z, hcomm z hzc, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hcomm x (hSc hx)
  · rw [← Subgroup.map_commutator, hSp]
  · rwa [Subgroup.card_map_of_injective ψ.symm.injective]
  · rw [MulEquiv.orderOf_eq, hz3]
  · intro h3
    obtain ⟨A, hAc, hAe, hAcard⟩ := hA h3
    refine ⟨A.map ψ.symm.toMonoidHom, ?_, CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hcomm x (hAc hx)
    · rwa [Subgroup.card_map_of_injective ψ.symm.injective]

end CFSG.LocalAnalysis.UniquenessCase.UC22.D4Seven
