module

public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinBlock
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.RankThree.CALinearPlane
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne.KCPrimary

private theorem tptdB_sylow_two_card_projectiveSL {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ T : Sylow 2 (projectiveSL n F),
      Nat.card (T : Subgroup (projectiveSL n F)) = Nat.card F ^ (n * (n - 1) / 2) := by
  obtain ⟨T, hT⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := n) hn
  exact ⟨T, by rw [hT, card_projUnitriangular]⟩

private theorem tptdB_card_pow_eq_of_equiv_projectiveSL {m n : ℕ} {E K : Type}
    [Field E] [Finite E] [CharP E 2] [Field K] [Finite K] [CharP K 2]
    (hm : 1 ≤ m) (hn : 1 ≤ n) (e : projectiveSL m E ≃* projectiveSL n K) :
    Nat.card E ^ (m * (m - 1) / 2) = Nat.card K ^ (n * (n - 1) / 2) := by
  obtain ⟨T, hT⟩ := tptdB_sylow_two_card_projectiveSL (F := E) hm
  obtain ⟨T', hT'⟩ := tptdB_sylow_two_card_projectiveSL (F := K) hn
  have hmapcard : Nat.card ((T : Subgroup (projectiveSL m E)).map e.toMonoidHom) =
      Nat.card (T : Subgroup (projectiveSL m E)) :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  have hequiv := Sylow.equiv (T.mapSurjective (f := e.toMonoidHom) e.surjective) T'
  have hcard : Nat.card (T : Subgroup (projectiveSL m E)) =
      Nat.card (T' : Subgroup (projectiveSL n K)) := by
    calc Nat.card (T : Subgroup (projectiveSL m E))
        = Nat.card ((T : Subgroup (projectiveSL m E)).map e.toMonoidHom) := hmapcard.symm
      _ = Nat.card (T' : Subgroup (projectiveSL n K)) := Nat.card_congr hequiv.toEquiv
  rw [← hT, ← hT', hcard]

private theorem tptdB_eq_of_mul_sub_one_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m * (m - 1) = n * (n - 1)) : m = n := by
  have hZ : (m : ℤ) * ((m : ℤ) - 1) = (n : ℤ) * ((n : ℤ) - 1) := by
    have h1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    have h2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hcast := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast at hcast
    rw [h1, h2] at hcast
    exact hcast
  have hfac : ((m : ℤ) - n) * ((m : ℤ) + (n : ℤ) - 1) = 0 := by nlinarith
  have hpos : (0 : ℤ) < (m : ℤ) + (n : ℤ) - 1 := by
    have : (2 : ℤ) ≤ m := by exact_mod_cast hm
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn
    omega
  have : (m : ℤ) - n = 0 := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact h'
    · omega
  omega

private theorem tptdB_eq_of_equiv_projectiveSL {m n : ℕ} {E K : Type}
    [Field E] [Finite E] [CharP E 2] [Field K] [Finite K] [CharP K 2]
    (hm : 2 ≤ m) (hn : 2 ≤ n) (e : projectiveSL m E ≃* projectiveSL n K) : m = n := by
  have hcard : Nat.card E = Nat.card K :=
    CFSG.Quasithin.B69.card_eq_of_equiv_projectiveSL hm hn e
  have hpow : Nat.card E ^ (m * (m - 1) / 2) = Nat.card E ^ (n * (n - 1) / 2) := by
    have h0 := tptdB_card_pow_eq_of_equiv_projectiveSL (le_trans (by norm_num) hm)
      (le_trans (by norm_num) hn) e
    rwa [← hcard] at h0
  have hq : 2 ≤ Nat.card E := by have := Finite.one_lt_card (α := E); omega
  have hdiv : m * (m - 1) / 2 = n * (n - 1) / 2 := Nat.pow_right_injective hq hpow
  have hm2 : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))
  have hn2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))
  have hsub : m * (m - 1) = n * (n - 1) := by rw [← hm2, ← hn2, hdiv]
  exact tptdB_eq_of_mul_sub_one_eq hm hn hsub

theorem tptdB_block_numerics
    {K : Type} [Field K] [Finite K] [CharP K 2] {d p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 4 ≤ d) (hf : Nat.card K = 2 ^ f)
    {g : GL (Fin d) K} {c : Kˣ}
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {C : Subgroup (projectiveSL d K)}
    (hC : IsComponentOf C
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (conjAut d K g)))
    {labJ : LargeEvenLabel} (hlabJ : LargeEvenInLambda2 labJ) (hlabJtag : labJ.tag = .A)
    (hlabJrank : labJ.rank = d - 2) (hlabJn : labJ.n = f)
    (hlabel : GGHasLabel labJ (↥C ⧸ Subgroup.center ↥C)) :
    ∃ h : Polynomial K, h.natDegree = 1 ∧
      h ∈ primaryFactors (glA g : Module.End K (Fin d → K)) ∧
      IsGoodFactor g h ∧
      primaryMultiplicity (glA g : Module.End K (Fin d → K)) h = d - 1 ∧
      C = (specialFactor g h).map (proj d K) := by
  have hpk : (p : K) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  have hf1 : 1 ≤ f := by
    have h2 : 2 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
    by_contra hf0
    have hf0' : f = 0 := by omega
    rw [hf0', pow_zero] at hf
    omega
  obtain ⟨hh, hCeq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
      (n := d) (k := K) hpk hg C (CFSG.Assembly.isComponentOf_iff_open.mp hC)
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))) :=
    squarefree_minpoly_glA hpk hg
  set h0 : Polynomial K := hh.1.1 with hh0
  have hmem : h0 ∈ primaryFactors (glA g : Module.End K (Fin d → K)) := hh.1.2
  have hgood : IsGoodFactor g h0 := hh.2
  rw [GGHasLabel] at hlabel
  rw [LargeEvenRawDatum] at hlabel
  rw [hlabJtag] at hlabel
  rw [hlabJrank, hlabJn] at hlabel
  have hd1 : d - 2 + 1 = d - 1 := by omega
  rw [hd1] at hlabel
  rw [LargeEvenRecipeLinear] at hlabel
  obtain ⟨K', hFld, hFin, hK'card, hQ⟩ := hlabel
  letI : Field K' := hFld
  haveI : Finite K' := hFin
  have hK'char : ringChar K' = 2 :=
    CFSG.RankThree.Chevalley.ringChar_eq_of_card Nat.prime_two hf1 hK'card
  haveI : CharP K' 2 := ringChar.of_eq hK'char
  obtain ⟨eQ⟩ := hQ
  have eJ : (↥C ⧸ Subgroup.center ↥C) ≃* projectiveSL (d - 1) K' :=
    eQ.trans (TypeA.recipeEquiv (d - 1) K')
  obtain ⟨eSL⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq hmem
  obtain ⟨f, hf_surj, hf_ker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_surjective_ker_le_center_map_proj
      (n := d) (k := K) (S := specialFactor g h0) eSL
  let gC : ↥((specialFactor g h0).map (proj d K)) ≃* ↥C := (MulEquiv.subgroupCongr hCeq).symm
  let f' : Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)) (AdjoinRoot h0) →*
      ↥C := gC.toMonoidHom.comp f
  have hf'_surj : Function.Surjective f' := gC.surjective.comp hf_surj
  have hf'_ker : f'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)) (AdjoinRoot h0)) := by
    rw [show f'.ker = f.ker from
      CFSG.StandardType.TypeA.ker_comp_mulEquiv gC f]
    exact hf_ker
  haveI : Fact (Irreducible h0) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  haveI : Finite (AdjoinRoot h0) := by
    have hmod : Module.Finite K (AdjoinRoot h0) :=
      (AdjoinRoot.powerBasis (Fact.out : Irreducible h0).ne_zero).finite
    exact Module.finite_of_finite K
  haveI : CharP (AdjoinRoot h0) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h0)).injective 2
  have hqF : CFSG.IsQuasisimple ↥(specialFactor g h0) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_specialFactor
      hsq hmem hgood
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)) (AdjoinRoot h0)) :=
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eSL.symm hqF).1
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f' hf'_surj hperfSL hf'_ker
  let eCent : (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)) (AdjoinRoot h0) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup
          (Fin (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)) (AdjoinRoot h0))) ≃*
      projectiveSL (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0) (AdjoinRoot h0) :=
    QuotientGroup.quotientMulEquivOfEq
      (scalars_eq_center
        (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0) (AdjoinRoot h0)).symm
  have eComb : projectiveSL (primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0)
      (AdjoinRoot h0) ≃* projectiveSL (d - 1) K' := (eCent.symm.trans eC).trans eJ
  have hm2 : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0 := by
    rcases hgood with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hn2 : 2 ≤ d - 1 := by omega
  have hmult : primaryMultiplicity (glA g : Module.End K (Fin d → K)) h0 = d - 1 :=
    tptdB_eq_of_equiv_projectiveSL hm2 hn2 eComb
  have hEcard : Nat.card (AdjoinRoot h0) = Nat.card K := by
    have hcard' : Nat.card (AdjoinRoot h0) = Nat.card K' :=
      CFSG.Quasithin.B69.card_eq_of_equiv_projectiveSL hm2 hn2 eComb
    rw [hcard', hK'card, hf]
  have hdeg : h0.natDegree = 1 := by
    have hK2 : 2 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
    apply Nat.pow_right_injective hK2
    show Nat.card K ^ h0.natDegree = Nat.card K ^ 1
    rw [pow_one, ← CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h0]
    exact hEcard
  exact ⟨h0, hdeg, hmem, hgood, hmult, hCeq⟩

end CFSG.StandardType

end
