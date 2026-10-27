module

public import CFSG.LocalAnalysis.StandardType.GGKD2SmallPieces1615
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKChevTwoL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615

private theorem ltrke1_setupFalse_of_iso {R : Type} [Group R] [Finite R] {K : Type} [Field K]
    [Finite K] (e : R ≃* CFSG.GorensteinWalter.PSL2 K) {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {I : Set (MulAut R)} (hinn : I ⊆ LargeEvenInnSet R)
    (hZ : Subgroup.center R = ⊥) : SetupFalse R I := by
  intro L' _ _ ψ hψ hker hperf e' J a hsetup
  obtain ⟨h3p, h3ne2, he1, he3, hφe, hcomp, h2n, hlabel, hae, hφa, haJ, hnoninn⟩ := hsetup
  obtain ⟨φ, hφI, hφeq⟩ := hφe
  obtain ⟨r, hr⟩ := hinn hφI
  have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ChevTwoL2.conj_injective_of_center_eq_bot hZ
  have hφne : φ ≠ 1 := by
    intro h1
    apply he1
    refine TypeA.mulAut_eq_of_forall ψ hker hperf (a := e') (b := 1) fun l => ?_
    rw [← hφeq l, h1]
    rfl
  have hφ3 : φ ^ 3 = 1 := by
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [TypeA.induced_pow ψ hφeq 3 l, he3]
    rfl
  have hr3 : r ^ 3 = 1 := by
    apply hconjinj
    rw [map_pow, hr, hφ3, map_one]
  have hrne : r ≠ 1 := by
    intro h1
    apply hφne
    rw [← hr, h1, map_one]
  have hggFix : ggFix e' = ggFixSub e' := by
    ext x; exact Iff.rfl
  have hcompG : IsComponentOf J (ggFix e') := by rwa [hggFix]
  have hcomp' : IsComponentOf (J.map ψ) (ggFix φ) :=
    USixTwo.isComponentOf_map_fix (π := ψ) (a := e') (ab := φ) hψ hker hφeq hcompG
  have hcommC : ∀ u ∈ ggFix φ, r * u = u * r := by
    intro u hu
    have hu' : (MulAut.conj r) u = u := by rw [hr]; exact hu
    have hru : r * u * r⁻¹ = u := by simpa [MulAut.conj_apply] using hu'
    calc r * u = (r * u * r⁻¹) * r := by group
      _ = u * r := by rw [hru]
  have hcyc : IsCyclic ↥(ggFix φ) :=
    CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ChevTwoL2.isCyclic_of_le_centralizer_psl2
      (X := R) (K := K) (m := m) hm hK e (x := r) hr3 hrne (U := ggFix φ) hcommC
  haveI : IsCyclic ↥(ggFix φ) := hcyc
  exact CFSG.StandardType.Line63.H5.false_of_isComponentOf_of_isSolvable
    (C := ggFix φ) (J := J.map ψ) inferInstance hcomp'

private theorem ltrke1_setupFalse_linear {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hKcard : Nat.card K = 2 ^ m) :
    SetupFalse (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ) := by
  let e₁ := TypeA.recipeEquiv 2 K
  let e₂ := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 K).symm
  let e : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃* CFSG.GorensteinWalter.PSL2 K :=
    e₁.trans e₂.symm
  have hcop : (Nat.card Kˣ).Coprime 2 := by
    rw [Nat.card_units, hKcard]
    exact Nat.coprime_two_right.mpr (ggOdd_two_pow_sub_one (by omega))
  have hinn := matConjImage_gl_subset_inn (K := K) (d := 2) hcop
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have hz' : e z ∈ Subgroup.center (CFSG.GorensteinWalter.PSL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y]
    have h1 : e z = 1 := by
      have := hz'
      rw [CFSG.GorensteinWalter.psl2_center_eq_bot K] at this
      simpa using this
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  exact ltrke1_setupFalse_of_iso e hm hKcard hinn hZ

private theorem ltrke1_recipeLinear_setupFalse {N m : ℕ} (hm : 2 ≤ m) (hN : N = 2 ^ m)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear 2 N Q) :
    LargeEvenRecipeLinear 2 N fun R _ I F => Q R I F ∧ SetupFalse R I := by
  subst hN
  obtain ⟨K, hKf, hKfi, hKcard, hQ⟩ := h
  exact ⟨K, hKf, hKfi, hKcard, hQ, ltrke1_setupFalse_linear (K := K) hm hKcard⟩

theorem smallA1TwD2_holds : SmallA1TwD2 := by
  rintro ⟨t, l, n⟩ hlab hcase Q hQ
  rcases hcase with ⟨ht, hr⟩ | ⟨ht, hr⟩
  · dsimp only at ht hr
    subst ht
    subst hr
    dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    have hrec : LargeEvenRecipeLinear 2 (2 ^ n) Q := by
      simpa [CFSG.StandardType.LargeEvenRawDatum] using hQ
    have h := ltrke1_recipeLinear_setupFalse (m := n) (hlab.2.2 rfl) rfl hrec
    simpa [CFSG.StandardType.LargeEvenRawDatum] using h
  · dsimp only at ht hr
    subst ht
    subst hr
    dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
    have hrec : LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2) Q := by
      simpa [CFSG.StandardType.LargeEvenRawDatum] using hQ
    have hm : 2 ≤ 2 * n := by omega
    have hN : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
    have h := ltrke1_recipeLinear_setupFalse (m := 2 * n) hm hN hrec
    simpa [CFSG.StandardType.LargeEvenRawDatum] using h

end CFSG.StandardType.KD2Pieces1615

end
