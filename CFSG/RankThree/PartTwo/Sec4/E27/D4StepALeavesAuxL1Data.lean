module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Uni
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.PartTwo.Sec19
open scoped Matrix Pointwise MatrixGroups commutatorElement

section Data


set_option maxHeartbeats 400000 in
theorem exists_threeA_layer_linear {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 1) (hq4 : 4 ≤ ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [CharP (AlgebraicClosure K) ℓ]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      LayerLinearModel σ x := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  set L := AlgebraicClosure K with hL
  have hqε : ((ℓ ^ f : ℕ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    rw [← ZMod.natCast_mod, hq1]
    rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (threeSixN L 1)
    (threeSixN_mem_adjointGroup (Or.inl rfl))
  have hFg' : trialityFrob L Fr g = g * threeSixN L 1 := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr (Or.inl rfl) hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG hFg' ha
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · exact layerLinearModel_of_model hℓp hℓ3 hf hq4 (by omega) σ hK hσ L Fr hFr g hgG hFg'
      (tup ζ gT) ha hord vT hv x hx

set_option maxHeartbeats 400000 in
theorem exists_threeA_layer_unitary {K : Type} [Field K] [Finite K] {n : ℕ} [Fact (Nat.Prime 2)]
    (hn1 : 1 ≤ n) (hq1 : 2 ^ n % 3 = 2) (hq2 : 2 < 2 ^ n)
    (hK : Nat.card K = (2 ^ n) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) [CharP (AlgebraicClosure K) 2]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    ∃ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (k : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      k ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      triEmb K σ (AlgebraicClosure K) x = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ ∧
      LayerUnitaryModel σ n x := by
  classical
  have hℓp : Nat.Prime 2 := Nat.prime_two
  have hℓ3 : (2 : ℕ) ≠ 3 := by decide
  set L := AlgebraicClosure K with hL
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hqε : ((2 ^ n : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) := by
    rw [← ZMod.natCast_mod, hq1]
    rfl
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := K) (ℓ := 2) hn1 L (threeSixN L (-1))
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L (-1) := hFg
  have ha := mem_threeSixTorus_tup_gT (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := exists_threeSixEmb_eq_conj hℓp hn1 hK hσ hFr hgG hFg' ha
  have hord := orderOf_rootDiagUnit_tup_gT hζ
  have hv := survivingRoots_tup_gT hζ
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  refine ⟨x, g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹,
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_, ?_⟩
  · change threeSixEmb K L σ x = _
    rw [hx, hd]
    group
  · exact layerUnitaryModel_of_model hn1 hq2 hq1 σ hK hσ L Fr hFr g hgG hFg'
      (tup ζ gT) ha hord vT hv x hx

end Data

end CFSG.RankThree.PartTwo.Sec4.E27
