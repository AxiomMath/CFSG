module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
import CFSG.LocalAnalysis.StandardType.KGLangS1ENormalFormE6Diag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeNonsplit
import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem kgLangS1ENormalFormE6Aux_rootDiagUnit_mem_adjointGroup
    {K : Type} [Field K] [Finite K] {e : ℕ} (hodd : Odd e)
    (hK : Nat.card K = 2 ^ e) (b : Fin 6 → Kˣ) :
    rootDiagUnit .E6 b ∈ adjointGroup .E6 K := by
  have hmod_aux : ∀ m : ℕ, (2 : ℕ) ^ (2 * m + 1) % 3 = 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hexp : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
      rw [hexp, pow_add, Nat.mul_mod, ih]
      norm_num
  obtain ⟨m, hm⟩ := hodd
  have hmod : (2 : ℕ) ^ e % 3 = 2 := by rw [hm]; exact hmod_aux m
  have hcop : Nat.Coprime (Nat.card Kˣ) 3 := by
    rw [Nat.card_units, hK, Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    intro hdvd
    have h1 : (2 ^ e - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h2 : (2 ^ e) % 3 = 1 := by
      have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
      have hsplit : 2 ^ e = (2 ^ e - 1) + 1 := by omega
      rw [hsplit, Nat.add_mod, h1]
    omega
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_adjointGroup_of_roots
    (τ := .E6) (L := K) (a := b) ?_
  intro j
  obtain ⟨u, hu⟩ := (powCoprime hcop).surjective (b j)
  refine ⟨u, ?_⟩
  rw [det_cartan_E6]
  simpa using hu

private theorem kgLangS1ENormalFormE6Aux_inndiagGroup_le_adjointGroup
    {K : Type} [Field K] [Finite K] {e : ℕ} (hodd : Odd e)
    (hK : Nat.card K = 2 ^ e) :
    RecipeExcLang.inndiagGroup .E6 K ≤ adjointGroup .E6 K := by
  rintro w ⟨b, j, hj, rfl⟩
  exact mul_mem (kgLangS1ENormalFormE6Aux_rootDiagUnit_mem_adjointGroup hodd hK b) hj

theorem kgLangS1E_ratPts_frob_E6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (hodd : Odd e) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* L), Nat.card k = 2 ^ e ∧
      ratPts .E6 L (frobTwistGL .E6 L 2 e 1) = (adjointGroup .E6 k).map (baseChangeGL ι) := by
  obtain ⟨k, _, _, ι, hk, hfix⟩ := kgLangS1E_ratPts_frob_E6_inndiag (L := L) he
  refine ⟨k, inferInstance, inferInstance, ι, hk, ?_⟩
  rw [hfix, le_antisymm (kgLangS1ENormalFormE6Aux_inndiagGroup_le_adjointGroup hodd hk)
    RecipeExcLang.adjointGroup_le_inndiagGroup]

theorem kgLangS1E_normalForm_toral_E6
    {e : ℕ} (he : 1 ≤ e) (_hodd : Odd e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = 2 ^ e) (hk : Nat.card k = 2 ^ e)
    (Ψ : ↥(adjointGroup .E6 K₀) ≃* ↥(adjointGroup .E6 k))
    {L : Type} [Field L] [IsAlgClosed L] (ι : k →+* L)
    (W : Subgroup ↥(RecipeExcLang.inndiagGroup .E6 K₀))
    (hW : GGGeomToral .E6 K₀ (W.map (RecipeExcLang.inndiagGroup .E6 K₀).subtype))
    (Y : Set (ModGL .E6 k))
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ adjointGroup .E6 k, ∃ w ∈ W, ∀ z : ↥(adjointGroup .E6 K₀),
      Ψ (RecipeExcLang.inndiagConj .E6 K₀ w z) =
        (⟨y, hy⟩ : ↥(adjointGroup .E6 k)) * Ψ z * (⟨y, hy⟩ : ↥(adjointGroup .E6 k))⁻¹) :
    ExcFramesHalf.IsToralSubgroup .E6 L
      (Subgroup.closure ((baseChangeGL (τ := .E6) ι) '' Y)) := by
  refine kgLangS1E_normalForm_toral_E6_inndiag he hK₀ hk Ψ ι W hW Y fun y hyY => ?_
  obtain ⟨hy, w, hw, hconj⟩ := hY y hyY
  refine ⟨RecipeExcLang.adjointGroup_le_inndiagGroup hy, w, hw, fun z => ?_⟩
  rw [hconj z]
  apply Subtype.ext
  rw [RecipeExcLang.coe_inndiagConj]
  rfl

end CFSG.StandardType
