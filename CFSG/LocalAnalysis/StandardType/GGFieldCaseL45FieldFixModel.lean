module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixData
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixMark
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Model

theorem gff_isSimpleGroup_adjoint {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) (k : Type) [Field k]
    [Finite k] : IsSimpleGroup ↥(adjointGroup τ k) := by
  have h : IsSimpleGroup (↥(adjointGroup τ k) ⧸ Subgroup.center ↥(adjointGroup τ k)) :=
    (gff_isQuasisimple_adjoint hτ k).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem gff_center_eq_bot {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : 5 ≤ Nat.card K) {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* AdjointQuotient τ K) : Subgroup.center X = ⊥ := by
  have hperf : Group.IsPerfect X := ⟨hX⟩
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient τ K)) := by
    rcases hτ with rfl | rfl
    · exact (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier hK).2
    · exact (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_hopfMultiplier hK).2
  have hdiv := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf θ
  rw [Nat.card_of_subsingleton (1 : CFSG.Open.griessHopfMultiplier (AdjointQuotient τ K))]
    at hdiv
  exact Subgroup.eq_bot_of_card_le (Subgroup.center X) (Nat.le_of_dvd Nat.one_pos hdiv)

theorem gff_torsion_model {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (I : Set (MulAut (LargeEvenCenterQuot (adjointGroup τ K)))) :
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (adjointGroup τ K)) I
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  intro X _ _ θ hX ψ _ hind Q hQ
  obtain ⟨f, hfF, u, -, hford, hind⟩ := hind
  have hr : 0 < τ.rank := by rcases hτ with rfl | rfl <;> decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hfF
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨k, _, _, n', hk, hnn', hn'1, ⟨E⟩⟩ := gff_fixed_data hτ hn hK hp.pos hσp
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn3 : 3 ≤ n := by
    have := Nat.mul_le_mul hp3 hn'1
    omega
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hZ : Subgroup.center X = ⊥ := gff_center_eq_bot hτ hK5 hX θ
  let e : LargeEvenCenterQuot (adjointGroup τ K) ≃* adjointGroup τ K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  let m : X ≃* adjointGroup τ K := (gffIsoOfCenterBot θ hZ).trans e
  let g : MulAut (adjointGroup τ K) := MulAut.congr e u
  have key : ∀ x, (g * entrywiseAdjointAut τ σ * g⁻¹) (m x) = m (ψ x) := by
    intro x
    have h1 : MulAut.congr e (u * f * u⁻¹) = g * entrywiseAdjointAut τ σ * g⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rw [← hσ]
      rfl
    rw [← h1, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, gffIsoOfCenterBot_apply]
    rw [hind _ _ rfl]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m ψ g (entrywiseAdjointAut τ σ) key E
  haveI : IsSimpleGroup ↥(adjointGroup τ k) := gff_isSimpleGroup_adjoint hτ k
  haveI : IsSimpleGroup ↥(ggAutFixedSubgroup ψ) := E'.isSimpleGroup
  have hQeq : Q = ggAutFixedSubgroup ψ :=
    CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup hQ
  subst hQeq
  exact largeEvenMarking_of_mulEquiv E' (gff_marking_adjoint hτ hn'1 hk)

end Model

end CFSG.StandardType
