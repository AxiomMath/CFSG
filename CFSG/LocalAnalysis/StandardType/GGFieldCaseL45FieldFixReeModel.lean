module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeFix
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

section ReeModel

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem gff_center_eq_bot_ree (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type}
    [Group X] [Finite X] (hX : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)) :
    Subgroup.center X = ⊥ := by
  have hperf : Group.IsPerfect X := ⟨hX⟩
  have hrel : ReeTitsRelationModel (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)) .F4
      reeF4Perm reeF4Long 2 (2 * a + 1) a :=
    ⟨K, inferInstance, inferInstance, hK,
      nonempty_centerQuot_congr (gff_commutator_reeFixedGroup ha hK).symm⟩
  have hRee : ReeTitsModel (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)) .twistedF4 2
      (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl, hrel⟩
  have hLie : LieModel (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)) .twistedF4 0 2
      (2 * a + 1) := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hRee⟩))
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier
      (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a))) :=
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.reeF4_hopfMultiplier ha hLie).2
  have hdiv := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf θ
  rw [Nat.card_of_subsingleton (1 : CFSG.Open.griessHopfMultiplier
    (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)))] at hdiv
  exact Subgroup.eq_bot_of_card_le (Subgroup.center X) (Nat.le_of_dvd Nat.one_pos hdiv)

theorem gff_torsion_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (I : Set (MulAut (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)))) :
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a)) I
      (RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a)) := by
  intro X _ _ θ hX ψ _ hind Q hQ
  obtain ⟨f, hfF, u, -, hford, hind⟩ := hind
  have hZΓ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  obtain ⟨σ, hσ⟩ := gff_ree_exists_fieldAut hZΓ hfF
  have hσp : orderOf σ = p := by
    rw [← orderOf_injective _ (gff_reeGammaFieldAutHom_injective ha hK) σ]
    change orderOf (ReeTag.F4.reeGammaFieldAut K a σ) = p
    rw [← hσ, MulEquiv.orderOf_eq, hford]
  obtain ⟨b, k, _, _, _, hkcard, -, ⟨E⟩⟩ := gff_ree_fixed hK hp hp2 σ hσp
  have hZ : Subgroup.center X = ⊥ := gff_center_eq_bot_ree ha hK hX θ
  let e : LargeEvenCenterQuot (ReeTag.F4.reeGamma K a) ≃* ↥(ReeTag.F4.reeGamma K a) :=
    centerQuotEquivOfBot hZΓ
  let m : X ≃* ↥(ReeTag.F4.reeGamma K a) := (gffIsoOfCenterBot θ hZ).trans e
  let g : MulAut ↥(ReeTag.F4.reeGamma K a) := MulAut.congr e u
  have key : ∀ x, (g * ReeTag.F4.reeGammaFieldAut K a σ * g⁻¹) (m x) = m (ψ x) := by
    intro x
    have h1 : MulAut.congr e (u * f * u⁻¹) = g * ReeTag.F4.reeGammaFieldAut K a σ * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσ]
    rw [← h1, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, gffIsoOfCenterBot_apply]
    rw [hind _ _ rfl]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m ψ g (ReeTag.F4.reeGammaFieldAut K a σ) key E
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card k = 2 := by simpa using hkcard
    let E'' : ↥(ggAutFixedSubgroup ψ) ≃* ↥(reeFixed ReeTag.F4 k 0) :=
      E'.trans (ReeTag.reeFixedEquivReeGamma k 0).symm
    let eJ : ↥⁅ggAutFixedSubgroup ψ, ggAutFixedSubgroup ψ⁆ ≃*
        ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) :=
      (CFSG.LieType.BorelTits.commutatorSubgroupEquiv (ggAutFixedSubgroup ψ)).trans
        (CFSG.LieType.BorelTits.commutatorEquiv E'')
    haveI : IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := gff_isSimpleGroup_tits hk2
    haveI : IsSimpleGroup ↥⁅ggAutFixedSubgroup ψ, ggAutFixedSubgroup ψ⁆ := eJ.isSimpleGroup
    have hQeq : Q = ⁅ggAutFixedSubgroup ψ, ggAutFixedSubgroup ψ⁆ :=
      CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_commutator_eq rfl hQ
    subst hQeq
    exact largeEvenMarking_of_mulEquiv eJ (gff_marking_tits hk2)
  ·
    haveI : IsSimpleGroup ↥(ReeTag.F4.reeGamma k b) := gff_isSimpleGroup_reeGamma hb hkcard
    haveI : IsSimpleGroup ↥(ggAutFixedSubgroup ψ) := E'.isSimpleGroup
    have hQeq : Q = ggAutFixedSubgroup ψ :=
      CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup hQ
    subst hQeq
    exact largeEvenMarking_of_mulEquiv E' (gff_marking_reeGamma hb hkcard)

end ReeModel

end CFSG.StandardType
