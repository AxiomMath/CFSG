module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Defs
public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LieType.Chevalley.C2E6FirstResidueLevi
public import CFSG.Monster.B.E6.StdF4Opposite
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyModel
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.Foundations
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldStep3
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowFieldCover
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate1016Base
public import Certificates.Certificate1021
public import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4


private theorem levi_setA_eq :
    (C2E6Std.setA : Set (Fin TwistTag.E6.tag.rank)) = E6GraphLevi.setA := by
  ext i
  show i ∈ ({0, 2, 3, 4, 5} : Set (Fin 6)) ↔ i ∈ {j : Fin 6 | j ≠ 1}
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  revert i
  decide

theorem levi_stdGroup : ∃ y₀ : ↥stdGroup, orderOf y₀ = 3 ∧ ∃ L : Subgroup ↥stdGroup,
    L ≤ Subgroup.centralizer ({y₀} : Set ↥stdGroup) ∧ Nat.card L = 9196830720 ∧
    ∀ P : Subgroup ↥stdGroup, P ≤ Subgroup.centralizer ({y₀} : Set ↥stdGroup) → ⁅P, P⁆ = P →
      P ≤ L := by
  refine ⟨rootInv * tMinus, orderOf_rootInv_mul_tMinus, (stdLevi firstJ).subgroupOf stdGroup,
    ?_, card_stdLevi_subgroupOf, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp (stdLevi_subgroupOf_le hx)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2 ⊢
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  · intro P hPc hPp
    have hk : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
    have hK : Nat.card K = 2 ^ 2 := by
      rw [Nat.card_eq_fintype_card, card_K]
      norm_num
    have hR : (((rootInv : ↥stdGroup) : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) ∈
        E6GraphLevi.thetaRootGroup (algebraMap (ZMod 2) K) := by
      refine (E6GraphLevi.mem_thetaRootGroup (algebraMap (ZMod 2) K)).2 ⟨1, ?_⟩
      rw [map_one, coe_rootInv, rootInvM, theta_eq]
      rfl
    have hT : (((tMinus : ↥stdGroup) : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) ∈
        E6GraphLevi.thetaNegRootGroup (algebraMap (ZMod 2) K) := by
      refine (E6GraphLevi.mem_thetaNegRootGroup (algebraMap (ZMod 2) K)).2 ⟨1, ?_⟩
      rw [map_one, coe_tMinus, theta_eq]
      rfl
    have ha : (((rootInv * tMinus : ↥stdGroup) : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) ∈
        E6GraphLevi.thetaRankOneGroup (algebraMap (ZMod 2) K) := by
      rw [Subgroup.coe_mul]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hR) (Subgroup.mem_sup_right hT)
    have ha3 : orderOf
        (((rootInv * tMinus : ↥stdGroup) : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_rootInv_mul_tMinus
    have hQp : ⁅P.map stdGroup.subtype, P.map stdGroup.subtype⁆ = P.map stdGroup.subtype := by
      rw [← Subgroup.map_commutator, hPp]
    have hQC : P.map stdGroup.subtype ≤ adjointGroup Tag.E6 K :=
      (Subgroup.map_subtype_le P).trans
        ((graphFixedRootGroup_le TwistTag.E6 K barHom).trans
          (twistedFixedGroup_le_adjointGroup TwistTag.E6 K barHom))
    have hQa : P.map stdGroup.subtype ≤
        Subgroup.centralizer {((rootInv * tMinus : ↥stdGroup) : ModGL Tag.E6 K)} := by
      rintro _ ⟨p, hp, rfl⟩
      have h := hPc hp
      rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
      rw [Subgroup.coe_subtype, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
    have hQA := CFSG.SeitzReduction.TwistedE6Pilot.le_subsystemGroup_of_perfect_of_le_centralizer
      (k := ZMod 2) (K := K) hk hK (algebraMap (ZMod 2) K) ha ha3 hQp hQC hQa
    intro x hx
    rw [Subgroup.mem_subgroupOf, stdLevi_firstJ]
    refine Subgroup.mem_inf.mpr ⟨?_, graphFixedRootGroup_le TwistTag.E6 K barHom x.2⟩
    have h := hQA (Subgroup.mem_map_of_mem stdGroup.subtype hx)
    rw [← levi_setA_eq] at h
    exact h

theorem levi_of_model {X : Type} [Group X] [Finite X]
    (h : ChevalleyExceptionalModel X .twistedE6 2 1) :
    ∃ y₀ : X, orderOf y₀ = 3 ∧ ∃ L : Subgroup X,
      L ≤ Subgroup.centralizer ({y₀} : Set X) ∧ Nat.card L = 9196830720 ∧
      ∀ P : Subgroup X, P ≤ Subgroup.centralizer ({y₀} : Set X) → ⁅P, P⁆ = P → P ≤ L := by
  have hLie : LieModel X .twistedE6 0 2 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  obtain ⟨e⟩ := C2E6Std.MatrixModel.nonempty_mulEquiv_stdGroup_of_lieModel hLie
  obtain ⟨y, hy, L, hLc, hLcard, hLperf⟩ := levi_stdGroup
  refine ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy, L.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    have h1 := hLc hl
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h1]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hLcard]
  · intro P hPc hPp
    have hP' : P.map e.toMonoidHom ≤ L := by
      refine hLperf _ ?_ ?_
      · rintro _ ⟨p, hp, rfl⟩
        have h1 := hPc hp
        rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
        have h2 := congrArg e h1
        simp only [map_mul, MulEquiv.apply_symm_apply] at h2
        simpa using h2
      · rw [← Subgroup.map_commutator, hPp]
    intro x hx
    exact ⟨e x, hP' ⟨x, hx, rfl⟩, by simp⟩

end CFSG.StandardType.TwE6MaxEleven
