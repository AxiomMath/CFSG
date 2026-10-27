module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Gen
public import CFSG.RankThree.Classical.SteinbergBYKernelBlockUnitary
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate2323
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType

open CFSG.LinearAlgebra.SteinbergBQ

theorem ggTBC_orth_mem_of_commute {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n) {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hH : CFSG.Open.IsElemAbelian 3 H)
    (hcard : Nat.card H = 3 ^ n) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgH : ∀ h ∈ H, g * h = h * g) : g ∈ H :=
  letI : Finite V := Module.finite_of_finite (ZMod 2)
  letI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  letI : Finite H := Subtype.finite
  letI : IsMulCommutative H := hH.1
  letI : CommGroup H := IsMulCommutative.instCommGroup
  letI : CFSG.IsElementaryAbelian 3 H :=
    { toIsMulCommutative := hH.1
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        exact Subtype.ext (hH.2 x x.2) }
  by
    classical
    have hpowH : ∀ e : H, e ^ 3 = 1 := fun e => Subtype.ext (hH.2 e e.2)
    have hfix : fixedSub H = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      by_contra hv0
      exact CFSG.LocalAnalysis.GLTheoremA.H1017.false_of_fixed_vector (E := H) hcard hpowH
        H.subtype H.subtype_injective hdim hv0
        (fun e => (mem_fixedSub.mp hv) (e : V ≃ₗ[ZMod 2] V) e.2)
    let S : Set (Subgroup (V ≃ₗ[ZMod 2] V)) :=
      {N | N ≤ H ∧ N.relIndex H = 3 ∧ fixedSub N ≠ ⊥}
    have hS : S.Finite := Set.toFinite S
    let I : Finset (Subgroup (V ≃ₗ[ZMod 2] V)) := hS.toFinset
    have hI : ∀ N, N ∈ I ↔ N ≤ H ∧ N.relIndex H = 3 ∧ fixedSub N ≠ ⊥ :=
      fun N => hS.mem_toFinset
    have hproper : ∀ N : I, ∃ x : V ≃ₗ[ZMod 2] V, x ∈ H ∧ x ∉ (N : Subgroup _) := by
      intro N
      have hNH : (N : Subgroup _) ≤ H := ((hI N).1 N.2).1
      have hidx : (N : Subgroup _).relIndex H = 3 := ((hI N).1 N.2).2.1
      have hne : (N : Subgroup _) ≠ H := by
        intro h
        rw [h, Subgroup.relIndex_self] at hidx
        exact absurd hidx (by norm_num)
      exact SetLike.exists_of_lt (lt_of_le_of_ne hNH hne)
    choose c hcH hcN using hproper
    obtain ⟨d, h3, hfp, -, -, -, -, -, -, -, hmr⟩ :=
      CFSG.RankThree.Classical.SteinbergBY.binary_three_kernel_block_unitary_centralizers
        Q hQ hdim H hHO hcard hfix I hI c (fun N => ⟨hcH N, hcN N⟩)
    obtain ⟨-, -, -, hcen, -, -⟩ := hmr rfl
    have hmem : g ∈ Subgroup.centralizer (H : Set (V ≃ₗ[ZMod 2] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [Subgroup.mem_inf]
      refine ⟨?_, hg⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hgH h hh).symm
    simpa [hcen] using hmem

end CFSG.StandardType

end
