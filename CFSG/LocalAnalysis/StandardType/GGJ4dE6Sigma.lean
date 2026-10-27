module

public import CFSG.LocalAnalysis.StandardType.GGJ4dPair
public import CFSG.LocalAnalysis.StandardType.GGJ4dStable
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Class
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwClass
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4TwLayers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private def j4dE6SigmaCheck : Bool :=
  (List.range e6Certificate.roots.length).all fun k =>
    let v := e6Certificate.root k
    if permLattice e6Graph v = v then true else iform v (permLattice e6Graph v) == 0

private theorem j4dE6SigmaCheck_eq : j4dE6SigmaCheck = true := by decide +kernel

theorem j4dE6Sigma_moved_orthogonal
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hmoved : permLattice e6Graph γ ≠ γ) :
    iform γ (permLattice e6Graph γ) = 0 := by
  have hcheck := j4dE6SigmaCheck_eq
  rw [j4dE6SigmaCheck, List.all_eq_true] at hcheck
  obtain ⟨k, hk, hroot⟩ :=
    (RootCertificate.isRoot_iff e6Certificate_check).1 hγ
  have hk2 := hcheck k (List.mem_range.2 hk)
  simp only at hk2
  have hmoved' : permLattice e6Graph (e6Certificate.root k) ≠ e6Certificate.root k := by
    simpa [hroot] using hmoved
  rw [if_neg hmoved'] at hk2
  have h0 := beq_iff_eq.1 hk2
  simpa [hroot] using h0

private def j4dE6SigmaAntiCheck : Bool :=
  (List.range e6Certificate.roots.length).all fun k =>
    let v := e6Certificate.root k
    !(permLattice e6Graph v == -v)

private theorem j4dE6SigmaAntiCheck_eq : j4dE6SigmaAntiCheck = true := by decide +kernel

theorem j4dE6Sigma_no_antifixed
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    permLattice e6Graph γ ≠ -γ := by
  have hcheck := j4dE6SigmaAntiCheck_eq
  rw [j4dE6SigmaAntiCheck, List.all_eq_true] at hcheck
  obtain ⟨k, hk, hroot⟩ :=
    (RootCertificate.isRoot_iff e6Certificate_check).1 hγ
  have hk2 := hcheck k (List.mem_range.2 hk)
  simp only at hk2
  intro h
  have hanti : permLattice e6Graph (e6Certificate.root k) = -e6Certificate.root k := by
    simpa [hroot] using h
  rw [hanti] at hk2
  simpa using hk2

theorem j4dE6Sigma_pair_kills
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a b : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit τ b})
    {γ : Fin τ.rank → ℤ}
    (hγcomp : γ ∈ componentRoots (rootCharHom a) i)
    (hβcomp : S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hγr : IsRoot τ γ) (hβr : IsRoot τ (S.ρ γ))
    (hρ2 : S.ρ (S.ρ γ) = γ) (horth : iform γ (S.ρ γ) = 0) (hne : γ ≠ S.ρ γ) :
    rootChar b γ = 1 :=
  (j4d_pair_detects_same S hτ hq hAlg i hle hγcomp hβcomp hγr hβr rfl hρ2 horth hne).1

theorem j4dE6Sigma_stable_of_pair_neg
    {τ : Tag} {L : Type} [Field L]
    (b : Fin τ.rank → Lˣ) {γ δ : Fin τ.rank → ℤ}
    (hδ : rootChar b δ = 1) (hsum : rootChar b (γ + δ) = 1) :
    rootChar b γ = 1 := by
  have h := rootChar_add b γ δ
  rw [hsum, hδ, mul_one] at h
  exact h.symm

theorem j4dE6Sigma_stable_of_pair_pos
    {τ : Tag} {L : Type} [Field L]
    (b : Fin τ.rank → Lˣ) {γ δ : Fin τ.rank → ℤ}
    (hδ : rootChar b δ = 1) (hsub : rootChar b (γ - δ) = 1) :
    rootChar b γ = 1 := by
  have h := rootChar_sub b γ δ
  rw [hsub, hδ, inv_one, mul_one] at h
  exact h.symm





end CFSG.StandardType.LangRat

end


