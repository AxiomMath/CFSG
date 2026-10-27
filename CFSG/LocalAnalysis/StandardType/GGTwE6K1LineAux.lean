module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
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
public import CFSG.Open.SplitBNPair
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
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
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
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import Certificates.Certificate10050
public import Certificates.Certificate8117

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


variable {K : Type} [Field K] {σ : K ≃+* K}

section Dim


theorem twE6MatFixDim_mem_of_pow_three [Finite K] (hK3 : ringChar K ≠ 3)
    {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    twE6MatFixDim K σ h ∈ ({24, 28, 30, 36, 46} : Set ℕ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) ∈
      adjointGroup Tag.E6 (AlgebraicClosure K) :=
    map_twistedE6InndiagGL_le σ (algebraMap K (AlgebraicClosure K))
      KSNotAll24.exists_cube_root_algebraicClosure (Subgroup.mem_map_of_mem _ h.2)
  have hx3 : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  obtain ⟨a, ha3, ha1, hdim⟩ :=
    KSNotAll24.exists_torus_conj_of_cube_one (x := (h : ModGL TwistTag.E6.tag K)) hK3 hxL hx3
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 3).1 h0
    exact hK3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 this)
  have key := KSNotAll24.finrank_ker_rootDiag_mem h3L ha3 fun h1 => hh1 (Subtype.ext (ha1 h1))
  rw [← hdim] at key
  exact key

theorem baseChange_comap_le_adjointGroup (E : Subgroup (MulAut (twistedE6RootGroup K σ))) :
    ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))) ≤
      adjointGroup Tag.E6 (AlgebraicClosure K) :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
    (map_twistedE6InndiagGL_le σ (algebraMap K (AlgebraicClosure K))
      KSNotAll24.exists_cube_root_algebraicClosure)

end Dim

theorem exists_inner_of_mem_twistedE6Inn [Finite K] {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1)
    (hh1 : h ≠ 1) (hin : twistedE6InndiagConj K σ h ∈ twistedE6Inn K σ) :
    ∃ s : twistedE6RootGroup K σ, MulAut.conj s = twistedE6InndiagConj K σ h ∧ s ^ 3 = 1 ∧
      s ≠ 1 ∧ twE6FixDim K σ s = twE6MatFixDim K σ h := by
  obtain ⟨s, hs⟩ := hin
  have hinj := twE6_conj_injective K σ q hσ hKq hq2
  have hC : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ := le_sup_left
  have hsh : twistedE6InndiagConj K σ ⟨(s : ModGL TwistTag.E6.tag K), hC s.2⟩ =
      MulAut.conj s := by
    ext c
    rfl
  have hhs : h = ⟨(s : ModGL TwistTag.E6.tag K), hC s.2⟩ :=
    hinj (hs.symm.trans hsh.symm)
  refine ⟨s, hs, ?_, ?_, (twE6MatFixDim_of_inner K σ q hσ hKq hq2 s h (hs.symm)).symm⟩
  · apply Subtype.ext
    have h1 := congrArg Subtype.val hh3
    rw [hhs, Subgroup.coe_pow] at h1
    rw [Subgroup.coe_pow]
    exact h1
  · rintro rfl
    exact hh1 (hhs.trans (Subtype.ext rfl))

theorem isElemAbelian_baseChange_comap (hinj : Function.Injective (twistedE6InndiagConj K σ))
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (((E.comap (twistedE6InndiagConj K σ)).map
      (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) :=
  ((hE.comap hinj).map _).map _

theorem baseChange_comap_commute (hinj : Function.Injective (twistedE6InndiagConj K σ))
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : CFSG.Open.IsElemAbelian 3 E)
    {h : twistedE6InndiagGL K σ} (hfE : twistedE6InndiagConj K σ h ∈ E) :
    ∀ x ∈ ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))),
      x * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          (h : ModGL TwistTag.E6.tag K) =
        baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          (h : ModGL TwistTag.E6.tag K) * x := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  have hgh : g * h = h * g := hinj (by rw [map_mul, map_mul]; exact hE.comm hg hfE)
  have h1 : (g : ModGL TwistTag.E6.tag K) * h = h * g := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hgh]
  have h2 := congrArg (baseChangeGL (algebraMap K (AlgebraicClosure K))) h1
  rw [map_mul, map_mul] at h2
  exact h2

end CFSG.StandardType.SCFourCover

end
