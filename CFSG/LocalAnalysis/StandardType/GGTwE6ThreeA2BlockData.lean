module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KF4 CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Lang.E6Descent
open scoped MatrixGroups
open Matrix

@[expose] def a2PairE6 : Fin 3 → (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)
  | 0 => e6LinePair 0
  | 1 => ((e6LinePair 1).2, (e6LinePair 1).1)
  | 2 => e6LinePair 2

theorem isA2Pair_symm
    {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) : IsA2Pair β α := by
  refine ⟨h.isRoot_snd, h.isRoot_fst, ?_, h.iform_snd.symm, ?_⟩
  · rw [add_comm]
    exact h.isRoot_add
  · rw [iform_comm, h.iform_snd]
    exact h.two_iform


theorem isA2Pair_a2PairE6 (i : Fin 3) : IsA2Pair (a2PairE6 i).1 (a2PairE6 i).2 := by
  fin_cases i
  · exact isA2Pair_e6LinePair 0
  · exact isA2Pair_symm (isA2Pair_e6LinePair 1)
  · exact isA2Pair_e6LinePair 2

theorem pairRefl_a2PairE6 (i : Fin 3) : pairRefl (a2PairE6 i) = gE6 i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · have h := isA2Pair_a2PairE6 0
    refine ext_single fun j => ?_
    rw [pairRefl, mul_smul, rootReflection_smul h.isRoot_fst,
      rootReflection_smul h.isRoot_snd, gE6, wordProd_smul]
    decide +kernel +revert
  · have h := isA2Pair_a2PairE6 1
    refine ext_single fun j => ?_
    rw [pairRefl, mul_smul, rootReflection_smul h.isRoot_fst,
      rootReflection_smul h.isRoot_snd, gE6, wordProd_smul]
    decide +kernel +revert
  · have h := isA2Pair_a2PairE6 2
    refine ext_single fun j => ?_
    rw [pairRefl, mul_smul, rootReflection_smul h.isRoot_fst,
      rootReflection_smul h.isRoot_snd, gE6, wordProd_smul]
    decide +kernel +revert

@[expose] def pairFormE6 (α : Fin Tag.E6.rank → ℤ) (v : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  ∑ j, ((α j : ℤ) : ZMod 3) * v j

theorem rootChar_zetaVec_eq_one_iff {Ω : Type} [Field Ω] {ζ : Ωˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (v : Fin Tag.E6.rank → ZMod 3)
    (α : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec ζ hζ v) α = 1 ↔ pairFormE6 α v = 0 := by
  rw [NoOffE8Five.rootChar_zetaVec]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 1 :=
      (zmodPowHom_injective hζo hζ) (by rw [h, map_one])
    simpa [pairFormE6] using congrArg Multiplicative.toAdd h1
  · intro h
    rw [show (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 0 by simpa [pairFormE6] using h,
      ofAdd_zero, map_one]

theorem adAct_gE6_eq_iff (i : Fin 3) (v : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 (gE6 i) v = v ↔
      pairFormE6 (a2PairE6 i).1 v = 0 ∧ pairFormE6 (a2PairE6 i).2 v = 0 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · change adAct .E6 3 ((coxeterSystem .E6).wordProd (wordE6G 0)) v = v ↔ _
    rw [← adWord_eq_adAct]
    decide +kernel +revert
  · change adAct .E6 3 ((coxeterSystem .E6).wordProd (wordE6G 1)) v = v ↔ _
    rw [← adWord_eq_adAct]
    decide +kernel +revert
  · change adAct .E6 3 ((coxeterSystem .E6).wordProd (wordE6G 2)) v = v ↔ _
    rw [← adWord_eq_adAct]
    decide +kernel +revert

theorem exists_frame_a2PairE6 (K : Type) [Field K] (i : Fin 3) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K,
      ∃ σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ,
        IsA2Frame ρ σ ∧ σ 0 1 = (a2PairE6 i).1 ∧ σ 1 2 = (a2PairE6 i).2 := by
  obtain ⟨v, h1, h2⟩ := exists_weyl_a2Pair_E6 (isA2Pair_a2PairE6 i)
  refine ⟨_, _, (e6Std_frame K).transport v, ?_, ?_⟩
  · show v • chainRoot chain13 0 1 = _
    rw [chainRoot13_zero_one]
    exact h1
  · show v • chainRoot chain13 1 2 = _
    rw [chainRoot13_one_two]
    exact h2

theorem a2Roots_neg {α β : Fin Tag.E6.rank → ℤ} :
    ∀ γ ∈ a2Roots α β, -γ ∈ a2Roots α β := by
  intro γ hγ
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [a2Roots]

theorem theta_rootSpan_a2PairE6_two {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : Function.Surjective Fr) :
    (rootSpan Tag.E6 Ω (a2Roots (a2PairE6 2).1 (a2PairE6 2).2)).map
        (CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.theta Fr) =
      rootSpan Tag.E6 Ω (a2Roots (a2PairE6 2).1 (a2PairE6 2).2) := by
  change (rootSpan TwistTag.E6.tag Ω (a2Roots (a2PairE6 2).1 (a2PairE6 2).2)).map
      (twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) Ω
        CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0) Fr) =
    rootSpan TwistTag.E6.tag Ω (a2Roots (a2PairE6 2).1 (a2PairE6 2).2)
  rw [map_twFrob_rootSpan TwistTag.E6 hq
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0
    (a2Roots_isRoot (isA2Pair_a2PairE6 2))]
  congr 1
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    change CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0 •
      permLattice TwistTag.E6.perm δ ∈ a2Roots (a2PairE6 2).1 (a2PairE6 2).2
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0_smul_permLattice]
    exact a2Roots_neg δ hδ
  · intro hγ
    refine ⟨-γ, a2Roots_neg γ hγ, ?_⟩
    change CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0 •
      permLattice TwistTag.E6.perm (-γ) = γ
    rw [permLattice_neg, smul_neg,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.twE6W0_smul_permLattice, neg_neg]

end CFSG.StandardType.NoOffTwE6Three
