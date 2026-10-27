module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveNotStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubNotNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySixA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFactsSmallRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzFieldKFacts
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.GroupTheory.PrimeOrderSylowNormalizer
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQOuter
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.GroupTheory.SylowNormalizedByPGroup
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Connected
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12b
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sm
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115Two
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.SmithB42Vacuous
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.K1320.L4CentT8
public import CFSG.RankThree.PartOne.K1320.L4Core
public import CFSG.RankThree.PartOne.K1320.L4Sl3
public import CFSG.RankThree.PartOne.U4F.Main
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.ThinCatalog.OuterThreeFree
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement
open CFSG.GroupTheory (exists_orderOf_eq_prime_mem_normalizer_inf_of_dihedral
  exists_orderOf_eq_prime_mem_normalizer_sup_of_dihedral)

variable {G : Type} [Group G] [Finite G]

@[expose] def GapWitness (D : Data G) (X : Subgroup G) (p : ℕ) (y : G) : Prop :=
  y ∈ D.M ∧ y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p ∧
    y ∈ Subgroup.normalizer
      ((D.T ⊓ (X ⊔ F08.CentOverO2 D.M X) : Subgroup G) : Set G) ∧
    D.T ≤ Subgroup.normalizer
      ((Subgroup.zpowers y ⊔ (D.T ⊓ (X ⊔ F08.CentOverO2 D.M X)) : Subgroup G) : Set G)

@[expose] def S17_45A (D : Data G) (X : Subgroup G) (p r : ℕ) (y : G) : Prop :=
  ∃ A : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf r A
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ∧
    CFSG.ABGLocalTools.IsSylowOf r A X ∧ Permutes A D.T ∧
    Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) ∧
    A ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G) = ⊥

theorem pRank_centOverO2_le_one_of_not_strongly {D : Data G} {X E : Subgroup G} {p r : ℕ}
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (hp : p ∈ D.sig)
    (hXM : X ≤ D.M) (hMN : D.M ≤ Subgroup.normalizer (X : Set G))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hab : ∀ P : Sylow r (Bar2 X), IsMulCommutative (P : Subgroup (Bar2 X)))
    (hout : ¬ r ∣ (X ⊔ F08.CentOverO2 D.M X).relIndex D.M)
    (hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M)
    (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1 := by
  classical
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hpP⟩
  obtain ⟨R, hR, hER⟩ :=
    exists_sylow_le_centralizer_of_isMulCommutative (M := D.M) (X := X) (E := E)
      hr hr2 hXM hMN hab hout hEX hEel.isPGroup
  have hMcent : CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    exact hnotStrong (strongly_of_two_le_pRank_centralizer hSg h1219 h76 h614 hp hr hr2
      hR hEel hEcard hER hcon)
  calc CFSG.Open.pRank p (F08.CentOverO2 D.M X)
      ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
        pRank_centOverO2_le_pRank_inf_centralizer hXM hMN hpP hp2 hr hr2 hrp hEX hEel.isPGroup
    _ ≤ 1 := hMcent

theorem gap17_45_cyclicS_holds {D : Data G} {X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (φ : ↥D.M →* DihedralGroup p) (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hrank : CFSG.Open.pRank p (F08.CentOverO2 D.M X) ≤ 1)
    (hpK : ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)))
    (hy : ∃ y ∈ D.M, y ∉ X ⊔ F08.CentOverO2 D.M X ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) : ∃ y : G, GapWitness D X p y := by
  have hCM : F08.CentOverO2 D.M X ≤ D.M :=
    (Subgroup.closure_le D.M).mpr (fun x hx => hx.1)
  obtain ⟨b, hbM, hbN, hbord, hbTN⟩ :=
    exists_orderOf_eq_prime_mem_normalizer_inf_of_dihedral hp hp2 hXM hCM hMX φ hφ hker
      D.sylowM hrank hpK hy hK hKF
  exact exists_orderOf_eq_prime_mem_normalizer_sup_of_dihedral hp hp2 hXM hCM hMX φ hφ hker
    D.sylowM hrank hpK hbM hbN hbord hbTN

theorem s17_45_normalizes_borel {D : Data G} {X : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G)) :
    D.T ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).1
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) := hTM.trans hMX
  have hTS : D.T ≤ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
    intro t ht
    exact CFSG.ABGLocalTools.mem_normalizer_inf (Subgroup.le_normalizer ht) (hTX ht)
  intro t ht
  exact CFSG.ABGLocalTools.mem_normalizer_inf (hTX ht)
    (CFSG.ABGLocalTools.mem_normalizer_normalizer (hTS ht))

theorem s17_45_mem_normalizer_borel {D : Data G} {X : Subgroup G} {y : G}
    (hMX : D.M ≤ Subgroup.normalizer (X : Set G)) (hyM : y ∈ D.M)
    (hyTN : y ∈ Subgroup.normalizer
      ((D.T ⊓ (X ⊔ F08.CentOverO2 D.M X) : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer
      ((X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hyX : y ∈ Subgroup.normalizer (X : Set G) := hMX hyM
  have hTX_eq : X ⊓ (D.T ⊓ (X ⊔ F08.CentOverO2 D.M X)) = D.T ⊓ X := by
    rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left le_sup_left), inf_comm]
  have hyTX : y ∈ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
    rw [← hTX_eq]
    exact CFSG.ABGLocalTools.mem_normalizer_inf hyX hyTN
  exact CFSG.ABGLocalTools.mem_normalizer_inf hyX
    (CFSG.ABGLocalTools.mem_normalizer_normalizer hyTX)

theorem s17_45_exists_A_sylow {D : Data G} {X : Subgroup G} {p r : ℕ} {y : G}
    (hp : p.Prime) (hr : r.Prime) (hyord : orderOf y = p)
    (hyK : y ∈ Subgroup.normalizer
      ((X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hpK : ¬ p ∣ Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))) :
    ∃ A : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf r A
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ∧
      Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) := by
  classical
  have hyP : IsPGroup p (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hyord, pow_one]
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hyP
    (Subgroup.zpowers_le.mpr hyK) hpK
  exact ⟨((S : Subgroup ↥(X ⊓ Subgroup.normalizer
      ((D.T ⊓ X : Subgroup G) : Set G))).map
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)).subtype), ⟨S, rfl⟩, hS⟩

theorem s17_45_exists_A {D : Data G} {X : Subgroup G} {p r : ℕ} {y : G}
    (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2) (hy : GapWitness D X p y)
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hpK : ¬ p ∣ Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)))
    (hKrel : (D.T ⊓ X).relIndex
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2)
    (hKfact : (Nat.card ↥
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2)
    (hXfact : (Nat.card ↥X).factorization r = 2)
    (hcentK : Subgroup.centralizer (Subgroup.zpowers y : Set G) ⊓
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ D.T ⊓ X) :
    S17_45A D X p r y := by
  classical
  obtain ⟨hyM, hyN, hyord, hyTN, -⟩ := hy
  have : Fact r.Prime := ⟨hr⟩
  let K : Subgroup G := X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := s17_45_mem_normalizer_borel hMX hyM hyTN
  obtain ⟨A, hAsyl, hAinv⟩ := s17_45_exists_A_sylow hp hr hyord hyK hpK
  have hAcard : Nat.card A = r ^ 2 := by rw [hAsyl.card_eq, hKfact]
  have hAK : A ≤ K := hAsyl.le
  have hAX : A ≤ X := hAK.trans inf_le_left
  have hSylX : CFSG.ABGLocalTools.IsSylowOf r A X :=
    CFSG.ABGLocalTools.isSylowOf_of_card hAX (by rw [hAcard, hXfact])
  have hA2 : IsPGroup r A := hAsyl.isPGroup
  have hT2 : IsPGroup 2 ↥(D.T ⊓ X) := D.sylowM.isPGroup.to_le inf_le_left
  have hdisj : A ⊓ (D.T ⊓ X) = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 hr2 A (D.T ⊓ X) hA2 hT2).eq_bot
  have hAT : A ≤ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) :=
    hAK.trans inf_le_right
  have hsupK : A ⊔ (D.T ⊓ X) = K := by
    have hTKsub : D.T ⊓ X ≤ K := le_inf inf_le_right (Subgroup.le_normalizer)
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAK hTKsub) ?_
    have hrel : (D.T ⊓ X).relIndex K * Nat.card ↥(D.T ⊓ X) = Nat.card ↥K := by
      have h := Subgroup.relIndex_mul_card (D.T ⊓ X) K
      have heq : (D.T ⊓ X) ⊓ K = D.T ⊓ X := inf_eq_left.mpr hTKsub
      rw [show Nat.card ↥((D.T ⊓ X) ⊓ K) = Nat.card ↥(D.T ⊓ X) from
        congrArg (fun H : Subgroup G => Nat.card ↥H) heq] at h
      exact h
    rw [hKrel] at hrel
    have hcard : Nat.card ↥(A ⊔ (D.T ⊓ X)) * Nat.card ↥(A ⊓ (D.T ⊓ X)) =
        Nat.card ↥A * Nat.card ↥(D.T ⊓ X) :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAT
    rw [hdisj, Subgroup.card_bot, mul_one, hAcard] at hcard
    exact (hcard.trans hrel).ge
  have hTK : D.T ≤ Subgroup.normalizer (K : Set G) := s17_45_normalizes_borel hXM hMX
  have hTsup : D.T ≤ Subgroup.normalizer ((A ⊔ (D.T ⊓ X) : Subgroup G) : Set G) := by
    rw [hsupK]; exact hTK
  have hperm : Permutes A D.T :=
    TwelveNineteen.permutes_of_le_normalizer_sup (X := A) (R := D.T ⊓ X) (T := D.T)
      inf_le_left hTsup hAT
  refine ⟨A, hAsyl, hSylX, hperm, hAinv, ?_⟩
  have hle : A ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G) ≤ D.T ⊓ X := by
    refine (inf_le_inf_right _ hAK).trans ?_
    rw [inf_comm]
    exact hcentK
  exact le_bot_iff.mp ((le_inf inf_le_left hle).trans (le_of_eq hdisj))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
