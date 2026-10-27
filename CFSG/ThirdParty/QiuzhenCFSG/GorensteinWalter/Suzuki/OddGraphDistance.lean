module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphGlobal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Intrinsic distance layers in the Suzuki commuting graph

The fibre-four and fibre-two layers are respectively the exact graph-distance
two and graph-distance three layers.  These intrinsic predicates are stable
under every graph automorphism and allow the rooted intersection array to be
transported to an arbitrary vertex.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Two vertices have a common neighbour. -/
@[expose] public def commutingGraphHasCommonNeighbor
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) : Prop :=
  ∃ X : UConjugates c,
    (commutingGraph c).Adj A X ∧ (commutingGraph c).Adj X B

/-- Exact graph distance two. -/
@[expose] public def commutingGraphDistTwo
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) : Prop :=
  A ≠ B ∧ ¬ (commutingGraph c).Adj A B ∧
    commutingGraphHasCommonNeighbor c A B

/-- Exact graph distance three in this diameter-three graph. -/
@[expose] public def commutingGraphDistThree
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) : Prop :=
  A ≠ B ∧ ¬ (commutingGraph c).Adj A B ∧
    ¬ commutingGraphHasCommonNeighbor c A B

/-- Having a common neighbour is symmetric in the two endpoints. -/
public theorem commutingGraphHasCommonNeighbor_comm
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    commutingGraphHasCommonNeighbor c A B ↔
      commutingGraphHasCommonNeighbor c B A := by
  constructor
  · rintro ⟨X, hAX, hXB⟩
    exact ⟨X, hXB.symm, hAX.symm⟩
  · rintro ⟨X, hBX, hXA⟩
    exact ⟨X, hXA.symm, hBX.symm⟩

/-- Exact distance two is symmetric. -/
public theorem commutingGraphDistTwo_comm
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    commutingGraphDistTwo c A B ↔ commutingGraphDistTwo c B A := by
  constructor
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨hne.symm, fun h => hAdj h.symm,
      (commutingGraphHasCommonNeighbor_comm c A B).mp hcommon⟩
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨hne.symm, fun h => hAdj h.symm,
      (commutingGraphHasCommonNeighbor_comm c A B).mpr hcommon⟩

/-- Exact distance three is symmetric. -/
public theorem commutingGraphDistThree_comm
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (A B : UConjugates c) :
    commutingGraphDistThree c A B ↔ commutingGraphDistThree c B A := by
  constructor
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨hne.symm, fun h => hAdj h.symm,
      fun h => hcommon ((commutingGraphHasCommonNeighbor_comm c A B).mpr h)⟩
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨hne.symm, fun h => hAdj h.symm,
      fun h => hcommon ((commutingGraphHasCommonNeighbor_comm c A B).mp h)⟩

public theorem commutingGraphHasCommonNeighbor_smul_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (A B : UConjugates c) :
    commutingGraphHasCommonNeighbor c (g • A) (g • B) ↔
      commutingGraphHasCommonNeighbor c A B := by
  constructor
  · rintro ⟨X, hAX, hXB⟩
    refine ⟨g⁻¹ • X, ?_, ?_⟩
    · have h := (commutingGraph.adj_smul_iff c g⁻¹ (g • A) X).mpr hAX
      simpa only [← mul_smul, inv_mul_cancel, one_smul] using h
    · have h := (commutingGraph.adj_smul_iff c g⁻¹ X (g • B)).mpr hXB
      simpa only [← mul_smul, inv_mul_cancel, one_smul] using h
  · rintro ⟨X, hAX, hXB⟩
    exact ⟨g • X,
      (commutingGraph.adj_smul_iff c g A X).mpr hAX,
      (commutingGraph.adj_smul_iff c g X B).mpr hXB⟩

public theorem commutingGraphDistTwo_smul_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (A B : UConjugates c) :
    commutingGraphDistTwo c (g • A) (g • B) ↔
      commutingGraphDistTwo c A B := by
  constructor
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨fun h => hne (congrArg (fun X => g • X) h),
      fun h => hAdj ((commutingGraph.adj_smul_iff c g A B).mpr h),
      (commutingGraphHasCommonNeighbor_smul_iff c g A B).mp hcommon⟩
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨(MulAction.injective g).ne hne,
      fun h => hAdj ((commutingGraph.adj_smul_iff c g A B).mp h),
      (commutingGraphHasCommonNeighbor_smul_iff c g A B).mpr hcommon⟩

public theorem commutingGraphDistThree_smul_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (A B : UConjugates c) :
    commutingGraphDistThree c (g • A) (g • B) ↔
      commutingGraphDistThree c A B := by
  constructor
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨fun h => hne (congrArg (fun X => g • X) h),
      fun h => hAdj ((commutingGraph.adj_smul_iff c g A B).mpr h),
      fun h => hcommon ((commutingGraphHasCommonNeighbor_smul_iff c g A B).mpr h)⟩
  · rintro ⟨hne, hAdj, hcommon⟩
    exact ⟨(MulAction.injective g).ne hne,
      fun h => hAdj ((commutingGraph.adj_smul_iff c g A B).mp h),
      fun h => hcommon ((commutingGraphHasCommonNeighbor_smul_iff c g A B).mp h)⟩

private theorem rootLayer_ne_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    {V : UConjugates c} {n : ℕ}
    (hV : (cosetLineEquiv hmin c hfirst).symm V ≠
      cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat
        ((cosetLineEquiv hmin c hfirst).symm V)) = n) :
    V ≠ UConjugates.base c := by
  intro hbase
  apply hV.1
  rw [hbase]
  apply (cosetLineEquiv hmin c hfirst).injective
  rw [(cosetLineEquiv hmin c hfirst).apply_symm_apply,
    cosetLineEquiv_base hmin c hfirst]

/-- The 12-point fibre-four layer is exactly distance two from the root. -/
public theorem firstCase_mem_rootLayerFour_iff_distTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c) :
    V ∈ firstCaseRootLayerFour hmin c hfirst ↔
      commutingGraphDistTwo c (UConjugates.base c) V := by
  constructor
  · intro hV
    refine ⟨(rootLayer_ne_base hmin c hfirst hV).symm, ?_, ?_⟩
    · intro hAdj
      have hAdj' := (commutingGraph_adj_iff c _ _).mp hAdj
      have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
        hmin c hfirst d V).mp ⟨hAdj'.1.symm, hAdj'.2⟩
      have hbad : (4 : ℕ) = 0 := hV.2.symm.trans hzero.2
      omega
    · have hcard := firstCase_rootLayerFour_rootNeighbor_card_one
        hmin c hfirst d V hV
      obtain ⟨X⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
      refine ⟨X.1.1, ?_, X.2⟩
      exact (commutingGraph_adj_iff c _ _).mpr
        ⟨X.1.2.1.symm, X.1.2.2⟩
  · rintro ⟨hVne, hnotAdj, X, hbaseX, hXV⟩
    have hX' := (commutingGraph_adj_iff c _ _).mp hbaseX
    let XN : lineNeighborSet c := ⟨X, ⟨hX'.1.symm, hX'.2⟩⟩
    rcases firstCase_root_partition hmin c hfirst d V with
      hbase | hN | hT | hF
    · exact False.elim (hVne hbase.symm)
    · exact False.elim (hnotAdj ((commutingGraph_adj_iff c _ _).mpr
        ⟨hN.1.symm, hN.2⟩))
    · exact False.elim (firstCase_rootNeighbor_not_adjacent_rootLayerTwo
        hmin c hfirst d XN V hT hXV)
    · exact hF

/-- The 18-point fibre-two layer is exactly distance three from the root. -/
public theorem firstCase_mem_rootLayerTwo_iff_distThree
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c) :
    V ∈ firstCaseRootLayerTwo hmin c hfirst ↔
      commutingGraphDistThree c (UConjugates.base c) V := by
  constructor
  · intro hV
    refine ⟨(rootLayer_ne_base hmin c hfirst hV).symm, ?_, ?_⟩
    · intro hAdj
      have hAdj' := (commutingGraph_adj_iff c _ _).mp hAdj
      have hzero := (firstCase_mem_lineNeighbors_iff_cosetLayer_zero
        hmin c hfirst d V).mp ⟨hAdj'.1.symm, hAdj'.2⟩
      have hbad : (2 : ℕ) = 0 := hV.2.symm.trans hzero.2
      omega
    · rintro ⟨X, hbaseX, hXV⟩
      have hX' := (commutingGraph_adj_iff c _ _).mp hbaseX
      let XN : lineNeighborSet c := ⟨X, ⟨hX'.1.symm, hX'.2⟩⟩
      exact firstCase_rootNeighbor_not_adjacent_rootLayerTwo
        hmin c hfirst d XN V hV hXV
  · rintro ⟨hVne, hnotAdj, hnoCommon⟩
    rcases firstCase_root_partition hmin c hfirst d V with
      hbase | hN | hT | hF
    · exact False.elim (hVne hbase.symm)
    · exact False.elim (hnotAdj ((commutingGraph_adj_iff c _ _).mpr
        ⟨hN.1.symm, hN.2⟩))
    · exact hT
    · exfalso
      apply hnoCommon
      have hcard := firstCase_rootLayerFour_rootNeighbor_card_one
        hmin c hfirst d V hF
      obtain ⟨X⟩ := (Nat.card_eq_one_iff_unique.mp hcard).2
      exact ⟨X.1.1,
        (commutingGraph_adj_iff c _ _).mpr ⟨X.1.2.1.symm, X.1.2.2⟩,
        X.2⟩

private def smulPredicateEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G)
    (P Q : UConjugates c → Prop)
    (hPQ : ∀ Y : UConjugates c, P Y ↔ Q (g • Y)) :
    {Y : UConjugates c // P Y} ≃ {Y : UConjugates c // Q Y} where
  toFun Y := ⟨g • Y.1, (hPQ Y.1).mp Y.2⟩
  invFun Y := ⟨g⁻¹ • Y.1, by
    apply (hPQ (g⁻¹ • Y.1)).mpr
    simpa only [← mul_smul, mul_inv_cancel, one_smul] using Y.2⟩
  left_inv Y := by
    apply Subtype.ext
    change g⁻¹ • (g • Y.1) = Y.1
    rw [← mul_smul]
    simp
  right_inv Y := by
    apply Subtype.ext
    change g • (g⁻¹ • Y.1) = Y.1
    rw [← mul_smul]
    simp

private def smulIncidenceEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G)
    (X X' : UConjugates c) (hX : g • X = X')
    (P Q : UConjugates c → Prop)
    (hPQ : ∀ Y : UConjugates c, P Y ↔ Q (g • Y)) :
    {Y : {Y : UConjugates c // P Y} // (commutingGraph c).Adj X Y.1} ≃
      {Y : {Y : UConjugates c // Q Y} // (commutingGraph c).Adj X' Y.1} where
  toFun Y := ⟨smulPredicateEquiv c g P Q hPQ Y.1, by
    have h := (commutingGraph.adj_smul_iff c g X Y.1.1).mpr Y.2
    change (commutingGraph c).Adj X' (g • Y.1.1)
    simpa only [hX] using h⟩
  invFun Y := ⟨(smulPredicateEquiv c g P Q hPQ).symm Y.1, by
    have h := (commutingGraph.adj_smul_iff c g⁻¹ X' Y.1.1).mpr Y.2
    have hXinv : g⁻¹ • X' = X := by
      calc
        g⁻¹ • X' = g⁻¹ • (g • X) := by rw [hX]
        _ = X := by rw [← mul_smul]; simp
    change (commutingGraph c).Adj X (g⁻¹ • Y.1.1)
    simpa only [hXinv] using h⟩
  left_inv Y := by
    apply Subtype.ext
    exact (smulPredicateEquiv c g P Q hPQ).left_inv Y.1
  right_inv Y := by
    apply Subtype.ext
    exact (smulPredicateEquiv c g P Q hPQ).right_inv Y.1

private def adjacencySymmEquiv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : UConjugates c)
    (P : UConjugates c → Prop) :
    {Y : {Y : UConjugates c // P Y} // (commutingGraph c).Adj X Y.1} ≃
      {Y : {Y : UConjugates c // P Y} // (commutingGraph c).Adj Y.1 X} where
  toFun Y := ⟨Y.1, Y.2.symm⟩
  invFun Y := ⟨Y.1, Y.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every distance-two vertex has three neighbours at distance three from the
chosen root. -/
public theorem firstCase_distTwo_distThree_neighbors_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (A X : UConjugates c) (hX : commutingGraphDistTwo c A X) :
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistThree c A Y} //
      (commutingGraph c).Adj X Y.1} = 3 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let X0 : UConjugates c := g⁻¹ • X
  have hA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hX0dist : commutingGraphDistTwo c (UConjugates.base c) X0 := by
    have h := (commutingGraphDistTwo_smul_iff c g⁻¹ A X).mpr hX
    simpa only [X0, hA0] using h
  have hX0F := (firstCase_mem_rootLayerFour_iff_distTwo
    hmin c hfirst d X0).mpr hX0dist
  have hXmap : g • X0 = X := by
    dsimp [X0]
    rw [← mul_smul]
    simp
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerTwo hmin c hfirst ↔
        commutingGraphDistThree c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerTwo_iff_distThree hmin c hfirst d]
    have h := commutingGraphDistThree_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulIncidenceEquiv c g X0 X hXmap
    (fun Y => Y ∈ firstCaseRootLayerTwo hmin c hfirst)
    (fun Y => commutingGraphDistThree c A Y) hPred
  calc
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistThree c A Y} //
        (commutingGraph c).Adj X Y.1} =
        Nat.card {Y : {Y : UConjugates c //
          Y ∈ firstCaseRootLayerTwo hmin c hfirst} //
            (commutingGraph c).Adj X0 Y.1} := (Nat.card_congr e).symm
    _ = 3 := (firstCase_rootLayerFour_two_incidence hmin c hfirst d).1 X0 hX0F

/-- A distance-two layer is a coclique. -/
public theorem firstCase_distTwo_internal_neighbors_card_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (A X : UConjugates c) (hX : commutingGraphDistTwo c A X) :
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
      (commutingGraph c).Adj X Y.1} = 0 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let X0 : UConjugates c := g⁻¹ • X
  have hA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hX0dist : commutingGraphDistTwo c (UConjugates.base c) X0 := by
    have h := (commutingGraphDistTwo_smul_iff c g⁻¹ A X).mpr hX
    simpa only [X0, hA0] using h
  have hX0F := (firstCase_mem_rootLayerFour_iff_distTwo
    hmin c hfirst d X0).mpr hX0dist
  have hXmap : g • X0 = X := by
    dsimp [X0]
    rw [← mul_smul]
    simp
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerFour hmin c hfirst ↔
        commutingGraphDistTwo c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerFour_iff_distTwo hmin c hfirst d]
    have h := commutingGraphDistTwo_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulIncidenceEquiv c g X0 X hXmap
    (fun Y => Y ∈ firstCaseRootLayerFour hmin c hfirst)
    (fun Y => commutingGraphDistTwo c A Y) hPred
  calc
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
        (commutingGraph c).Adj X Y.1} =
        Nat.card {Y : {Y : UConjugates c //
          Y ∈ firstCaseRootLayerFour hmin c hfirst} //
            (commutingGraph c).Adj X0 Y.1} := (Nat.card_congr e).symm
    _ = 0 := firstCase_rootLayerFour_internal_neighbors_card_zero
      hmin c hfirst d X0 hX0F

/-- Two vertices in the same distance-two layer are never adjacent. -/
public theorem firstCase_distTwo_not_adjacent
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A X Y : UConjugates c}
    (hX : commutingGraphDistTwo c A X)
    (hY : commutingGraphDistTwo c A Y) :
    ¬ (commutingGraph c).Adj X Y := by
  intro hXY
  let z : {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
      (commutingGraph c).Adj X Y.1} := ⟨⟨Y, hY⟩, hXY⟩
  have hcard := firstCase_distTwo_internal_neighbors_card_zero
    hmin c hfirst d A X hX
  let := Fintype.ofFinite
    {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
      (commutingGraph c).Adj X Y.1}
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff] at hcard
  exact hcard.false z

/-- Every distance-three vertex has two neighbours at distance two from the
chosen root. -/
public theorem firstCase_distThree_distTwo_neighbors_card_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (A X : UConjugates c) (hX : commutingGraphDistThree c A X) :
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
      (commutingGraph c).Adj X Y.1} = 2 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let X0 : UConjugates c := g⁻¹ • X
  have hA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hX0dist : commutingGraphDistThree c (UConjugates.base c) X0 := by
    have h := (commutingGraphDistThree_smul_iff c g⁻¹ A X).mpr hX
    simpa only [X0, hA0] using h
  have hX0T := (firstCase_mem_rootLayerTwo_iff_distThree
    hmin c hfirst d X0).mpr hX0dist
  have hXmap : g • X0 = X := by
    dsimp [X0]
    rw [← mul_smul]
    simp
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerFour hmin c hfirst ↔
        commutingGraphDistTwo c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerFour_iff_distTwo hmin c hfirst d]
    have h := commutingGraphDistTwo_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulIncidenceEquiv c g X0 X hXmap
    (fun Y => Y ∈ firstCaseRootLayerFour hmin c hfirst)
    (fun Y => commutingGraphDistTwo c A Y) hPred
  have hroot : Nat.card {Y : {Y : UConjugates c //
      Y ∈ firstCaseRootLayerFour hmin c hfirst} //
        (commutingGraph c).Adj X0 Y.1} = 2 := by
    rw [Nat.card_congr (adjacencySymmEquiv c X0
      (fun Y => Y ∈ firstCaseRootLayerFour hmin c hfirst))]
    exact (firstCase_rootLayerFour_two_incidence hmin c hfirst d).2 X0 hX0T
  calc
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistTwo c A Y} //
        (commutingGraph c).Adj X Y.1} =
        Nat.card {Y : {Y : UConjugates c //
          Y ∈ firstCaseRootLayerFour hmin c hfirst} //
            (commutingGraph c).Adj X0 Y.1} := (Nat.card_congr e).symm
    _ = 2 := hroot

/-- Every distance-three vertex has two neighbours in the distance-three
layer. -/
public theorem firstCase_distThree_internal_neighbors_card_two
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (A X : UConjugates c) (hX : commutingGraphDistThree c A X) :
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistThree c A Y} //
      (commutingGraph c).Adj X Y.1} = 2 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let X0 : UConjugates c := g⁻¹ • X
  have hA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hX0dist : commutingGraphDistThree c (UConjugates.base c) X0 := by
    have h := (commutingGraphDistThree_smul_iff c g⁻¹ A X).mpr hX
    simpa only [X0, hA0] using h
  have hX0T := (firstCase_mem_rootLayerTwo_iff_distThree
    hmin c hfirst d X0).mpr hX0dist
  have hXmap : g • X0 = X := by
    dsimp [X0]
    rw [← mul_smul]
    simp
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerTwo hmin c hfirst ↔
        commutingGraphDistThree c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerTwo_iff_distThree hmin c hfirst d]
    have h := commutingGraphDistThree_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulIncidenceEquiv c g X0 X hXmap
    (fun Y => Y ∈ firstCaseRootLayerTwo hmin c hfirst)
    (fun Y => commutingGraphDistThree c A Y) hPred
  calc
    Nat.card {Y : {Y : UConjugates c // commutingGraphDistThree c A Y} //
        (commutingGraph c).Adj X Y.1} =
        Nat.card {Y : {Y : UConjugates c //
          Y ∈ firstCaseRootLayerTwo hmin c hfirst} //
            (commutingGraph c).Adj X0 Y.1} := (Nat.card_congr e).symm
    _ = 2 := firstCase_rootLayerTwo_internal_neighbors_card_two
      hmin c hfirst d X0 hX0T

/-- Every vertex has twelve vertices at distance two. -/
public theorem firstCase_distTwo_layer_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (A : UConjugates c) :
    Nat.card {Y : UConjugates c // commutingGraphDistTwo c A Y} = 12 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerFour hmin c hfirst ↔
        commutingGraphDistTwo c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerFour_iff_distTwo hmin c hfirst d]
    have h := commutingGraphDistTwo_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulPredicateEquiv c g
    (fun Y => Y ∈ firstCaseRootLayerFour hmin c hfirst)
    (fun Y => commutingGraphDistTwo c A Y) hPred
  calc
    Nat.card {Y : UConjugates c // commutingGraphDistTwo c A Y} =
        Nat.card {Y : UConjugates c //
          Y ∈ firstCaseRootLayerFour hmin c hfirst} := (Nat.card_congr e).symm
    _ = 12 := firstCaseRootLayerFour_card hmin c hfirst d

/-- Every vertex has eighteen vertices at distance three. -/
public theorem firstCase_distThree_layer_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (A : UConjugates c) :
    Nat.card {Y : UConjugates c // commutingGraphDistThree c A Y} = 18 := by
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  have hPred : ∀ Y : UConjugates c,
      Y ∈ firstCaseRootLayerTwo hmin c hfirst ↔
        commutingGraphDistThree c A (g • Y) := by
    intro Y
    rw [firstCase_mem_rootLayerTwo_iff_distThree hmin c hfirst d]
    have h := commutingGraphDistThree_smul_iff c g (UConjugates.base c) Y
    simpa only [hgA] using h.symm
  let e := smulPredicateEquiv c g
    (fun Y => Y ∈ firstCaseRootLayerTwo hmin c hfirst)
    (fun Y => commutingGraphDistThree c A Y) hPred
  calc
    Nat.card {Y : UConjugates c // commutingGraphDistThree c A Y} =
        Nat.card {Y : UConjugates c //
          Y ∈ firstCaseRootLayerTwo hmin c hfirst} := (Nat.card_congr e).symm
    _ = 18 := firstCaseRootLayerTwo_card hmin c hfirst d

end CFSG.GorensteinWalter
