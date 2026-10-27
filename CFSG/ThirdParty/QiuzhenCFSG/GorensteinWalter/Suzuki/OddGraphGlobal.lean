module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphIntersectionArray
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Global consequences of the Suzuki odd-graph intersection array

Conjugation makes the graph vertex- and edge-transitive.  Transporting the
rooted intersection array shows that the graph is triangle-free and that two
distinct vertices have at most one common neighbour.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every conjugate of `U` is obtained by moving the base vertex. -/
public theorem UConjugates.exists_smul_base
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (V : UConjugates c) :
    ∃ g : G, g • UConjugates.base c = V := by
  rcases V.2 with ⟨g, hV⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  rw [UConjugates.smul_def]
  change conjugateSubgroup c.U g = V.1
  exact hV.symm

/-- The conjugation action on graph vertices is transitive. -/
public theorem firstCase_commutingGraph_vertex_transitive
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (V W : UConjugates c) :
    ∃ g : G, g • V = W := by
  obtain ⟨a, ha⟩ := UConjugates.exists_smul_base c V
  obtain ⟨b, hb⟩ := UConjugates.exists_smul_base c W
  refine ⟨b * a⁻¹, ?_⟩
  calc
    (b * a⁻¹) • V = (b * a⁻¹) • (a • UConjugates.base c) := by rw [ha]
    _ = b • UConjugates.base c := by
      rw [← mul_smul]
      congr 1
      group
    _ = W := hb

/-- The commuting graph is triangle-free. -/
public theorem firstCase_commutingGraph_triangle_free
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A B C : UConjugates c}
    (hAB : (commutingGraph c).Adj A B)
    (hAC : (commutingGraph c).Adj A C) :
    ¬ (commutingGraph c).Adj B C := by
  intro hBC
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let B0 : UConjugates c := g⁻¹ • B
  let C0 : UConjugates c := g⁻¹ • C
  have hgA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hbaseB : (commutingGraph c).Adj (UConjugates.base c) B0 := by
    have h := (commutingGraph.adj_smul_iff c g⁻¹ A B).mpr hAB
    simpa only [B0, hgA0] using h
  have hbaseC : (commutingGraph c).Adj (UConjugates.base c) C0 := by
    have h := (commutingGraph.adj_smul_iff c g⁻¹ A C).mpr hAC
    simpa only [C0, hgA0] using h
  have hBC0 : (commutingGraph c).Adj B0 C0 := by
    exact (commutingGraph.adj_smul_iff c g⁻¹ B C).mpr hBC
  have hB' := (commutingGraph_adj_iff c _ _).mp hbaseB
  have hC' := (commutingGraph_adj_iff c _ _).mp hbaseC
  let BN : lineNeighborSet c := ⟨B0, ⟨hB'.1.symm, hB'.2⟩⟩
  let CN : lineNeighborSet c := ⟨C0, ⟨hC'.1.symm, hC'.2⟩⟩
  have hBC' := (commutingGraph_adj_iff c _ _).mp hBC0
  exact neighbor_coclique hmin c hfirst d BN CN hBC'.1 hBC'.2

/-- Distinct vertices have at most one common neighbour. -/
public theorem firstCase_commutingGraph_commonNeighbor_unique
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    {A C X Y : UConjugates c}
    (hAC : A ≠ C)
    (hAX : (commutingGraph c).Adj A X)
    (hXC : (commutingGraph c).Adj X C)
    (hAY : (commutingGraph c).Adj A Y)
    (hYC : (commutingGraph c).Adj Y C) :
    X = Y := by
  classical
  obtain ⟨g, hgA⟩ := UConjugates.exists_smul_base c A
  let C0 : UConjugates c := g⁻¹ • C
  let X0 : UConjugates c := g⁻¹ • X
  let Y0 : UConjugates c := g⁻¹ • Y
  have hgA0 : g⁻¹ • A = UConjugates.base c := by
    calc
      g⁻¹ • A = g⁻¹ • (g • UConjugates.base c) := by rw [hgA]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hbaseX : (commutingGraph c).Adj (UConjugates.base c) X0 := by
    have h := (commutingGraph.adj_smul_iff c g⁻¹ A X).mpr hAX
    simpa only [X0, hgA0] using h
  have hX0C0 : (commutingGraph c).Adj X0 C0 :=
    (commutingGraph.adj_smul_iff c g⁻¹ X C).mpr hXC
  have hbaseY : (commutingGraph c).Adj (UConjugates.base c) Y0 := by
    have h := (commutingGraph.adj_smul_iff c g⁻¹ A Y).mpr hAY
    simpa only [Y0, hgA0] using h
  have hY0C0 : (commutingGraph c).Adj Y0 C0 :=
    (commutingGraph.adj_smul_iff c g⁻¹ Y C).mpr hYC
  rcases firstCase_root_partition hmin c hfirst d C0 with hbase | hN | hT | hF
  · have hEq : A = C := by
      apply (MulAction.injective g⁻¹)
      have hC0 : g⁻¹ • C = UConjugates.base c := by
        simpa only [C0] using hbase
      exact hgA0.trans hC0.symm
    exact False.elim (hAC hEq)
  · let XN : lineNeighborSet c := ⟨X0, by
      have h := (commutingGraph_adj_iff c _ _).mp hbaseX
      exact ⟨h.1.symm, h.2⟩⟩
    let CN : lineNeighborSet c := ⟨C0, hN⟩
    have hXC' := (commutingGraph_adj_iff c _ _).mp hX0C0
    exact False.elim (neighbor_coclique hmin c hfirst d XN CN hXC'.1 hXC'.2)
  · let XN : lineNeighborSet c := ⟨X0, by
      have h := (commutingGraph_adj_iff c _ _).mp hbaseX
      exact ⟨h.1.symm, h.2⟩⟩
    exact False.elim
      (firstCase_rootNeighbor_not_adjacent_rootLayerTwo
        hmin c hfirst d XN C0 hT hX0C0)
  · let R := {Z : lineNeighborSet c // (commutingGraph c).Adj Z.1 C0}
    have hRcard : Nat.card R = 1 :=
      firstCase_rootLayerFour_rootNeighbor_card_one hmin c hfirst d C0 hF
    let XR : R := ⟨⟨X0, by
      have h := (commutingGraph_adj_iff c _ _).mp hbaseX
      exact ⟨h.1.symm, h.2⟩⟩, hX0C0⟩
    let YR : R := ⟨⟨Y0, by
      have h := (commutingGraph_adj_iff c _ _).mp hbaseY
      exact ⟨h.1.symm, h.2⟩⟩, hY0C0⟩
    let : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hRcard).1
    have hXY0 : X0 = Y0 := congrArg (fun Z : R => Z.1.1) (Subsingleton.elim XR YR)
    apply (MulAction.injective g⁻¹)
    exact hXY0

end CFSG.GorensteinWalter
