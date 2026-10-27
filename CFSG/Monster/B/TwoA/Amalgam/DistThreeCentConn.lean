module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.LieType.Chevalley.CosetBuilding

theorem chamberRoot_mem_rootClass
    (x : C2E6Std.stdChamber) : chamberRoot x ∈ rootClass := by
  induction x using QuotientGroup.induction_on with
  | H g => exact (mem_rootClass_iff _).2 ⟨g, (chamberRoot_mk g).symm⟩

theorem chamberRoot_eq_or_commute
    {x y : C2E6Std.stdChamber} {i : Fin 4}
    (h : stdDistance x y = ncs.simple i) :
    chamberRoot x = chamberRoot y ∨ Commute (chamberRoot x) (chamberRoot y) := by
  have hδ := isWeylDistanceBuilding_stdDistance
  by_cases hi : i ∈ firstJ
  · left
    have hy : y ∈ residue ncs stdDistance firstJ x := Relation.ReflTransGen.single ⟨i, hi, h⟩
    exact (chamberRoot_eq_iff x y).2
      (CFSG.Monster.B.Geometry.residue_eq_of_mem hδ hy).symm
  · right
    have hi0 : i ∈ FourthResidue.fourthJ := by
      revert hi
      fin_cases i <;> simp [firstJ, FourthResidue.fourthJ]
    have hy : y ∈ residue ncs stdDistance FourthResidue.fourthJ x :=
      Relation.ReflTransGen.single ⟨i, hi0, h⟩
    have hR := (exists_typeFour_iff_commute ⟨residue ncs stdDistance firstJ x, x, rfl⟩
      ⟨residue ncs stdDistance firstJ y, y, rfl⟩).1
      ⟨residue ncs stdDistance FourthResidue.fourthJ x, ⟨x, rfl⟩,
        ⟨x, CFSG.Monster.B.Geometry.self_mem_residue firstJ x,
          CFSG.Monster.B.Geometry.self_mem_residue _ x⟩,
        ⟨y, CFSG.Monster.B.Geometry.self_mem_residue firstJ y, hy⟩⟩
    rwa [vertexRoot_eq _ rfl, vertexRoot_eq _ rfl] at hR

theorem induce_neighborSet_connected
    (w : CVert) :
    (cgraph.induce (cgraph.neighborSet w)).Connected := by
  obtain ⟨M, -⟩ := exists_rootModel w
  set H := cgraph.induce (cgraph.neighborSet w)
  let pt : C2E6Std.stdChamber → cgraph.neighborSet w := fun x =>
    M.iv.symm ⟨chamberRoot x, chamberRoot_mem_rootClass x⟩
  have hpt : ∀ x, (M.iv (pt x) : stdGroup) = chamberRoot x := fun x => by
    simp only [pt, Equiv.apply_symm_apply]
  have step : ∀ {x y : C2E6Std.stdChamber} {i : Fin 4}, stdDistance x y = ncs.simple i →
      H.Reachable (pt x) (pt y) := by
    intro x y i h
    by_cases hxy : pt x = pt y
    · rw [hxy]
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.comap_adj, Function.Embedding.subtype_apply,
        Function.Embedding.subtype_apply, M.adj_iff _ _ hxy, hpt, hpt]
      rcases chamberRoot_eq_or_commute h with e | e
      · exact absurd (by simp only [pt, e]) hxy
      · exact e
  have hreach : ∀ x y : C2E6Std.stdChamber, H.Reachable (pt x) (pt y) := by
    intro x y
    have hy : y ∈ residue ncs stdDistance Set.univ x := by
      rw [CFSG.Monster.B.Geometry.residue_univ isWeylDistanceBuilding_stdDistance]
      trivial
    induction hy with
    | refl => rfl
    | tail _ hbc ih =>
      obtain ⟨i, -, hi⟩ := hbc
      exact ih.trans (step hi)
  have hsurj : ∀ z : cgraph.neighborSet w, ∃ x, pt x = z := by
    intro z
    obtain ⟨g, hg⟩ := (mem_rootClass_iff _).1 (M.iv z).2
    refine ⟨(g : C2E6Std.stdChamber), M.iv.injective ?_⟩
    apply Subtype.ext
    rw [hpt, chamberRoot_mk, hg]
  have : Nonempty (cgraph.neighborSet w) := ⟨pt ((1 : stdGroup) : C2E6Std.stdChamber)⟩
  refine ⟨fun z z' => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj z
  obtain ⟨y, rfl⟩ := hsurj z'
  exact hreach x y

end CFSG.Monster.B.TwoA.Amalgam
