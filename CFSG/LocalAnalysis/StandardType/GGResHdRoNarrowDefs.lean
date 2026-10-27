module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorANarrow : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

@[expose] def GGTBTorLiftADepRows : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → 6 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R

@[expose] def GGTBJTwoNodeLargeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 10 ≤ X.rank) p J L →
        GGResTwoNodeSideDatum p Bs L J) ∧
      (GGResXDatum p Bs K → GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 10 ≤ X.rank) p J K →
        GGResTwoNodeSideDatum p Bs K J)

theorem ggTBTorANarrow_of_all (h : GGTBTorAll) : GGTBTorANarrow :=
  fun p hp hp2 lab hlab htag h6 hdvd hM =>
    h.1 p hp hp2 lab hlab htag (by omega) hdvd hM (by rintro ⟨-, h5, -⟩; omega)

theorem ggTBTorLiftADepRows_of_rows (h : GGTBTorLiftRows) : GGTBTorLiftADepRows :=
  fun p hp hp2 lab hlab htag h6 hdvd hM =>
    h p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
      (CoxeterMatrix.A lab.rank) hp hp2 hlab
      (GGTBTorRowAt.aDep htag (by omega) hdvd hM (by rintro ⟨-, h5, -⟩; omega))

theorem ggTBJTwoNodeLargeInput_of_input (h : GGTBJTwoNodeInput) : GGTBJTwoNodeLargeInput := by
  intro G _ _ p B Bs x L D J y K hH hp
  refine ⟨fun hX hrow => ?_, fun hX hrow => ?_⟩
  · obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    exact (h G p B Bs x L D J y K hH).1 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr.1⟩
  · obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    exact (h G p B Bs x L D J y K hH).2 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr.1⟩

end CFSG.StandardType

end
