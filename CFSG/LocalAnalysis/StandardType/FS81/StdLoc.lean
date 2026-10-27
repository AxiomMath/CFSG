module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def FS81HypALoc {G : Type} [Group G] [Finite G] (b₀ : G) (K : Subgroup G) : Prop :=
  orderOf b₀ = 3 ∧
  K ≤ Subgroup.centralizer ({b₀} : Set G) ∧
    (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ Subgroup.center K = ⊥ ∧
    LargeEvenMarking K (fun lab _ _ _ _ _ => FSLab lab) ∧
  (∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S) ∧
  True ∧ True

@[expose] def HypSetupLoc {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (m : ℕ) :
    Prop :=
  FS81HypALoc b₀ K ∧ IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E ∧ b₀ ∈ E ∧
    Nat.card E = 3 ^ m ∧ 7 ≤ m ∧ 2 ^ m * m.factorial < Nat.card (ggAutomizer ⊤ E)

@[expose] def StdLoc {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row) :
    Prop :=
  True ∧ HypSetupLoc b₀ K E r.m ∧ CanonPosition b₀ K E r

theorem StdAssumptions.toLoc {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {r : Row} (h : StdAssumptions b₀ K E r) : StdLoc b₀ K E r := by
  obtain ⟨-, ⟨⟨h1, h2, h3, h4, h5, h6, -, -⟩, h7, h8, h9, h10, h11⟩, h12⟩ := h
  exact ⟨trivial, ⟨⟨h1, h2, h3, h4, h5, h6, trivial, trivial⟩, h7, h8, h9, h10, h11⟩, h12⟩

end CFSG.StandardType.FrameRoute.FS81
