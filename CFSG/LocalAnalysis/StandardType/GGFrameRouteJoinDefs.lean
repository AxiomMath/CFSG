module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

section Join

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveWeylAtJoin (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ 𝒦 : Finset (Subgroup G), GGNbrSet p B x D J 𝒦 ∧ 𝒦.Nonempty ∧
    GGWeylOfType p M (ggAutomizerJoin L Bs 𝒦)

end Join

@[expose] def GGFrameEndLabelJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .D ∧ lab.rank = 6) ∨
          (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1)) ∧
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .twA ∧ lab.rank = 8) ∨
          (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1))

@[expose] def GGFSxEndsCardJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇ →
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B) ∧
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B)

@[expose] def GGFSyNonFSPointJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₇ →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)) ∧
    (GGSecFiveWeylAtJoin 3 B Bs x L D J CoxeterMatrix.E₈ →
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ =>
            ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1))

@[expose] def GGFrameRouteJoinInputs : Prop :=
  FS81ThmACRankInput ∧ LSS92TorusMaxInput ∧ GGFrameEndLabelJoinInput ∧ GGFSxEndsCardJoinInput ∧
    GGFSyNonFSPointJoinInput

end CFSG.StandardType.FrameRoute

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveWeylAt.toJoin {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ι : Type} {M : CoxeterMatrix ι} (h : GGSecFiveWeylAt p B Bs x L D J M) :
    FrameRoute.GGSecFiveWeylAtJoin p B Bs x L D J M := by
  obtain ⟨y, K, hN, hW⟩ := h
  refine ⟨{K}, ⟨by simp, fun K' hK' => ?_⟩, Finset.singleton_nonempty K, ?_⟩
  · rw [Finset.mem_singleton] at hK'
    subst hK'
    exact ⟨y, hN⟩
  · simpa only [ggAutomizerJoin, Finset.iSup_singleton] using hW

@[expose] def GGSecFiveE78QTwoLabelInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L → p = 3 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        ((∃ e' : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e') ∨
          (∃ e' : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e')) →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
          GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → lab.n < 2

end CFSG.StandardType

end
