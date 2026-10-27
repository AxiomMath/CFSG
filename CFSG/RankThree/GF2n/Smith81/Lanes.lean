module

public import CFSG.RankThree.GF2n.Smith81.Statement

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

section Lanes

variable (M Q Z B : Subgroup G)

@[expose] def SmithLaneTI : Prop :=
  (∀ n : ℕ, CaseD1 Q Z n →
    CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 n ∧ OuterOnFStar G) ∧
  (CaseD2 M Q Z B →
    (NoA2 Q Z (LB M Q B) → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      CFSG.Blueprint.LieModel (FStar G) .G2 0 2 f) ∧
    (¬ NoA2 Q Z (LB M Q B) → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      CFSG.Blueprint.LieModel (FStar G) .PSL 4 2 f ∧ OuterOnFStar G)) ∧
  (CaseD3 M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .trialityD4 0 2 f)

@[expose] def SmithLaneOrth : Prop :=
  (∀ t : G, CtxD4 M Q Z B t → CaseE1Plus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaPlus 4 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE1Minus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaMinus 4 2 f) ∧
  (∀ (t : G) (m : ℕ), CtxD4 M Q Z B t → CaseE2Plus M Q Z B t m → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaPlus (m + 2) 2 f) ∧
  (∀ (t : G) (m : ℕ), CtxD4 M Q Z B t → CaseE2Minus M Q Z B t m → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaMinus (m + 2) 2 f)

@[expose] def SmithLaneE : Prop :=
  (∀ t : G, CtxD4 M Q Z B t → CaseE3U M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .twistedE6 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE3L M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E6 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE4 M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E7 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE5 M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E8 0 2 f)

@[expose] def SmithLaneLin : Prop :=
  ¬ IsTIMod M Q (LB M Q B) → ∀ n : ℕ, CaseE6 M Q Z B n → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f ∧ OuterOnFStar G

theorem smithConclusion_iff_lanes :
    SmithConclusion M Q Z B ↔
      SmithLaneTI M Q Z B ∧ SmithLaneOrth M Q Z B ∧ SmithLaneE M Q Z B ∧ SmithLaneLin M Q Z B := by
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
    exact ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩, a12⟩
  · rintro ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩, a12⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

end Lanes

end CFSG.RankThree.GF2n.Smith81
