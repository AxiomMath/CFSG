module

public import CFSG.RankThree.GF2n.Tim81.HBar
public import CFSG.RankThree.GF2n.Tim81.Setting

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def IsL2OrSzGroup (X : Type) [Group X] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2), 4 ≤ Fintype.card F ∧
      Nonempty (X ≃* SL(2, F))) ∨
    (∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2), 1 ≤ a ∧
      Fintype.card F = 2 ^ (2 * a + 1) ∧ Nonempty (X ≃* CFSG.Blueprint.suzukiGroup a F))

@[expose] def IsL2OrSz (V H : Subgroup G) : Prop :=
  IsL2OrSzGroup (HBar V H)

@[expose] def CentralTIStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T Z : Subgroup Y) [Z.Normal],
    Assembly.IsElemAbelian 2 T → Subgroup.normalClosure (T : Set Y) = ⊤ → IsTI T →
      WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)) → Z ≤ Subgroup.center Y →
      IsL2OrSzGroup (Y ⧸ Z) → Z = ⊥

@[expose] def Sec41Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), RootHyp M V → ∀ h : G,
    IsHMember M V (Pc M V ⊔ conjSubgroup h (Pc M V)) →
      IsL2OrSz V (Pc M V ⊔ conjSubgroup h (Pc M V))

@[expose] def KFactorization (M V H : Subgroup G) (h₀ : G) : Prop :=
  kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ kOf V H)

variable {M V H : Subgroup G}

theorem le_xOf_self (V H : Subgroup G) : V ≤ Tim79a.xOf V H := by
  simpa [conjSubgroup_one] using
    (Tim79a.le_xOf (V := V) (H := H)
      (Tim79a.conjSubgroup_mem_omegaOf (V := V) (H := H) (h := 1) H.one_mem))

end CFSG.RankThree.GF2n.Tim81
