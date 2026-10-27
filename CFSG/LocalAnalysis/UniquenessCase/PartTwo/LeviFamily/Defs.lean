module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Q : Type} [Group Q] [Finite Q]

structure IsLeviFamily (P : Subgroup Q) (d : ℕ) (L : Fin d → Subgroup Q) : Prop where
  pCoreOf_le : ∀ i, pCoreOf 2 P ≤ L i
  le : ∀ i, L i ≤ P
  normal : ∀ i, ((L i).subgroupOf P).Normal
  eq_opp_sup : ∀ i, L i = Opp 2 (L i) ⊔ pCoreOf 2 P
  ne : ∀ i, L i ≠ pCoreOf 2 P
  commutator_le : ∀ i j, i ≠ j → ⁅L i, L j⁆ ≤ pCoreOf 2 P
  iSup_eq : (⨆ i, L i) = Opp 2 P ⊔ pCoreOf 2 P
  tits : ∀ i (N : Subgroup Q), pCoreOf 2 P ≤ N → N ≤ L i → (N.subgroupOf (L i)).Normal →
    ¬ ⁅N, L i⁆ ≤ pCoreOf 2 P → S17.oUpperTwo (L i) ≤ N

@[expose] def LeviAlt (P : Subgroup Q) (d : ℕ) (L : Fin d → Subgroup Q) : Prop :=
  (d ≤ 2 ∧ ∀ i, CFSG.Open.IsQuasisimple (Bar2 (L i))) ∨
    ∀ i (N : Subgroup Q) (n : ℕ), pCoreOf 2 P ≤ N → N ≤ L i → (N.subgroupOf (L i)).Normal →
      3 ≤ n → ¬ IsL2 (Bar2 N) n

@[expose] def HasLeviFamilies (S : Type) [Group S] [Finite S] : Prop :=
  ∀ P : Subgroup S, S19.IsNontrivialParabolic S P →
    ∃ (d : ℕ) (L : Fin d → Subgroup S), IsLeviFamily P d L

@[expose] def HasLeviFamiliesAlt (S : Type) [Group S] [Finite S] : Prop :=
  ∀ P : Subgroup S, S19.IsNontrivialParabolic S P →
    ∃ (d : ℕ) (L : Fin d → Subgroup S), IsLeviFamily P d L ∧ LeviAlt P d L

theorem HasLeviFamiliesAlt.hasLeviFamilies {S : Type} [Group S] [Finite S]
    (h : HasLeviFamiliesAlt S) : HasLeviFamilies S := fun P hP =>
  let ⟨d, L, hL, _⟩ := h P hP
  ⟨d, L, hL⟩

omit [Finite Q] in
@[expose] def LeviBlk (two big : Prop) (d : ℕ) (L : Fin d → Subgroup Q) : Prop :=
  (∀ i, 3 ∣ Nat.card (Bar2 (S17.oUpperTwo (L i))) ∧
    (CFSG.Open.IsQuasisimple (Bar2 (S17.oUpperTwo (L i))) ∨
      (Nonempty (Bar2 (S17.oUpperTwo (L i)) ≃* Multiplicative (ZMod 3)) ∧ two))) ∧
  (d ≤ 2 ∨ big)

@[expose] def HasLeviFamiliesBlk (two big : Prop) (S : Type) [Group S] [Finite S] : Prop :=
  ∀ P : Subgroup S, S19.IsNontrivialParabolic S P →
    ∃ (d : ℕ) (L : Fin d → Subgroup S),
      IsLeviFamily P d L ∧ LeviAlt P d L ∧ LeviBlk two big d L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
