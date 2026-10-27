module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth103CaseAStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Y : Subgroup G), Sec10Hyp hc n → Good101 M Q Z B t → Sit M Q Z Y t → CaseA Q Z t →
      Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t

@[expose] def Stroth103CaseBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Sec10Hyp hc n → (∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) →
      ∀ (t : G) (Y : Subgroup G), Good101 M Q Z B t → Sit M Q Z Y t → ¬ CaseA Q Z t →
        Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t

@[expose] def Stroth103M2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (s : G),
    Sec10Hyp hc n → Good101 M Q Z B s → SLMNat hc s 2 →
      (∀ y ∈ Q, ¬ Good103 M Q Z B (s * y)) →
        ∃ (t : G) (Y : Subgroup G), Good101 M Q Z B t ∧ Sit M Q Z Y t ∧ CaseA Q Z t ∧
          ¬ Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t

theorem stroth_10_3b_of_cases (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    (hA : Stroth103CaseAStatement) (hB : Stroth103CaseBStatement) : Stroth103bStatement := by
  intro G _ _ M Q Z B hc n H hno t ht
  obtain ⟨Y, hs⟩ := ht.exists_sit hc
  have hle : Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t := by
    by_cases hcA : CaseA Q Z t
    · exact hA G M Q Z B hc n t Y H ht hs hcA
    · exact hB G M Q Z B hc n H hno t Y ht hs hcA
  exact (Good101.good103_of_le_Vt h34 hspread H ht hs hle).2

theorem stroth_10_3a_of_cases (hA : Stroth103CaseAStatement) (hM2 : Stroth103M2Statement) :
    Stroth103aStatement := by
  intro G _ _ M Q Z B hc n s H hs hs2
  by_contra hcon
  push Not at hcon
  obtain ⟨t, Y, ht, hsY, hcA, hbad⟩ := hM2 G M Q Z B hc n s H hs hs2 hcon
  exact hbad (hA G M Q Z B hc n t Y H ht hsY hcA)

end CFSG.RankThree.GF2n.Stroth80
