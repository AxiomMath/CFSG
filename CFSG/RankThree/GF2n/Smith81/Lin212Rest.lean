module

public import CFSG.RankThree.GF2n.Smith81.LinRestCore

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Lin212RestFirstProp (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z

@[expose] def Lin212RestFirstStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      Lin212RestFirstProp M Q Z

@[expose] def Lin212ComplProp (M Q Z : Subgroup G) : Prop :=
  ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
    ∃ K : Subgroup G, K ≤ M ∧ K ⊓ Q = ⊥ ∧ K ⊔ Q = M ∧ ∃ q ∈ Q, q * x * q⁻¹ ∈ K

@[expose] def Lin212ComplStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      Lin212ComplProp M Q Z

theorem lin212Rest_of (h1 : Lin212RestFirstStatement) (h2 : Lin212ComplStatement) :
    Lin212RestStatement := fun G _ _ M Q Z B n V₁ V₂ hb hc hS hn X x hs hne =>
  ⟨h1 G M Q Z B n V₁ V₂ hb hc hS hn X x hs hne, h2 G M Q Z B n V₁ V₂ hb hc hS hn X x hs hne⟩

section Main

variable [Finite G] {M Q Z B X : Subgroup G} {n : ℕ}
  {V₁ V₂ : Subgroup G} {x : G}

theorem lin212RestFirst_of_A (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x) {A : Subgroup G}
    (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAX : A ≤ QB X) :
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have hcA : Ctx M Q Z A := ⟨hc.hyp, hA, hAQ, hAZ⟩
  rcases (LinSetup.transv_of_conj hc hS hn hcA).1 with h | h
  · exact rest_first_core hb hc hS hn hs hA hAQ hAX h
  · exact rest_first_core hb hc hS.symm hn hs hA hAQ hAX h

theorem lin212RestFirst_of (h28c : Lin28CondStatement) : Lin212RestFirstStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn X x hs hne
  obtain ⟨A, hA, hAle⟩ := h28c G M Q Z B X x n V₁ V₂ hb hc hS hn hs hne
  exact lin212RestFirst_of_A hb hc hS hn hs hA (hAle.trans inf_le_left)
    (hAle.trans inf_le_right)

theorem lin3Statement_of_seven_leaves_compl (h28c : Lin28CondStatement)
    (h7 : Lin212C7Statement) (hcompl : Lin212ComplStatement) (h212two : Lin212TwoStatement)
    (h28two : Lin28TwoStatement) (h213 : Lin213Statement) (h26 : Lin26Statement) :
    Lin3Statement :=
  lin3Statement_of_seven_leaves h28c h7 (lin212Rest_of (lin212RestFirst_of h28c) hcompl)
    h212two h28two h213 h26

end Main

end CFSG.RankThree.GF2n.Smith81
