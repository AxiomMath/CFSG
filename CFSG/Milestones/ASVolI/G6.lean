module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6

@[expose] def G_6_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)) (a : MulAut V),
    Hypothesis61 X a →
      commV (classClosure X a) = ⊤ ∧
      commV (pResidualOf 2 (classClosure X a)) = ⊤ ∧
      ∀ H : Subgroup (MulAut V), H ≤ X → conjClosure (Subgroup.zpowers a) H = classClosure X a →
        ∀ U : Subgroup V, IsHSubmodule H U → commV (Subgroup.zpowers a) ≤ U → U = ⊤

theorem as_G_6_2 : G_6_2 := by
  intro V _ _ X a h
  exact ⟨lemma_G62_1 h, lemma_G62_2 h, fun H _ hK U hU hUa => lemma_G62_3 h hK hU hUa⟩

@[expose] def G_6_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)) (a : MulAut V),
    Hypothesis61 X a → ∀ U : Subgroup V, IsHSubmodule (classClosure X a) U →
      (conjClosure (Subgroup.zpowers a) (classClosure X a) = classClosure X a ∨
        IsHSubmodule X U) →
      commOn (classClosure X a) U = ⊥ ∨ U = ⊤ ∨
        (Nat.card (commOn (Subgroup.zpowers a) U) = 2 ∧
          Nat.card ((commV (Subgroup.zpowers a)).map (QuotientGroup.mk' U)) = 2)

theorem as_G_6_3 : G_6_3 := by
  intro V _ _ X a h U hU hcase
  exact lemma_G63 h hU hcase

@[expose] def G_6_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (a : MulAut V), G64.Hyp61 G a →
      Nat.card ↥(commV (Subgroup.zpowers a)) = 2 → G64.Conclusion G a

section

theorem as_G_6_4
    : G_6_4 :=
  CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds

end

end CFSG.ASVolI
