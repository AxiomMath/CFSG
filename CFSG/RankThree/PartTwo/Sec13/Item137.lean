module

public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Config137 {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L P E F : Subgroup G) (t : G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 3 P (A ⊔ L) ∧ A ≤ P ∧
    t ∈ L ⊓ Subgroup.normalizer (P : Set G) ∧ (∀ z ∈ ⁅P, P⁆, t * z * t⁻¹ = z⁻¹) ∧
    {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27} =
      {A, conjugate A t, E, F} ∧
    A ≠ conjugate A t ∧ E ≠ F ∧ E ≠ A ∧ E ≠ conjugate A t ∧ F ≠ A ∧ F ≠ conjugate A t ∧
    E ≤ (A ⊔ L) ⊓ Subgroup.normalizer (A : Set G) ∧
    F ≤ (A ⊔ L) ⊓ Subgroup.normalizer (A : Set G) ∧
    Nonempty (Sec4.autIn L E ≃* GL (Fin 2) (ZMod 3)) ∧
    Nonempty (Sec4.autIn L F ≃* GL (Fin 2) (ZMod 3)) ∧
    E = Subgroup.zpowers c ⊔ (E ⊓ L) ∧ F = Subgroup.zpowers c ⊔ (F ⊓ L)

@[expose] def Item137Delta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∃ (P E F : Subgroup G) (t : G), Config137 A c L P E F t

@[expose] def Item137NormLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t →
          ∀ X : Subgroup G, X = E ∨ X = F → HypS X ∨ HypT X →
            Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def Item137Move : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∃ s ∈ Subgroup.normalizer (F : Set G),
              s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)

theorem Config137.facts {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L P E F : Subgroup G} {t : G}
    (h : Config137 A c L P E F t) {X : Subgroup G} (hX : X = E ∨ X = F) :
    X ≤ (A ⊔ L) ⊓ Subgroup.normalizer (A : Set G) ∧ CFSG.Assembly.IsElemAbelian 3 X ∧
      Nat.card X = 27 ∧ Nonempty (Sec4.autIn L X ≃* GL (Fin 2) (ZMod 3)) := by
  obtain ⟨-, -, -, -, hΔ, -, -, -, -, -, -, hEN, hFN, hEa, hFa, -, -⟩ := h
  have hmem : X ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27} := by
    rw [hΔ]
    rcases hX with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨-, hX3, hX27⟩ := hmem
  rcases hX with rfl | rfl
  · exact ⟨hEN, hX3, hX27, hEa⟩
  · exact ⟨hFN, hX3, hX27, hFa⟩

theorem rank3II_13_7_of_steps (hΔ : Item137Delta) (hN : Item137NormLe) (hM : Item137Move) :
    Item137 := by
  intro G _ _ A c L h hM12
  obtain ⟨P, E, F, t, hcfg⟩ := hΔ G A c L h hM12
  by_cases hE : HypS E ∨ HypT E
  · by_cases hF : HypS F ∨ HypT F
    · exfalso
      obtain ⟨s, hsF, hsH⟩ := hM G A c L h hM12 P E F t hcfg hE
        (hN G A c L h hM12 P E F t hcfg E (Or.inl rfl) hE)
      exact hsH (hN G A c L h hM12 P E F t hcfg F (Or.inr rfl) hF hsF)
    · obtain ⟨hle, h3, h27, haut⟩ := hcfg.facts (Or.inr rfl)
      exact ⟨F, hle, h3, h27, haut, not_or.mp hF⟩
  · obtain ⟨hle, h3, h27, haut⟩ := hcfg.facts (Or.inl rfl)
    exact ⟨E, hle, h3, h27, haut, not_or.mp hE⟩

end CFSG.RankThree.PartTwo.Sec13
