module

public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def IsList1293Two (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty (Q ≃* NativeSporadic.M24) ∨ Nonempty (Q ≃* NativeSporadic.J4)

@[expose] def IsList1293Three (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ IsHatA7 Q ∨
    Nonempty (Q ≃* NativeSporadic.M23) ∨ Nonempty (Q ≃* NativeSporadic.HS) ∨
    Nonempty (Q ≃* NativeSporadic.He) ∨ Nonempty (Q ≃* NativeSporadic.Ru) ∨ IsSL27OverE49 Q

@[expose] def Lemma12_9_3K1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ K₁ : Subgroup G, lOne L V₁ ≤ K₁ ∧
        quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) ∧
        Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) ∧
        (lOne L V₁ = K₁ ∨ IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
          (n = 4 ∧ IsList1293Three (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)))

theorem lemma12_9_3K1_of (h1293 : Lemma12_9_3) : Lemma12_9_3K1 := by
  intro G _ _ T L V n hcx V₁ hV₁
  obtain ⟨K₁, hLK, hK, hK₁n, hcases⟩ := h1293 G T L V n hcx 1 V₁ hV₁
    (by rcases hcx.n45 with h | h <;> simp [h])
  have hli : li128 n 1 L V₁ = lOne L V₁ := by simp [li128, lOne]
  rw [hli] at hLK hcases
  refine ⟨K₁, hLK, hK, hK₁n, ?_⟩
  rcases hcases with heq | ⟨-, h2⟩ | ⟨-, hn4, h3⟩
  · exact Or.inl heq
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hn4, h3⟩)

end CFSG.Quasithin.H13
