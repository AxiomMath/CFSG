module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma12_9_3One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ K₁ : Subgroup G, lOne L V₁ ≤ K₁ ∧
        quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) ∧
        Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G)

theorem lemma12_9_3_one (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Lemma12_9_3One := by
  intro G _ _ T L V n hcx V₁ hV₁
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  exact exists_cComp_normalizer_ge_lOne h1222 h37 h38 h39 hcx.hyp hn hV₁

theorem Lemma12_9_3.one (h1293 : Lemma12_9_3) : Lemma12_9_3One := by
  intro G _ _ T L V n hcx V₁ hV₁
  obtain ⟨K₁, hLK₁, hK₁c, hK₁n, -⟩ := h1293 G T L V n hcx 1 V₁ hV₁ (by
    rcases hcx.n45 with h | h
    · exact Or.inr ⟨h, Or.inl rfl⟩
    · exact Or.inl ⟨h, le_rfl, by omega⟩)
  have h1 : li128 n 1 L V₁ = lOne L V₁ := by
    unfold li128 lOne
    split_ifs with h
    · omega
    · rfl
  rw [h1] at hLK₁
  exact ⟨K₁, hLK₁, hK₁c, hK₁n⟩

end CFSG.Quasithin.H13
