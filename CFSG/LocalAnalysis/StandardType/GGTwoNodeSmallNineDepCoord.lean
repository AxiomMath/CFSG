module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel8
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel9
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel9m

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ninedep_model {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hV : Module.finrank (ZMod 3) V ≤ 9) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod 3) V)
    (x : V) (ha : V) (αa : Module.Dual (ZMod 3) V)
    (hF : CFSG.StandardType.GGDepAFrame 3 9 h α x) (hha : αa ha = 2) (hx : αa x ≠ 0)
    (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ())
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3)) :
    ∃ (D nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ),
      (⟨3, D, nF, gens, x', b⟩ : Pt) ∈ pts8 () ++ pts9 () ++ pts9m () ∧
      ∃ e : V ≃ₗ[ZMod 3] (Fin D → ZMod 3), (⟨3, D, nF, gens, x', b⟩ : Pt).Models e h α x ha αa := by
  obtain ⟨D, u, hD, ⟨C⟩⟩ := ninedep_chart hV h α x hF
  rcases hD with rfl | rfl
  · obtain ⟨nF, gens, x', b, hmem, e, hM⟩ :=
      ninedep_model_8 h α x u C ha αa hha hx s hs o ho hH hA
    exact ⟨8, nF, gens, x', b, by simp only [List.mem_append]; exact Or.inl (Or.inl hmem), e, hM⟩
  · by_cases hM : C.e ha 8 = 0
    · obtain ⟨nF, gens, x', b, hmem, e, hM'⟩ :=
        ninedep_model_9m h α x u C hF.fix ha αa hha hx hM s hs o ho hH hA
      exact ⟨9, nF, gens, x', b, by simp only [List.mem_append]; exact Or.inr hmem, e, hM'⟩
    · obtain ⟨nF, gens, x', b, hmem, e, hM'⟩ :=
        ninedep_model_9 h α x u C ha αa hha hx hM s hs o ho hH hA
      exact ⟨9, nF, gens, x', b, by simp only [List.mem_append]; exact Or.inl (Or.inr hmem), e, hM'⟩

end CFSG.TwoNodeSmall
