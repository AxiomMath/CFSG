module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Defs
public import CFSG.Quasithin.Recognition.Stroth.Str83SevenPath

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G]

theorem inf_map_conj_eq_win (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) :
    (Q₁ ⊓ Q₂) ⊓ (Q₁ ⊓ Q₂).map (MulAut.conj (x₂ * x₁)).toMonoidHom ⊓
        (Q₁ ⊓ Q₂).map (MulAut.conj ((x₂ * x₁) ^ 2)).toMonoidHom ⊓
        (Q₁ ⊓ Q₂).map (MulAut.conj ((x₂ * x₁) ^ 3)).toMonoidHom =
      win Q₁ Q₂ x₁ x₂ 0 7 := by
  ext y
  simp only [mem_inf, mem_win_iff, mem_qv_iff, mem_map_conj_iff, trackElt, trackPar]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2, h3⟩, h4, h5⟩, h6, h7⟩ i hi0 hi7
    interval_cases i
    · simpa [Int.even_iff] using h0
    · simpa [Int.even_iff] using h1
    · simpa [Int.even_iff] using h2
    · simpa [Int.even_iff] using h3
    · simpa [Int.even_iff] using h4
    · simpa [Int.even_iff] using h5
    · simpa [Int.even_iff] using h6
    · simpa [Int.even_iff] using h7
  · intro h
    have e : ∀ i : ℤ, 0 ≤ i → i ≤ 7 → _ := h
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · simpa [Int.even_iff] using e 0 le_rfl (by norm_num)
    · simpa [Int.even_iff] using e 1 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 2 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 3 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 4 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 5 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 6 (by norm_num) (by norm_num)
    · simpa [Int.even_iff] using e 7 (by norm_num) le_rfl

@[expose] def Str83G5AbstractGoal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (c : Conf G n), win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 7 = ⊥

@[expose] def Str83G5ConcreteGoal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      ∃ c : Conf G (2 * a + 1), c.P₁ = L1 ⊔ bigB L1 L2 S ∧ c.P₂ = L2 ⊔ bigB L1 L2 S ∧
        c.Q₁ = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ∧ c.Q₂ = pCoreOf 2 (L2 ⊔ bigB L1 L2 S)

theorem str83SevenPath_of_conf (hA : Str83G5AbstractGoal) (hC : Str83G5ConcreteGoal) :
    Str83SevenPath := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨c, hP₁, hP₂, hQ₁, hQ₂⟩ := hC G L1 L2 S a hF ha hSz hBig hL2
  refine ⟨c.x₁, hP₁ ▸ c.track.x₁_mem, fun h => c.track.x₁_not_mem ?_, c.x₂,
    hP₂ ▸ c.track.x₂_mem, fun h => c.track.x₂_not_mem ?_, ?_⟩
  · rw [hP₂]
    exact mem_sup_right h
  · rw [hP₁]
    exact mem_sup_right h
  · rw [← hQ₁, ← hQ₂, inf_map_conj_eq_win]
    exact hA G (2 * a + 1) c

end CFSG.Quasithin.Stroth.G5

end
