module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem l1_large (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) :
    (∃ z V, IsNaturalAt G₁ (G₁ ⊓ G₂) z V ∧ V ≤ pCoreOf 2 G₂) ∨
      (∃ z V, IsNaturalAt G₂ (G₁ ⊓ G₂) z V ∧ V ≤ pCoreOf 2 G₁) := by
  have hT : G₁ ⊓ G₂ ≠ ⊥ := by
    intro e
    rw [e] at h32
    simp at h32
  rcases l1_trichotomy h hT with h1 | h1 | ⟨z₁, V₁, z₂, V₂, hn₁, hn₂, hV₁, hV₂⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd (card_le_sixteen_of_b_one h hn₁ hn₂ hV₁ hV₂) (by omega)

theorem l1_setup (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) :
    ∃ A B : Subgroup D, ((A = G₁ ∧ B = G₂) ∨ (A = G₂ ∧ B = G₁)) ∧ GoldHyp A B ∧
      ∃ z V, IsNaturalAt A (A ⊓ B) z V ∧ V ≤ pCoreOf 2 B ∧
        AmalgamHypV (A ⊔ B) A B (A ⊓ B) V ∧ F112W.IsNaturalS3 A V ∧
        2 ≤ critDist (A ⊔ B) A B V ∧
        (critDist (A ⊔ B) A B V = 2 ∨
          (3 ≤ critDist (A ⊔ B) A B V ∧ IsElemAbelian 2 (conjClosure V B))) := by
  rcases l1_large h h32 with ⟨z, V, hn, hV⟩ | ⟨z, V, hn, hV⟩
  · exact ⟨G₁, G₂, Or.inl ⟨rfl, rfl⟩, h, z, V, hn, hV, h.amalgamHypV hn, hn.natural,
      (two_le_critDist_iff h hn).mpr hV, critDist_dichotomy h hn hV⟩
  · have hn' : IsNaturalAt G₂ (G₂ ⊓ G₁) z V := by rw [inf_comm]; exact hn
    exact ⟨G₂, G₁, Or.inr ⟨rfl, rfl⟩, h.symm, z, V, hn', hV, h.symm.amalgamHypV hn', hn'.natural,
      (two_le_critDist_iff h.symm hn').mpr hV, critDist_dichotomy h.symm hn' hV⟩

end GoldAmL

end F6

end CFSG.Quasithin
