module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421NS

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_isL2Quot {f : ℕ} (hf : 2 ≤ f) {X : Type*} [Group X] (h : IsL2Quot f X) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have := Fintype.ofFinite (GaloisField 2 f)
    have hc : 4 ≤ (Finset.univ : Finset (GaloisField 2 f)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 f) (n := 2)
    le_rfl (Or.inr h4)).2.1
  exact e.isSimpleGroup

end S1421NS

end CFSG.Quasithin
