module

public import CFSG.Quasithin.H13.NQCatA314LieSp4
public import CFSG.Quasithin.H13.NQCatA314LieG2
public import CFSG.Quasithin.H13.NQCatA314LieD4
public import CFSG.Quasithin.H13.NQCatA314LieF4

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique

theorem desc_lie
    (G : Type) [Group G] [Finite G] (L P : Subgroup G) (hrk : IsRank2LieChar2 ↥L)
    (hP : IsMaxParabolic2 L P) (hA : IsAlt 5 (ModO2 (perfectCore P))) :
    CFSG.generalizedFitting ↥(perfectCore P) = CFSG.pCore 2 ↥(perfectCore P) ∧
      (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L) := by
  rcases hrk with ⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨-, hf, hm⟩⟩ | hT
  · obtain ⟨hc, rfl⟩ := lieP_l3 L P f hf (Or.inl hm) hP hA
    exact ⟨generalizedFitting_eq_of_charTwo hc, Or.inl hm⟩
  · obtain ⟨hc, rfl⟩ := lieP_l3 L P f hf (Or.inr hm) hP hA
    exact ⟨generalizedFitting_eq_of_charTwo hc, Or.inr (Or.inl hm)⟩
  · obtain ⟨hc, rfl⟩ := lieP_sp4 L P f hf hm hP hA
    exact ⟨generalizedFitting_eq_of_charTwo hc, Or.inr (Or.inr (Or.inl hm))⟩
  · obtain ⟨hc, rfl⟩ := lieP_g2 L P f hf hm hP hA
    exact ⟨generalizedFitting_eq_of_charTwo hc, Or.inr (Or.inr (Or.inr (Or.inl hm)))⟩
  · obtain ⟨hc, rfl⟩ := lieP_d4 L P f hf hm hP hA
    exact ⟨generalizedFitting_eq_of_charTwo hc, Or.inr (Or.inr (Or.inr (Or.inr hm)))⟩
  · exact (lieP_f4 L P f hf hm hP hA).2.elim
  · exact (lieP_tits L P hT hP hA).2.elim

end CFSG.Quasithin.H13.NQCat.A314D
