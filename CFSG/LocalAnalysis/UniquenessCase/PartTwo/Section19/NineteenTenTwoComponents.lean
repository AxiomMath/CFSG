module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]


theorem bar2_IOf_shape_of_alt2 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V)
    (hcase2 : IOf D p L = conjClosure D.M L ∧ conjClosure D.M L ≠ L ∧ 2 < S17.nOf L ∧
        ((IsL2 (Bar2 L) (S17.nOf L) ∧ (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
          (IsSz (Bar2 L) (S17.nOf L) ∧
            (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]))) :
    (∃ x ∈ D.M, IOf D p L = L ⊔ CFSG.Quasithin.conjSubgroup L x) ∧
      (IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
        IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L)) := by
  have hL : L ∈ calC D.M := h.hyp.hL.1
  obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ := S17.p42_alt2_of_ne h42 h.hyp.hp hL hcase2.2.1
  refine ⟨⟨x, hxM, hcase2.1.trans hXsup⟩, ?_⟩
  rcases hcase2.2.2.2 with ⟨hL2, -⟩ | ⟨hSz, -⟩
  · have hsq := isL2Square_bar2_conjClosure hL hxM hXsup hne hL2
    rw [← hcase2.1] at hsq
    exact Or.inl hsq
  · have hsq := isSzSquare_bar2_conjClosure hL hxM hXsup hne hSz
    rw [← hcase2.1] at hsq
    exact Or.inr hsq

theorem shape_of_ctx19_10 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V) (hodd : Odd (S17.nOf L)) :
    IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨ IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) := by
  have h1910 := h.h1910
  simp only [Setting1910] at h1910
  obtain ⟨-, h1 | h2 | h3⟩ := h1910
  · exact Or.inl h1.1
  · rcases (bar2_IOf_shape_of_alt2 D h h42 h2).2 with hsq | hsq
    · exact Or.inr (Or.inl hsq)
    · exact Or.inr (Or.inr hsq)
  · exfalso
    obtain ⟨-, hn2, ⟨k, hk⟩, -⟩ := h3
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk] at hn2
      norm_num at hn2
    have heven : Even (S17.nOf L) := by
      rw [hk]
      exact (Nat.even_pow' hk0).mpr even_two
    exact (Nat.not_odd_iff_even.mpr heven) hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
