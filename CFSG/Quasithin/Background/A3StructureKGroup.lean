module

public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.LocalAnalysis.SectionRank.Induction

public section

namespace CFSG.Quasithin

open CFSG.Assembly CFSG.Open.SQTKTauCeti

theorem nonab_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul]; exact h'))⟩

theorem kGroup_subgroup {G : Type} [Group G] (hG : CFSG.SectionRank.IsKGroupCat G) (Y : Subgroup G) :
    CFSG.SectionRank.IsKGroupCat ↥Y :=
  hG.subgroup Y

theorem kGroup_quotient {G : Type} [Group G] (hG : CFSG.SectionRank.IsKGroupCat G) (M : Subgroup G)
    [M.Normal] : CFSG.SectionRank.IsKGroupCat (G ⧸ M) :=
  hG.quotient M

theorem assemblyPRank_eq {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.Assembly.pRank p H = CFSG.Open.pRank p H := rfl

theorem sqt_iff {G : Type} [Group G] [Finite G] :
    StronglyQuasithin G ↔ ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2 :=
  Iff.rfl

theorem sqt_subgroup {G : Type} [Group G] [Finite G] (hG : StronglyQuasithin G)
    (Y : Subgroup G) : StronglyQuasithin ↥Y := fun p hp hp2 =>
  (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt Y.subtype Y.subtype_injective).trans
    (hG p hp hp2)

theorem sqt_quotient_two_group {G : Type} [Group G] [Finite G] (hG : StronglyQuasithin G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P) : StronglyQuasithin (G ⧸ P) :=
  fun p hp hp2 => by
    have h : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2 := hG p hp hp2
    have h2 := CFSG.SectionRank.pRank_quotient_two_group P hP hp hp2
    show CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ P)) ≤ 2
    rw [h2]
    exact h

end CFSG.Quasithin
