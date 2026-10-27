module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowCrit
public import CFSG.GH74.GLS.IVK.Statements.Sec4c

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

theorem l143Rows_G23 (h47 : CFSG.GH74.GLS.IVK.IVK_4_7ef) :
    ∀ (S : Type) [Group S] [Finite S],
      CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 1 → L143Rows S := by
  intro S _ _ hS
  have hLie : CFSG.Blueprint.LieModel S .G2 0 3 1 := Or.inr (Or.inl ⟨rfl, by decide, hS⟩)
  obtain ⟨P⟩ : Nonempty (Sylow 3 S) := inferInstance
  obtain ⟨hgen, hcardP⟩ := h47.1 S 3 1 Nat.prime_three (by norm_num) (Or.inl hLie) P
  obtain ⟨hel, hcardZ⟩ := h47.2 S 1 hLie P
  have hP : Nat.card (P : Subgroup S) = 729 := by
    rw [hcardP hLie]
    norm_num
  have hZ : Nat.card (Subgroup.center (P : Subgroup S)) = 9 := by
    rw [hcardZ]
    norm_num
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup S,
      Z = (Subgroup.center (P : Subgroup S)).map (P : Subgroup S).subtype := ⟨_, rfl⟩
  have hZP : Z ≤ (P : Subgroup S) := hZdef ▸ Subgroup.map_subtype_le _
  have hZc : ∀ z ∈ Z, ∀ g ∈ (P : Subgroup S), z * g = g * z := by
    rw [hZdef]
    rintro _ ⟨c, hc, rfl⟩ g hg
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)).symm
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    rw [hZdef]
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 3)
      (A := Subgroup.center (P : Subgroup S)) c hc, map_one]
  have hZcard : Nat.card Z = 9 := by
    rw [hZdef, Subgroup.card_map_of_injective (P : Subgroup S).subtype_injective, hZ]
  obtain ⟨y, hyP, hy3, hyZ⟩ : ∃ y ∈ (P : Subgroup S), y ^ 3 = 1 ∧ y ∉ Z := by
    by_contra h
    have hle : (P : Subgroup S) ≤ Z :=
      hgen.symm.le.trans ((Subgroup.closure_le Z).mpr fun x hx => by
        by_contra hxZ
        exact h ⟨x, hx.1, hx.2, hxZ⟩)
    have := Subgroup.card_le_of_le hle
    omega
  exact L143Rows.of_central P Z hZP hZc hZ3 (by omega) hyP hy3 hyZ

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
