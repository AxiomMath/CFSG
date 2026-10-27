module

public import CFSG.RankThree.PartOne.NF7J.FinCore
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG.LieType.SteinbergBR.AutGL32 CFSG.QuasithinUnique.Setup.Family

@[expose] def code32 (M : M32) : ℕ :=
  (M 0 0).val + 2 * (M 0 1).val + 4 * (M 0 2).val + 8 * (M 1 0).val + 16 * (M 1 1).val +
    32 * (M 1 2).val + 64 * (M 2 0).val + 128 * (M 2 1).val + 256 * (M 2 2).val

theorem mk32_code32 : ∀ M : M32, mk32 (code32 M) = M := by decide +kernel

@[expose] def canonTable : List (ℕ × ℕ × ℕ × Bool) :=
  [(84, 167, 124, false), (84, 233, 124, true), (84, 275, 214, true), (84, 281, 214, false), (84, 302, 84, true), (84, 305, 254, false), (84, 401, 254, true), (84, 458, 84, false), (124, 161, 236, true), (124, 214, 116, false), (124, 266, 86, true), (124, 279, 212, true), (124, 281, 159, false), (124, 305, 183, false), (124, 403, 92, false), (124, 465, 110, true), (161, 124, 188, false), (161, 214, 188, true), (161, 275, 205, false), (161, 277, 253, false), (161, 281, 205, true), (161, 302, 140, true), (161, 337, 253, true), (161, 458, 140, false), (167, 84, 244, true), (167, 233, 172, false), (167, 266, 141, true), (167, 275, 95, false), (167, 277, 111, false), (167, 313, 204, true), (167, 345, 156, false), (167, 465, 181, true), (214, 124, 116, true), (214, 161, 236, false), (214, 266, 86, false), (214, 275, 159, true), (214, 309, 110, false), (214, 313, 92, true), (214, 345, 212, false), (214, 401, 183, true), (233, 84, 244, false), (233, 167, 172, true), (233, 266, 141, false), (233, 279, 156, true), (233, 281, 95, true), (233, 309, 181, false), (233, 337, 111, true), (233, 403, 204, false), (266, 124, 98, false), (266, 167, 122, false), (266, 214, 98, true), (266, 233, 122, true), (266, 277, 358, true), (266, 305, 382, true), (266, 337, 358, false), (266, 401, 382, false), (275, 84, 99, false), (275, 161, 163, true), (275, 167, 171, true), (275, 214, 115, false), (275, 305, 423, true), (275, 309, 431, true), (275, 337, 359, false), (275, 465, 375, false), (277, 161, 277, true), (277, 167, 285, true), (277, 266, 85, false), (277, 281, 215, false), (277, 302, 117, false), (277, 313, 247, false), (277, 401, 407, true), (277, 403, 415, true), (279, 124, 103, false), (279, 233, 229, false), (279, 305, 309, true), (279, 309, 317, true), (279, 345, 213, false), (279, 401, 179, true), (279, 403, 187, true), (279, 458, 87, false), (281, 84, 99, true), (281, 124, 115, true), (281, 161, 163, false), (281, 233, 171, false), (281, 277, 359, true), (281, 309, 375, true), (281, 401, 423, false), (281, 465, 431, false), (302, 84, 102, false), (302, 161, 165, false), (302, 277, 303, true), (302, 305, 311, true), (302, 345, 157, false), (302, 403, 94, false), (302, 458, 114, true), (302, 465, 106, true), (305, 84, 270, true), (305, 124, 286, true), (305, 266, 142, false), (305, 275, 207, false), (305, 279, 239, false), (305, 302, 174, false), (305, 337, 335, true), (305, 345, 351, true), (309, 214, 271, true), (309, 233, 279, true), (309, 275, 93, false), (309, 279, 125, false), (309, 281, 158, false), (309, 313, 190, false), (309, 458, 342, true), (309, 465, 334, true), (313, 167, 167, false), (313, 214, 230, false), (313, 277, 302, true), (313, 309, 318, true), (313, 337, 107, true), (313, 345, 123, true), (313, 403, 206, false), (313, 458, 143, false), (337, 161, 277, false), (337, 233, 285, false), (337, 266, 85, true), (337, 275, 215, true), (337, 305, 407, false), (337, 313, 415, false), (337, 403, 247, true), (337, 458, 117, true), (345, 167, 229, true), (345, 214, 103, true), (345, 279, 213, true), (345, 302, 87, true), (345, 305, 179, false), (345, 313, 187, false), (345, 401, 309, false), (345, 465, 317, false), (401, 84, 270, false), (401, 214, 286, false), (401, 266, 142, true), (401, 277, 335, false), (401, 279, 351, false), (401, 281, 207, true), (401, 345, 239, true), (401, 458, 174, true), (403, 124, 230, true), (403, 233, 167, true), (403, 277, 107, false), (403, 279, 123, false), (403, 302, 143, true), (403, 313, 206, true), (403, 337, 302, false), (403, 465, 318, false), (458, 84, 102, true), (458, 161, 165, true), (458, 279, 157, true), (458, 302, 114, false), (458, 309, 106, false), (458, 313, 94, true), (458, 337, 303, false), (458, 401, 311, false), (465, 124, 271, false), (465, 167, 279, false), (465, 275, 158, true), (465, 281, 93, true), (465, 302, 342, false), (465, 309, 334, false), (465, 345, 125, true), (465, 403, 190, true)]

@[expose] def chkCanon (t : ℕ × ℕ × ℕ × Bool) : Bool :=
  decide (det3 (mk32 t.2.2.1) = 1) &&
    (if t.2.2.2 then decide (mk32 t.2.2.1 * (mk32 t.1)ᵀ = mk32 84 * mk32 t.2.2.1) &&
        decide (mk32 t.2.2.1 * (mk32 t.2.1)ᵀ = mk32 167 * mk32 t.2.2.1)
      else decide (mk32 t.2.2.1 * mk32 t.1 = mk32 84 * mk32 t.2.2.1) &&
        decide (mk32 t.2.2.1 * mk32 t.2.1 = mk32 167 * mk32 t.2.2.1))

theorem canonTable_ok : canonTable.all chkCanon = true := by decide +kernel

theorem canonTable_cover : ∀ A : M32, det3 A = 1 → A ≠ 1 → A * A = 1 → ∀ B : M32, det3 B = 1 → B ≠ 1 →
    B * B = 1 → IsOrd4 (A * B) → ∃ t ∈ canonTable, t.1 = code32 A ∧ t.2.1 = code32 B := by
  decide +kernel

theorem exists_canon (A B : M32) (hA : det3 A = 1) (hA1 : A ≠ 1) (hA2 : A * A = 1) (hB : det3 B = 1)
    (hB1 : B ≠ 1) (hB2 : B * B = 1) (hAB : IsOrd4 (A * B)) :
    (∃ h : M32, det3 h = 1 ∧ h * A = mk32 84 * h ∧ h * B = mk32 167 * h) ∨
      (∃ h : M32, det3 h = 1 ∧ h * Aᵀ = mk32 84 * h ∧ h * Bᵀ = mk32 167 * h) := by
  obtain ⟨t, ht, h1, h2⟩ := canonTable_cover A hA hA1 hA2 B hB hB1 hB2 hAB
  have hc := List.all_eq_true.1 canonTable_ok t ht
  have hA' : mk32 t.1 = A := by rw [h1, mk32_code32]
  have hB' : mk32 t.2.1 = B := by rw [h2, mk32_code32]
  obtain ⟨a, b, hh, flag⟩ := t
  simp only at hA' hB'
  simp only [chkCanon, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [hA', hB'] at hc
  obtain ⟨hdet, hc2⟩ := hc
  cases flag
  · left
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc2
    exact ⟨mk32 hh, hdet, hc2.1, hc2.2⟩
  · right
    simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc2
    exact ⟨mk32 hh, hdet, hc2.1, hc2.2⟩

end CFSG.RankThree.PartOne.NF7J
