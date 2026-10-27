module

public import CFSG.RankThree.PartOne.NF7J.GLNorm

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix

theorem det3_GL (g : GL (Fin 3) (ZMod 2)) : det3 (g : M32) = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  have h3 : ((g : M32)).det = 1 := by simpa using h2
  rwa [det3_eq] at h3

@[expose] noncomputable def matUnit' (M : M32) (h : det3 M = 1) : GL (Fin 3) (ZMod 2) :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [det3_eq M, h]; exact isUnit_one)).unit

theorem matUnit'_val (M : M32) (h : det3 M = 1) : ((matUnit' M h : GL (Fin 3) (ZMod 2)) : M32) = M := rfl

@[expose] def conjTable : List (ℕ × ℕ) :=
  [(84, 99), (124, 107), (161, 92), (167, 93), (214, 103), (233, 110), (266, 267), (275, 273), (277, 161), (279, 305), (281, 266), (302, 271), (305, 140), (309, 141), (313, 270), (337, 98), (345, 106), (401, 84), (403, 85), (458, 111), (465, 102)]

@[expose] def chkConj (t : ℕ × ℕ) : Bool :=
  decide (det3 (mk32 t.2) = 1) && decide (mk32 t.2 * mk32 275 = mk32 t.1 * mk32 t.2)

theorem conjTable_ok : conjTable.all chkConj = true := by decide +kernel

theorem conjTable_cover : ∀ B : M32, det3 B = 1 → B ≠ 1 → B * B = 1 → conjTable.any (fun t => t.1 == code32 B) = true := by
  decide +kernel

theorem exists_conj_A0 (B : M32) (hB : det3 B = 1) (hB1 : B ≠ 1) (hB2 : B * B = 1) :
    ∃ K : M32, det3 K = 1 ∧ K * mk32 275 = B * K := by
  have hc := conjTable_cover B hB hB1 hB2
  obtain ⟨t, ht, hte⟩ := List.any_eq_true.1 hc
  have hok := List.all_eq_true.1 conjTable_ok t ht
  simp only [chkConj, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hB' : mk32 t.1 = B := by
    have : t.1 = code32 B := by simpa using hte
    rw [this, mk32_code32]
  rw [hB'] at hok
  exact ⟨mk32 t.2, hok.1, hok.2⟩

theorem det3_mk32_275 : det3 (mk32 275) = 1 := by decide +kernel

theorem cent_rho_fin : ∀ h : M32, det3 h = 1 → h * mk32 482 = mk32 482 * h →
    h = 1 ∨ h = mk32 482 ∨ h = mk32 482 * mk32 482 ∨ h = mk32 482 * mk32 482 * mk32 482 := by
  decide +kernel

@[expose] def ord4Table : List (ℕ × ℕ) :=
  [(86, 106), (92, 214), (103, 122), (107, 114), (116, 206), (122, 98), (143, 84), (158, 86), (163, 242), (165, 241), (169, 85), (188, 87), (205, 212), (212, 111), (225, 125), (239, 102), (242, 207), (254, 116), (270, 330), (285, 331), (298, 335), (307, 345), (311, 346), (317, 334), (330, 115), (339, 107), (351, 99), (358, 123), (369, 205), (377, 213), (394, 94), (405, 233), (407, 234), (409, 93), (428, 95), (443, 92), (460, 103), (467, 110), (473, 117), (482, 124), (494, 215), (501, 204)]

@[expose] def chkOrd4 (t : ℕ × ℕ) : Bool :=
  decide (det3 (mk32 t.2) = 1) && decide (mk32 t.2 * mk32 482 = mk32 t.1 * mk32 t.2)

theorem ord4Table_ok : ord4Table.all chkOrd4 = true := by decide +kernel

theorem ord4Table_cover : ∀ g : M32, IsOrd4 g → ord4Table.any (fun t => t.1 == code32 g) = true := by
  decide +kernel

theorem exists_conj_rho (g : M32) (hg : IsOrd4 g) : ∃ K : M32, det3 K = 1 ∧ K * mk32 482 = g * K := by
  have hc := ord4Table_cover g hg
  obtain ⟨t, ht, hte⟩ := List.any_eq_true.1 hc
  have hok := List.all_eq_true.1 ord4Table_ok t ht
  simp only [chkOrd4, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hg' : mk32 t.1 = g := by
    have : t.1 = code32 g := by simpa using hte
    rw [this, mk32_code32]
  rw [hg'] at hok
  exact ⟨mk32 t.2, hok.1, hok.2⟩

theorem mk32_84_mul_167 : mk32 84 * mk32 167 = mk32 482 := by decide +kernel

end CFSG.RankThree.PartOne.NF7J
