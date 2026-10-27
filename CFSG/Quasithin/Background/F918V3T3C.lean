module

public import CFSG.Quasithin.Background.F918V3T3A
public import CFSG.Sporadic.J1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace F918V3T3

section Mathieu

open Equiv

set_option maxRecDepth 100000

def m11a : Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

def m11b : Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

theorem three_dvd_card_M11 : 3 ∣ Nat.card NativeSporadic.M11 := by
  have ha : m11a ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m11b ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_cube NativeSporadic.M11 (x := m11a * m11b * m11b * m11a * m11b * m11b)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb) hb) ha) hb) hb)
    (by unfold m11a m11b; decide) (by unfold m11a m11b; decide)

def m12a : Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

def m12b : Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem three_dvd_card_M12 : 3 ∣ Nat.card NativeSporadic.M12 :=
  three_dvd_card_of_cube NativeSporadic.M12 (x := m12b)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    (by unfold m12b; decide) (by unfold m12b; decide)

def m22a : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

def m22b : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem three_dvd_card_M22 : 3 ∣ Nat.card NativeSporadic.M22 := by
  have ha : m22a ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m22b ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_cube NativeSporadic.M22
    (x := (m22a * m22b * m22a * m22b * m22b * m22b) ^ 2)
    (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha) hb) hb) hb) _)
    (by unfold m22a m22b; decide) (by unfold m22a m22b; decide)

def m23a : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

def m23b : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem three_dvd_card_M23 : 3 ∣ Nat.card NativeSporadic.M23 := by
  have ha : m23a ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m23b ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact three_dvd_card_of_cube NativeSporadic.M23 (x := m23a * m23b * m23b * m23a * m23b * m23b)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb) hb) ha) hb) hb)
    (by unfold m23a m23b; decide) (by unfold m23a m23b; decide)

def m24a : Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]

def m24b : Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem three_dvd_card_M24 : 3 ∣ Nat.card NativeSporadic.M24 :=
  three_dvd_card_of_cube NativeSporadic.M24 (x := m24b)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    (by unfold m24b; decide) (by unfold m24b; decide)

end Mathieu

theorem three_dvd_card_J1 : 3 ∣ Nat.card NativeSporadic.J1 := by
  rw [CFSG.Sporadic.J1.card_J1]
  norm_num

theorem three_dvd_card_J2 : 3 ∣ Nat.card NativeSporadic.J2 := by
  obtain ⟨x, y, h, -, -, -, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact three_dvd_card_of_card_eq _ (k := 3) (by norm_num) hc

theorem three_dvd_card_J4 : 3 ∣ Nat.card NativeSporadic.J4 := by
  obtain ⟨x, y, h, -, -, -, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  exact three_dvd_card_of_card_eq _ (k := 3) (by norm_num) hc

theorem three_dvd_card_He : 3 ∣ Nat.card NativeSporadic.He := by
  obtain ⟨x, y, h, -, -, -, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  exact three_dvd_card_of_card_eq _ (k := 3) (by norm_num) hc

theorem three_dvd_card_Ru : 3 ∣ Nat.card NativeSporadic.Ru := by
  obtain ⟨x, y, h, -, -, -, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
  exact three_dvd_card_of_card_eq _ (k := 3) (by norm_num) hc

theorem three_dvd_card_HS : 3 ∣ Nat.card NativeSporadic.HS := by
  obtain ⟨x, y, h, -, -, -, hc, -⟩ := CFSG.SectionRank.HS_sylow3_square_witness
  exact three_dvd_card_of_card_eq _ (k := 2) (by norm_num) hc

theorem three_dvd_card_of_sporadic
    {S : Type} [Group S] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru)
    (e : S ≃* NativeSporadic.Carrier s) : 3 ∣ Nat.card S := by
  rw [Nat.card_congr e.toEquiv]
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact three_dvd_card_M11
  · exact three_dvd_card_M12
  · exact three_dvd_card_M22
  · exact three_dvd_card_M23
  · exact three_dvd_card_M24
  · exact three_dvd_card_J1
  · exact three_dvd_card_J2
  · exact three_dvd_card_J4
  · exact three_dvd_card_HS
  · exact three_dvd_card_He
  · exact three_dvd_card_Ru

end F918V3T3

end CFSG.Quasithin
