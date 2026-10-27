module

public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem swap_mul_swap_cube {α : Type*} [DecidableEq α] [Fintype α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  have ht : Equiv.Perm.IsThreeCycle (Equiv.swap a b * Equiv.swap b c) := by
    have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b) (b := a) (c := c)
      hab.symm hbc hac
    rwa [Equiv.swap_comm b a] at h
  rw [← orderOf_dvd_iff_pow_eq_one, ht.orderOf]

private theorem swap_image_Iic (m : ℕ) :
    Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) '' {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}
      = {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 1} := by
  ext i
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · right; rfl
    · exfalso
      have : x.val = m + 1 := by rw [h2]
      omega
    · left
      have hxne : x.val ≠ m := by
        intro hv
        exact h1 (Fin.ext (by rw [hv]))
      omega
  · rintro (h | h)
    · refine ⟨i, ?_, ?_⟩
      · omega
      · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro hh
          have : i.val = m := by rw [hh]
          omega
        · intro hh
          have : i.val = m + 1 := by rw [hh]
          omega
    · refine ⟨(⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)), ?_, ?_⟩
      · simp
      · rw [Equiv.swap_apply_left]
        exact Fin.ext h.symm

private theorem swap_mul_swap_image_Iic (m : ℕ) :
    (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) *
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1))) '' {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}
      = {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 2} := by
  ext i
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.Perm.mul_apply]
    by_cases hA : x = (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
    · rw [hA, Equiv.swap_apply_left, Equiv.swap_apply_left]
      right; rfl
    · have hxlt : x.val < m := by
        have : x.val ≠ m := by
          intro hv; exact hA (Fin.ext hv)
        omega
      have hB : Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
            (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) x = x := by
        refine Equiv.swap_apply_of_ne_of_ne hA ?_
        intro hh
        have : x.val = m + 1 := by rw [hh]
        omega
      rw [hB]
      have hC : Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1))
            (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) x = x := by
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro hh
          have : x.val = m + 1 := by rw [hh]
          omega
        · intro hh
          have : x.val = m + 2 := by rw [hh]
          omega
      rw [hC]
      left; exact hxlt
  · rintro (h | h)
    · refine ⟨i, ?_, ?_⟩
      · omega
      · rw [Equiv.Perm.mul_apply]
        have hiA : Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
              (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) i = i := by
          refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
          · intro hh
            have : i.val = m := by rw [hh]
            omega
          · intro hh
            have : i.val = m + 1 := by rw [hh]
            omega
        rw [hiA]
        refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
        · intro hh
          have : i.val = m + 1 := by rw [hh]
          omega
        · intro hh
          have : i.val = m + 2 := by rw [hh]
          omega
    · refine ⟨(⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)), ?_, ?_⟩
      · simp
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
        exact Fin.ext h.symm

theorem weylRep_cube (n : ℕ) (j j' : Fin n) (h : j.val + 1 = j'.val) :
    (weylRep n F2 j * weylRep n F2 j') ^ 3 = 1 := by
  have hj : j.succ = j'.castSucc :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
  have hab : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ).ne
  have hbc : j.succ ≠ j'.succ := by
    rw [hj]
    exact (Fin.castSucc_lt_succ).ne
  have hac : j.castSucc ≠ j'.succ := by
    intro hh
    have hv : j.castSucc.val = j'.succ.val := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  rw [weylRep_eq_slPerm n j, weylRep_eq_slPerm n j', ← map_mul, ← map_pow]
  rw [show Equiv.swap j'.castSucc j'.succ = Equiv.swap j.succ j'.succ by rw [← hj]]
  rw [swap_mul_swap_cube hab hbc hac, map_one]

theorem top_eq_sup_conj (m : ℕ) (hm : 1 ≤ m) :
    (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) =
      (slUpper2Hom m).range ⊔
        (slUpper2Hom m).range.map
          (MulAut.conj (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom ⊔
        (slUpper2Hom m).range.map
          (MulAut.conj (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
            weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom := by
  have hU : (slUpper2Hom m).range =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m} := range_slUpper2Hom m
  have hU1 : ((slUpper2Hom m).range.map
        (MulAut.conj (weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom) =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 1} := by
    rw [hU, weylRep_eq_slPerm, slOn_map_conj_slPerm]
    rw [show ((⟨m, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
          (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl,
        show ((⟨m, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact congrArg (slOn (m + 1 + 1 + 1)) (swap_image_Iic m)
  have hU2 : ((slUpper2Hom m).range.map
        (MulAut.conj (weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
          weylRep (m + 1 + 1) F2 ⟨m, by omega⟩)).toMonoidHom) =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 2} := by
    have hw : weylRep (m + 1 + 1) F2 ⟨m + 1, by omega⟩ *
        weylRep (m + 1 + 1) F2 ⟨m, by omega⟩ =
        slPerm gf2_two (Equiv.swap ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc)
            ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ) *
          Equiv.swap ((⟨m, by omega⟩ : Fin (m + 1 + 1)).castSucc)
            ((⟨m, by omega⟩ : Fin (m + 1 + 1)).succ)) := by
      rw [weylRep_eq_slPerm, weylRep_eq_slPerm, ← map_mul]
    rw [hU, hw, slOn_map_conj_slPerm]
    rw [show ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl,
        show ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl,
        show ((⟨m, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
          (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl,
        show ((⟨m, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact congrArg (slOn (m + 1 + 1 + 1)) (swap_mul_swap_image_Iic m)
  rw [← slOn_univ (m + 1 + 1 + 1), hU1, hU2, hU]
  have h01 : (({i : Fin (m + 1 + 1 + 1) | i.val ≤ m} : Set (Fin (m + 1 + 1 + 1))) ∩
      {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 1}).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Fin.val_zero]; omega
    · simp only [Set.mem_setOf_eq, Fin.val_zero]; omega
  rw [slOn_sup_of_inter h01]
  rw [show ({i : Fin (m + 1 + 1 + 1) | i.val ≤ m} : Set (Fin (m + 1 + 1 + 1))) ∪
        {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 1} =
      {i : Fin (m + 1 + 1 + 1) | i.val ≤ m + 1} from by
    ext i; simp only [Set.mem_union, Set.mem_setOf_eq]; omega]
  have h11 : (({i : Fin (m + 1 + 1 + 1) | i.val ≤ m + 1} : Set (Fin (m + 1 + 1 + 1))) ∩
      {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 2}).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Fin.val_zero]; omega
    · simp only [Set.mem_setOf_eq, Fin.val_zero]; omega
  rw [slOn_sup_of_inter h11]
  rw [show ({i : Fin (m + 1 + 1 + 1) | i.val ≤ m + 1} : Set (Fin (m + 1 + 1 + 1))) ∪
        {i : Fin (m + 1 + 1 + 1) | i.val < m ∨ i.val = m + 2} = Set.univ from by
    ext i; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]; omega]

theorem slOn_lt_eq_sup (m : ℕ) (hm : 3 ≤ m) :
    slOn (m + 1 + 1 + 1) {i | i.val < m + 2} =
      slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val ∧ i.val < m + 2} ⊔
        slOn (m + 1 + 1 + 1) {0, 1, 4} := by
  have h4v : (4 : Fin (m + 1 + 1 + 1)).val = 4 :=
    Fin.val_cast_of_lt (show 4 < m + 1 + 1 + 1 by omega)
  have h0v : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero (m + 1 + 1 + 1)
  have h1v : (1 : Fin (m + 1 + 1 + 1)).val = 1 :=
    Fin.val_cast_of_lt (show 1 < m + 1 + 1 + 1 by omega)
  have hmem : (({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val < m + 2} :
        Set (Fin (m + 1 + 1 + 1))) ∩
      ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1)))).Nonempty := by
    refine ⟨4, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, h4v]; omega
    · simp
  rw [slOn_sup_of_inter hmem]
  rw [show ({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val < m + 2} :
        Set (Fin (m + 1 + 1 + 1))) ∪ ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) =
      {i : Fin (m + 1 + 1 + 1) | i.val < m + 2} from by
    ext i
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h2, hlt⟩ | h | h | h)
      · exact hlt
      · rw [h, h0v]; omega
      · rw [h, h1v]; omega
      · rw [h, h4v]; omega
    · intro hlt
      by_cases h2 : 2 ≤ i.val
      · exact Or.inl ⟨h2, hlt⟩
      · have h01 : i.val = 0 ∨ i.val = 1 := by omega
        rcases h01 with hv | hv
        · exact Or.inr (Or.inl (Fin.ext (by rw [h0v]; exact hv)))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext (by rw [h1v]; exact hv))))]

end CFSG.StandardType.GGHalf

end
