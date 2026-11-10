module

public import CFSG.Quasithin.Vol2.Asc94.He42P427H2

public section

namespace CFSG.Quasithin.A94.He42P427H

open CFSG.Quasithin.A94.L52 Matrix Subgroup

abbrev Sg : Subgroup Hc := Subgroup.centralizer ({abar} : Set Hc)

theorem mem_Sg_iff (x : Hc) : x ∈ Sg ↔ x * abar = abar * x := mem_centralizer_singleton_iff

theorem Phi_mem_Sg (p : Fin 9 → ZMod 2) : Phi p ∈ Sg := (mem_Sg_iff _).2 (Phi_comm_abar p)

theorem Sg_eq_range : (Sg : Set Hc) = Set.range Phi := by
  ext x
  constructor
  · intro hx
    exact ⟨prm x, (eq_Phi_of_comm x ((mem_Sg_iff x).1 hx)).symm⟩
  · rintro ⟨p, rfl⟩
    exact Phi_mem_Sg p

theorem Phi_injective : Function.Injective Phi :=
  Function.LeftInverse.injective (fun p => prm_Phi p)

theorem card_Sg : Nat.card ↥Sg = 512 := by
  have h : Nat.card ↥(Set.range Phi) = Nat.card (Fin 9 → ZMod 2) :=
    Nat.card_range_of_injective Phi_injective
  have h2 : Nat.card ↥Sg = Nat.card ↥(Set.range Phi) := by
    rw [← Sg_eq_range]
    rfl
  rw [h2, h, Nat.card_eq_fintype_card]
  simp

theorem cm_Sg_col1 (x : Hc) (hx : x ∈ Sg) :
    cm x 1 1 = 1 ∧ cm x 2 1 = 0 ∧ cm x 3 1 = 0 ∧ cm x 4 1 = 0 := by
  have h := eq_Phi_of_comm x ((mem_Sg_iff x).1 hx)
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Phi, cm_Phi', Xm]
    simp
  · simp only [Phi, cm_Phi', Xm]
    simp
  · simp only [Phi, cm_Phi', Xm]
    simp
  · rw [cm_row4]
    simp

@[expose] def W0 : Subgroup Hc where
  carrier := {x | x ∈ Sg ∧ cm x 0 1 = 0}
  mul_mem' := by
    rintro x y ⟨hx, hx01⟩ ⟨hy, hy01⟩
    refine ⟨Sg.mul_mem hx hy, ?_⟩
    obtain ⟨hy11, hy21, hy31, hy41⟩ := cm_Sg_col1 y hy
    rw [cm_mul, Matrix.mul_apply, Fin.sum_univ_five, hy01, hx01, hy11, hy21, hy31, hy41]
    simp
  one_mem' := ⟨Sg.one_mem, by simp [cm_one]⟩
  inv_mem' := by
    rintro x ⟨hx, hx01⟩
    refine ⟨Sg.inv_mem hx, ?_⟩
    obtain ⟨hx11, hx21, hx31, hx41⟩ := cm_Sg_col1 x⁻¹ (Sg.inv_mem hx)
    have hxx : cm (x * x⁻¹) 0 1 = 0 := by rw [mul_inv_cancel, cm_one]; simp
    rw [cm_mul, Matrix.mul_apply, Fin.sum_univ_five, cm_00, hx01, hx11, hx21, hx31, hx41] at hxx
    simpa using hxx

theorem mem_W0_iff (x : Hc) : x ∈ W0 ↔ x ∈ Sg ∧ cm x 0 1 = 0 := Iff.rfl

end CFSG.Quasithin.A94.He42P427H
