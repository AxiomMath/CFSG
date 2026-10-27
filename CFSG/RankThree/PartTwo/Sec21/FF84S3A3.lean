module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem a8c8_val_eq_inv : ((a8c8 : A8) : P8) = (m₁ * m₂)⁻¹ := by
  rw [a8c8_val]
  decide +kernel

theorem comm_of_mem_a8Kb (x : A8) (hx : x ∈ a8Kb) :
    (x : P8) * (m₁ * m₂) = (m₁ * m₂) * (x : P8) := by
  have hx' : x ∈ Subgroup.centralizer ({a8c8} : Set A8) := a8Kb_le_centralizer hx
  have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx')
  simp only [Subgroup.coe_mul] at h
  rw [a8c8_val_eq_inv] at h
  exact (Commute.inv_right_iff (a := (x : P8)) (b := m₁ * m₂)).1 h

theorem centralizer_c_eq_map :
    (Subgroup.centralizer ({a8c8} : Set A8)).map (alternatingGroup (Fin 8)).subtype =
      Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 hx
    have h := congrArg Subtype.val hx'
    simp only [Subgroup.coe_mul] at h
    rw [a8c8_val_eq_inv] at h
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, x.2⟩
    exact (Commute.inv_right_iff (a := ((x : A8) : P8)) (b := m₁ * m₂)).1 h
  · rintro ⟨h1, h2⟩
    refine ⟨⟨y, h2⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show y * ((a8c8 : A8) : P8) = ((a8c8 : A8) : P8) * y
    rw [a8c8_val_eq_inv]
    exact Commute.inv_right_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 h1)

theorem formPerm_354_mem : (List.formPerm [3, 5, 4] : P8) ∈ alternatingGroup (Fin 8) := by
  have hd3 : (List.formPerm [3, 5, 4] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  exact Equiv.Perm.mem_alternatingGroup.2 hd3.sign

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
