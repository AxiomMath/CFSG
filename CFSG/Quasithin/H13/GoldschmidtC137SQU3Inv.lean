module

public import CFSG.Quasithin.H13.GoldschmidtC137SQRkU33
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem no_comm_statedSU {F : Type} [Field F] (hF : Nat.card F = 9) (t b : StatedSU 3 3 F)
    (ht : orderOf t = 2) (hb : orderOf b = 7) : t * b ≠ b * t := by
  intro hcomm
  have h := unitaryFieldData_of_card hF
  have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
    rw [gramForm_e0_left]
    exact one_ne_zero
  set L₀ := lineOf _ hv with hL₀
  set t₀ : StatedSU 3 3 F := (tauLine h hF L₀ : StatedSU 3 3 F) with ht₀def
  have ht₀ : orderOf t₀ = 2 := (tauLine h hF L₀).2
  have hcard : Nat.card (Subgroup.centralizer {t₀}) = 96 :=
    card_centralizer_tauLine (h := h) (hF := hF) (L₀ := L₀) rfl
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_orderOf_eq_two hF ht ht₀)
  have hmem : c * b * c⁻¹ ∈ Subgroup.centralizer {t₀} := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * b * c⁻¹ * (c * t * c⁻¹) = c * (b * t) * c⁻¹ := by group
      _ = c * (t * b) * c⁻¹ := by rw [hcomm]
      _ = c * t * c⁻¹ * (c * b * c⁻¹) := by group
  have hord : orderOf (c * b * c⁻¹) = 7 := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective b
    rw [← hb]
    exact this
  have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer {t₀}) hmem
  rw [hord, hcard] at hdvd
  omega

theorem u3_no_comm_of_lieModel {Y : Type} [Group Y] (h : LieModel Y .PSU 3 3 1) (t b : Y)
    (ht : orderOf t = 2) (hb : orderOf b = 7) : t * b ≠ b * t := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_statedSU_of_lieModel h
  intro hcomm
  refine no_comm_statedSU hF (e t) (e b) ?_ ?_ (by rw [← map_mul, ← map_mul, hcomm])
  · rw [← ht]
    exact orderOf_injective e.toMonoidHom e.injective t
  · rw [← hb]
    exact orderOf_injective e.toMonoidHom e.injective b

end CFSG.Quasithin.H13.U3.GC137.SQ
