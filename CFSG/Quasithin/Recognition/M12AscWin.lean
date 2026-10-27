module

public import CFSG.Quasithin.Recognition.M12AscWinTab
public import CFSG.Quasithin.Recognition.M12AscConj

public section

namespace CFSG.Quasithin

open Subgroup

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem mem_ascQ_symm [Finite G] (hyp : Asc03Hyp G z) {w₁ w₂ : G} (h1 : IsConj z w₁)
    (h2 : IsConj z w₂) (hne : w₁ ≠ w₂) (h : w₂ ∈ ascQ w₁) : w₁ ∈ ascQ w₂ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  obtain ⟨c2, hc2⟩ := isConj_iff.1 h2
  have hh : c⁻¹ * w₂ * c ∈ ascQ z := by
    rw [← hc] at h
    exact (mem_ascQ_conj z c w₂).1 h
  have hdz : (c⁻¹ * c2) * z * (c⁻¹ * c2)⁻¹ = c⁻¹ * w₂ * c := by
    rw [← hc2]
    group
  have hne' : (c⁻¹ * c2) * z * (c⁻¹ * c2)⁻¹ ≠ z := by
    intro e
    apply hne
    rw [hdz] at e
    calc w₁ = c * z * c⁻¹ := hc.symm
      _ = c * (c⁻¹ * w₂ * c) * c⁻¹ := by rw [e]
      _ = w₂ := by group
  have hQ : (c⁻¹ * c2) * z * (c⁻¹ * c2)⁻¹ ∈ ascQ z := by rw [hdz]; exact hh
  have key := (config_of_conj hyp hne' hQ).1
  rw [← hc2, mem_ascQ_conj z c2 w₁]
  have : c2⁻¹ * w₁ * c2 = (c⁻¹ * c2)⁻¹ * z * (c⁻¹ * c2) := by
    rw [← hc]
    group
  rw [this]
  exact key

namespace AscModel

theorem exists_y_window [Finite G] {a : G} (hyp : Asc03Hyp G a) (ma : AscModel a) {p1 p3 p4 : G}
    (h1 : p1 ∈ ascH a) (h3 : p3 ∈ ascH a) (h4 : p4 ∈ ascH a)
    (h33 : p3 * p3 = 1) (h44 : p4 * p4 = 1) (h13 : p1 * p3 = p3 * p1) (h14 : p1 * p4 = p4 * p1)
    (h43 : p4 * p3 * p4 = a * p3) (hF : ma.tb p1 ∈ FTabs) (hne1 : p1 ≠ 1) (hnea : p1 ≠ a)
    (hQ3 : p3 ∉ ascQ a) :
    ∃ y ∈ ascQ a, y * y = a ∧ y * p1 = (p1 * a) * y ∧ y * p4 = (a * (p3 * p1)) * y ∧
      y * p3 = (p1 * p4) * y := by
  have haH : a ∈ ascH a := z_mem_ascH a
  have ht1 : ma.tb p1 ≠ tid := fun e => hne1 ((ma.eq_one_iff h1).2 e)
  have ht1z : ma.tb p1 ≠ zTab := fun e => hnea ((ma.eq_z_iff h1).2 e)
  have ht3q : ma.tb p3 ∉ qTabs := fun e => hQ3 ((ma.mem_ascQ_iff_tb hyp).2 ⟨h3, e⟩)
  have ht33 : tmul (ma.tb p3) (ma.tb p3) = tid := (ma.mul_self_eq_one_iff h3).1 h33
  have ht13 : tmul (ma.tb p1) (ma.tb p3) = tmul (ma.tb p3) (ma.tb p1) :=
    (ma.comm_iff h1 h3).1 h13
  have ht44 : tmul (ma.tb p4) (ma.tb p4) = tid := (ma.mul_self_eq_one_iff h4).1 h44
  have ht14 : tmul (ma.tb p1) (ma.tb p4) = tmul (ma.tb p4) (ma.tb p1) :=
    (ma.comm_iff h1 h4).1 h14
  have ht43 : tmul (tmul (ma.tb p4) (ma.tb p3)) (ma.tb p4) = tmul zTab (ma.tb p3) := by
    have := congrArg ma.tb h43
    rwa [ma.tb_mul (mul_mem h4 h3) h4, ma.tb_mul h4 h3, ma.tb_mul haH h3, ma.tb_z] at this
  obtain ⟨q, hq, hqq, hq1, hq4, hq3⟩ := y_exists_tab _ (ma.tb_mem h1) hF ht1 ht1z _
    (ma.tb_mem h3) ht3q ht33 ht13 _ (ma.tb_mem h4) ht44 ht14 ht43
  have hqH : q ∈ ascHTabs := qTabs_sub q hq
  obtain ⟨y, hyH, hyq⟩ := ma.exists_tb hqH
  have hyQ : y ∈ ascQ a := (ma.mem_ascQ_iff_tb hyp).2 ⟨hyH, by rw [hyq]; exact hq⟩
  refine ⟨y, hyQ, ?_, ?_, ?_, ?_⟩
  · apply ma.tb_inj (mul_mem hyH hyH) haH
    rw [ma.tb_mul hyH hyH, ma.tb_z, hyq]
    exact hqq
  · apply ma.tb_inj (mul_mem hyH h1) (mul_mem (mul_mem h1 haH) hyH)
    rw [ma.tb_mul hyH h1, ma.tb_mul (mul_mem h1 haH) hyH, ma.tb_mul h1 haH, ma.tb_z, hyq]
    exact hq1
  · apply ma.tb_inj (mul_mem hyH h4) (mul_mem (mul_mem haH (mul_mem h3 h1)) hyH)
    rw [ma.tb_mul hyH h4, ma.tb_mul (mul_mem haH (mul_mem h3 h1)) hyH,
      ma.tb_mul haH (mul_mem h3 h1), ma.tb_mul h3 h1, ma.tb_z, hyq]
    exact hq4
  · apply ma.tb_inj (mul_mem hyH h3) (mul_mem (mul_mem h1 h4) hyH)
    rw [ma.tb_mul hyH h3, ma.tb_mul (mul_mem h1 h4) hyH, ma.tb_mul h1 h4, hyq]
    exact hq3

end AscModel

end CFSG.Quasithin
