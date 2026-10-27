module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem sup_inf_centralizer_le_right_of_inf_conjSubgroup_eq_bot {V A₁ C : Subgroup G} {y : G}
    (hVy : V ⊓ conjSubgroup V y⁻¹ = ⊥) (hA₁V : A₁ ≤ V)
    (hAC : ∀ a ∈ A₁, ∀ c ∈ C, a * c = c * a)
    (hyC : C ≤ Subgroup.centralizer ({y} : Set G)) :
    (A₁ ⊔ C) ⊓ Subgroup.centralizer ({y} : Set G) ≤ C := by
  have hnorm : A₁ ≤ Subgroup.normalizer (C : Set G) := fun a ha =>
    centralizer_le_normalizer (C : Set G)
      (mem_centralizer_iff.2 fun c hc => (hAC a ha c hc).symm)
  intro m hm
  obtain ⟨hmM, hmCen⟩ := mem_inf.1 hm
  have hym : y * m = m * y := (mem_centralizer_iff.1 hmCen) y (by simp)
  have hmM' : m ∈ (A₁ : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A₁ C hnorm]
    exact hmM
  obtain ⟨x, hx, c, hc, hxcm⟩ := Set.mem_mul.1 hmM'
  have hxy : y * x = x * y := by
    have hcy : y * c = c * y := (mem_centralizer_iff.1 (hyC hc)) y (by simp)
    have hcalc : y * x * c = x * y * c := by
      calc y * x * c = y * (x * c) := by group
        _ = y * m := by rw [hxcm]
        _ = m * y := hym
        _ = (x * c) * y := by rw [hxcm]
        _ = x * (c * y) := by group
        _ = x * (y * c) := by rw [hcy]
        _ = x * y * c := by group
    exact mul_right_cancel hcalc
  have hxconj : x ∈ conjSubgroup V y⁻¹ := by
    rw [mem_conjSubgroup_iff, inv_inv]
    have hxx : y⁻¹ * x * y = x := by
      rw [mul_assoc, ← hxy, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hxx]
    exact hA₁V hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hVy]
    exact mem_inf.2 ⟨hA₁V hx, hxconj⟩
  have hx1 : x = 1 := mem_bot.1 hxbot
  rw [← hxcm, hx1, one_mul]
  exact hc

theorem inf_ne_bot_of_inf_ne_bot_of_inf_conjSubgroup_eq_bot [Finite G]
    {V A₁ C P : Subgroup G} {y : G} (hVy : V ⊓ conjSubgroup V y⁻¹ = ⊥) (hA₁V : A₁ ≤ V)
    (hM : ∀ a ∈ A₁ ⊔ C, ∀ b ∈ A₁ ⊔ C, a * b = b * a)
    (hyM : y ∈ Subgroup.normalizer ((A₁ ⊔ C : Subgroup G) : Set G))
    (hyC : C ≤ Subgroup.centralizer ({y} : Set G)) (hPM : P ≤ A₁ ⊔ C)
    (hyP : y ∈ Subgroup.normalizer (P : Set G)) (hPV : P ⊓ V ≠ ⊥) :
    P ⊓ C ≠ ⊥ := by
  by_contra hPC
  have hAC : ∀ a ∈ A₁, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    hM a (mem_sup_left ha) c (mem_sup_right hc)
  have hnorm : A₁ ≤ Subgroup.normalizer (C : Set G) := fun a ha =>
    centralizer_le_normalizer (C : Set G)
      (mem_centralizer_iff.2 fun c hc => (hAC a ha c hc).symm)
  have hcoe : ((A₁ ⊔ C : Subgroup G) : Set G) = (A₁ : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A₁ C hnorm
  have hPfree : P ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
    apply le_bot_iff.1
    intro z hz
    obtain ⟨hzP, hzCen⟩ := mem_inf.1 hz
    have hzM : z ∈ A₁ ⊔ C := hPM hzP
    have hzC : z ∈ C :=
      sup_inf_centralizer_le_right_of_inf_conjSubgroup_eq_bot hVy hA₁V hAC hyC
        (mem_inf.2 ⟨hzM, hzCen⟩)
    exact hPC ▸ mem_inf.2 ⟨hzP, hzC⟩
  obtain ⟨⟨a, haPV⟩, ha_ne⟩ := ne_bot_iff_exists_ne_one.mp hPV
  have haP : a ∈ P := (mem_inf.1 haPV).1
  have haV : a ∈ V := (mem_inf.1 haPV).2
  have ha_ne1 : a ≠ 1 := fun h => ha_ne (Subtype.ext h)
  obtain ⟨q, hqP, haq⟩ := exists_eq_inv_mul_conj_of_inf_centralizer hyP hPfree a haP
  have hqM : q ∈ A₁ ⊔ C := hPM hqP
  have hqM' : q ∈ (A₁ : Set G) * (C : Set G) := by
    rw [← hcoe]
    exact hqM
  obtain ⟨x, hx, c, hc, hxcq⟩ := Set.mem_mul.1 hqM'
  set x' : G := y * x * y⁻¹ with hx'def
  have hcy : y * c = c * y := (mem_centralizer_iff.1 (hyC hc)) y (by simp)
  have hyq : y * (x * c) * y⁻¹ = x' * c := by
    calc y * (x * c) * y⁻¹ = (y * x * y⁻¹) * (y * c * y⁻¹) := by group
      _ = x' * c := by rw [hx'def, hcy]; group
  have hx'M : x' ∈ A₁ ⊔ C := (mem_normalizer_iff.1 hyM x).1 (mem_sup_left hx)
  have hx'invM : x⁻¹ ∈ A₁ ⊔ C := mem_sup_left (A₁.inv_mem hx)
  have hcomm : (x⁻¹ * x') * c = c * (x⁻¹ * x') :=
    hM (x⁻¹ * x') ((A₁ ⊔ C).mul_mem hx'invM hx'M) c (mem_sup_right hc)
  have hax' : a = x⁻¹ * x' := by
    have h1 : a = c⁻¹ * x⁻¹ * (x' * c) := by
      rw [haq, ← hxcq, hyq, mul_inv_rev]
    rw [h1]
    calc c⁻¹ * x⁻¹ * (x' * c) = c⁻¹ * ((x⁻¹ * x') * c) := by group
      _ = c⁻¹ * (c * (x⁻¹ * x')) := by rw [hcomm]
      _ = x⁻¹ * x' := by group
  have hx'xa : x' = x * a := by
    rw [hax']
    group
  have hx'V : x' ∈ V := by
    rw [hx'xa]
    exact V.mul_mem (hA₁V hx) haV
  have hx'conj : x' ∈ conjSubgroup V y⁻¹ := by
    rw [mem_conjSubgroup_iff, inv_inv]
    have hxx : y⁻¹ * x' * y = x := by rw [hx'def]; group
    rw [hxx]
    exact hA₁V hx
  have hx'bot : x' ∈ (⊥ : Subgroup G) := by
    rw [← hVy]
    exact mem_inf.2 ⟨hx'V, hx'conj⟩
  have hx'1 : x' = 1 := mem_bot.1 hx'bot
  have hx1 : x = 1 := by
    have hyx1 : y * x * y⁻¹ = 1 := by rw [← hx'def]; exact hx'1
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = y⁻¹ * 1 * y := by rw [hyx1]
      _ = 1 := by group
  exact ha_ne1 (by rw [hax', hx1, hx'1]; group)

end CFSG.LocalAnalysis.WeakClosure81
