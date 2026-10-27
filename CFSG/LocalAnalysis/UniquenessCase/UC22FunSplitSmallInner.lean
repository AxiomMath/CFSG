module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem mem_range_conj_of_odd_of_card_three (hF : Nat.card F = 3)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →*
      MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  classical
  obtain ⟨ρ⟩ := CFSG.ClassicalInvolution.Q3.Q3T6.Fa.nonempty_ringEquiv_zmod_three hF
  let e : SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) (ZMod 3) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.slMap2 ρ
  let β : MulAut (SpecialLinearGroup (Fin 2) (ZMod 3)) := MulAut.congr e α
  have hβodd : Odd (orderOf β) := by
    rw [show orderOf β = orderOf α from MulEquiv.orderOf_eq (MulAut.congr e) α]
    exact hα
  have hβ2 : β ^ 2 ∈ CFSG.ClassicalInvolution.Q3.Q3T6.inn3 :=
    Subgroup.sq_mem_of_index_two CFSG.ClassicalInvolution.Q3.Q3T6.inn3_index β
  have hβzp : β ∈ Subgroup.zpowers (β ^ 2) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.coprime_two_right.mpr hβodd).symm)
  have hβinn : β ∈ CFSG.ClassicalInvolution.Q3.Q3T6.inn3 :=
    (Subgroup.zpowers_le.mpr hβ2) hβzp
  obtain ⟨g, hg⟩ := (CFSG.ClassicalInvolution.Q3.Q3T6.mem_inn3_iff).mp hβinn
  refine ⟨e.symm g, ?_⟩
  ext x : 1
  apply e.injective
  calc
    e ((MulAut.conj (e.symm g)) x) = g * e x * g⁻¹ := by
      simp [MulAut.conj_apply]
    _ = (MulAut.conj g) (e x) := by rw [MulAut.conj_apply]
    _ = β (e x) := by rw [hg]
    _ = e (α x) := by simp [β, MulAut.congr_apply]

theorem exists_inner_normalizer_aut_of_card_three (hF : Nat.card F = 3)
    {Y : Type} [Group Y] [Finite Y]
    (φ : SpecialLinearGroup (Fin 2) F →* Y)
    (hφ : Function.Injective φ)
    {g : Y} (hgN : g ∈ Subgroup.normalizer (φ.range : Set Y))
    (hgodd : Odd (orderOf g)) :
    ∃ y : SpecialLinearGroup (Fin 2) F,
      ∀ x : SpecialLinearGroup (Fin 2) F,
        g * φ x * g⁻¹ = φ y * φ x * (φ y)⁻¹ := by
  classical
  let H := φ.range
  let e : SpecialLinearGroup (Fin 2) F ≃* H := MonoidHom.ofInjective hφ
  let act : MulAut H := H.normalizerMonoidHom ⟨g, hgN⟩
  let α : MulAut (SpecialLinearGroup (Fin 2) F) := e.trans (act.trans e.symm)
  have hact_dvd : orderOf act ∣ orderOf g := by
    simpa [Subgroup.orderOf_mk] using
      orderOf_map_dvd H.normalizerMonoidHom ⟨g, hgN⟩
  have hact_odd : Odd (orderOf act) := Odd.of_dvd_nat hgodd hact_dvd
  have hα_eq : α = (MulAut.congr e).symm act := by
    exact (MulAut.congr_symm_apply e act).symm
  have hα_order : orderOf α = orderOf act := by
    rw [hα_eq]
    exact MulEquiv.orderOf_eq ((MulAut.congr e).symm) act
  have hα_odd : Odd (orderOf α) := by
    rw [hα_order]
    exact hact_odd
  have hα_apply : ∀ x : SpecialLinearGroup (Fin 2) F, e (α x) = act (e x) := by
    intro x
    simp [α]
  have hφ_alpha : ∀ x : SpecialLinearGroup (Fin 2) F,
      (φ (α x) : Y) = g * φ x * g⁻¹ := by
    intro x
    have h := congrArg Subtype.val (hα_apply x)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    have h1 : ((e (α x) : H) : Y) = φ (α x) :=
      MonoidHom.ofInjective_apply hφ
    have h2 : ((e x : H) : Y) = φ x :=
      MonoidHom.ofInjective_apply hφ
    rw [h1, h2] at h
    simpa using h
  obtain ⟨y, hy⟩ := mem_range_conj_of_odd_of_card_three hF α hα_odd
  refine ⟨y, fun x => ?_⟩
  calc
    g * φ x * g⁻¹ = (φ (α x) : Y) := (hφ_alpha x).symm
    _ = φ ((MulAut.conj y) x) := by rw [← hy]
    _ = φ y * φ x * (φ y)⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem normalizerMonoidHom_mem_range_conj_of_equiv_sl2_three
    {X : Type} [Group X] [Finite X]
    {K : Subgroup X} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3)
    (e : K ≃* SpecialLinearGroup (Fin 2) F)
    {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hodd : Odd (orderOf g)) :
    K.normalizerMonoidHom ⟨g, hg⟩ ∈
      (MulAut.conj : K →* MulAut K).range := by
  classical
  let act : MulAut K := K.normalizerMonoidHom ⟨g, hg⟩
  have hact_dvd : orderOf act ∣ orderOf g := by
    simpa [Subgroup.orderOf_mk] using
      orderOf_map_dvd K.normalizerMonoidHom ⟨g, hg⟩
  have hact_odd : Odd (orderOf act) := Odd.of_dvd_nat hodd hact_dvd
  let α : MulAut (SpecialLinearGroup (Fin 2) F) := MulAut.congr e act
  have hα_order : orderOf α = orderOf act :=
    MulEquiv.orderOf_eq (MulAut.congr e) act
  have hα_odd : Odd (orderOf α) := by
    rw [hα_order]
    exact hact_odd
  obtain ⟨y, hy⟩ := mem_range_conj_of_odd_of_card_three hF α hα_odd
  refine ⟨e.symm y, ?_⟩
  ext k : 1
  apply e.injective
  calc
    e ((MulAut.conj (e.symm y)) k) = y * e k * y⁻¹ := by
      simp [MulAut.conj_apply]
    _ = (MulAut.conj y) (e k) := by rw [MulAut.conj_apply]
    _ = α (e k) := by rw [hy]
    _ = e (act k) := by simp [α, MulAut.congr_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
