module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GH74.KGroups.L34Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.GH74.KGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

namespace L34Seven

open CFSG.GH74.KGroups

private def l34SevenCMat : Matrix (Fin 3) (Fin 3) GF4 :=
  !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private def l34SevenXMat : Matrix (Fin 3) (Fin 3) GF4 :=
  !![0, 0, 1; 0, 1, 0; 1, 1, 1]

private def l34SevenCSL : Matrix.SpecialLinearGroup (Fin 3) GF4 :=
  ⟨l34SevenCMat, by rw [Matrix.det_fin_three]; decide⟩

private def l34SevenXSL : Matrix.SpecialLinearGroup (Fin 3) GF4 :=
  ⟨l34SevenXMat, by rw [Matrix.det_fin_three]; decide⟩

private def l34SevenGSL : Matrix.SpecialLinearGroup (Fin 3) GF4 :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by rw [Matrix.det_fin_three]; decide⟩

private theorem l34SevenCSLPowSeven : l34SevenCSL ^ 7 = 1 := by decide +kernel

private theorem l34SevenXSLPowThree : l34SevenXSL ^ 3 = 1 := by decide +kernel

private theorem l34SevenXSLNotMemCenter :
    l34SevenXSL ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4) := by
  intro h
  have h1 : l34SevenGSL * l34SevenXSL = l34SevenXSL * l34SevenGSL :=
    Subgroup.mem_center_iff.mp h l34SevenGSL
  exact (by decide +kernel : l34SevenXSL * l34SevenGSL ≠ l34SevenGSL * l34SevenXSL) h1.symm

private theorem l34SevenXSLMulCSL :
    l34SevenXSL * l34SevenCSL = l34SevenCSL ^ 2 * l34SevenXSL := by
  decide +kernel

private theorem l34SevenGSLMulCSLNe :
    l34SevenGSL * l34SevenCSL ≠ l34SevenCSL * l34SevenGSL := by
  decide +kernel

private theorem l34SevenCSLNotMemCenter :
    l34SevenCSL ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4) := by
  intro h
  exact l34SevenGSLMulCSLNe (Subgroup.mem_center_iff.mp h l34SevenGSL)

private noncomputable def l34SevenQSL :
    Matrix.SpecialLinearGroup (Fin 3) GF4 →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) GF4 :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4))

private theorem l34SevenQSLCSLPowSeven : l34SevenQSL l34SevenCSL ^ 7 = 1 := by
  rw [← map_pow, l34SevenCSLPowSeven, map_one]

private theorem l34SevenQSLCSLNeOne : l34SevenQSL l34SevenCSL ≠ 1 := by
  intro h
  have hker : l34SevenCSL ∈ MonoidHom.ker l34SevenQSL := MonoidHom.mem_ker.mpr h
  have hmem : l34SevenCSL ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4) := by
    simpa [l34SevenQSL, QuotientGroup.ker_mk'] using hker
  exact l34SevenCSLNotMemCenter hmem

private theorem l34SevenNotSevenDvdIndex {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (hH : Nat.card H = 7) (hG : Nat.card G = 20160) :
    ¬ 7 ∣ H.index := by
  intro h
  have hmul : H.index * 7 = 20160 := by
    rw [← hH, Subgroup.index_mul_card, hG]
  obtain ⟨k, hk⟩ := h
  have h49 : 49 ∣ 20160 := by
    refine ⟨k, ?_⟩
    calc 20160 = H.index * 7 := hmul.symm
      _ = (7 * k) * 7 := by rw [hk]
      _ = 49 * k := by ring
  obtain ⟨m, hm⟩ := h49
  omega

end L34Seven

open L34Seven

theorem K_L34Seven : ∀ (X : Type) [Group X] [Finite X], IsL3 X 2 →
    ∀ C : Subgroup X, Nat.card C = 7 →
      ∃ x ∈ Subgroup.normalizer (C : Set X), orderOf x = 3 ∧
        ∀ c ∈ C, x * c * x⁻¹ = c ^ 2 := by
  classical
  intro X _ _ hX C hC
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel
    (K := X) (F := GF4) 3 2 2 (by norm_num)
      (by rw [Nat.card_eq_fintype_card]; decide) hX
  let P := Matrix.ProjectiveSpecialLinearGroup (Fin 3) GF4
  have hcardP : Nat.card P = 20160 := CFSG.GH74.KGroups.L34.card_psl
  let C' : Subgroup P := C.map e.toMonoidHom
  have hC'card : Nat.card C' = 7 := by
    rw [Subgroup.card_map_of_injective e.injective, hC]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hC'p : IsPGroup 7 C' := IsPGroup.of_card (n := 1) (by rw [hC'card]; norm_num)
  have hC'index : ¬ 7 ∣ C'.index :=
    l34SevenNotSevenDvdIndex C' hC'card hcardP
  let C'Sylow : Sylow 7 P := hC'p.toSylow hC'index
  let cP : P := l34SevenQSL l34SevenCSL
  let xP : P := l34SevenQSL l34SevenXSL
  have hxP3 : xP ^ 3 = 1 := by
    rw [show xP = l34SevenQSL l34SevenXSL from rfl, ← map_pow, l34SevenXSLPowThree, map_one]
  have hxPne : xP ≠ 1 := by
    intro h
    have hker : l34SevenXSL ∈ MonoidHom.ker l34SevenQSL := MonoidHom.mem_ker.mpr h
    exact l34SevenXSLNotMemCenter (by simpa [l34SevenQSL, QuotientGroup.ker_mk'] using hker)
  have hxPorder : orderOf xP = 3 := orderOf_eq_prime hxP3 hxPne
  let C0 : Subgroup P := Subgroup.zpowers cP
  have hcP7 : cP ^ 7 = 1 := l34SevenQSLCSLPowSeven
  have hcPne : cP ≠ 1 := l34SevenQSLCSLNeOne
  have hcPorder : orderOf cP = 7 := orderOf_eq_prime hcP7 hcPne
  have hC0card : Nat.card C0 = 7 := by
    dsimp only [C0]
    rw [Nat.card_zpowers, hcPorder]
  have hC0p : IsPGroup 7 C0 := IsPGroup.of_card (n := 1) (by rw [hC0card]; norm_num)
  have hC0index : ¬ 7 ∣ C0.index :=
    l34SevenNotSevenDvdIndex C0 hC0card hcardP
  let C0Sylow : Sylow 7 P := hC0p.toSylow hC0index
  have hxP_cP_eq : xP * cP = cP ^ 2 * xP := by
    have h := congrArg l34SevenQSL l34SevenXSLMulCSL
    simpa [xP, cP, map_mul, map_pow] using h
  have hxP_cP : xP * cP * xP⁻¹ = cP ^ 2 := by
    rw [hxP_cP_eq, mul_assoc, mul_inv_cancel, mul_one]
  have hx0sq : ∀ c0 ∈ C0, xP * c0 * xP⁻¹ = c0 ^ 2 := by
    intro c0 hc0
    dsimp only [C0] at hc0
    have hfin : IsOfFinOrder cP := by
      rw [← orderOf_ne_zero_iff, hcPorder]
      norm_num
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hc0
    obtain ⟨n, -, hnc0⟩ := hc0
    rw [← hnc0]
    calc xP * cP ^ n * xP⁻¹
        = (MulAut.conj xP) (cP ^ n) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj xP) cP) ^ n := map_pow _ _ _
      _ = (cP ^ 2) ^ n := by rw [MulAut.conj_apply, hxP_cP]
      _ = (cP ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have : Finite (Sylow 7 P) := by
    have : (C0Sylow : Subgroup P).FiniteIndex := Subgroup.finiteIndex_of_finite
    exact Sylow.finite_of_finiteIndex C0Sylow
  obtain ⟨g, hg⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := P) (α := Sylow 7 P) C0Sylow C'Sylow
  have hC'eq : (fun x : P => g * x * g⁻¹) '' (C0 : Set P) = (C' : Set P) := by
    have h := congrArg (fun S : Sylow 7 P => (S : Set P)) hg
    rw [Sylow.coe_smul] at h
    have h0 : (C0Sylow : Set P) = (C0 : Set P) := rfl
    have h1 : (C'Sylow : Set P) = (C' : Set P) := rfl
    rw [h0, h1] at h
    rw [← Set.image_smul] at h
    simpa [MulAut.smul_def, MulAut.conj_apply] using h
  let x' : P := g * xP * g⁻¹
  have hx'order : orderOf x' = 3 := by
    rw [show x' = MulAut.conj g xP from rfl]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) xP).trans hxPorder
  have hx'sq : ∀ c' ∈ C', x' * c' * x'⁻¹ = c' ^ 2 := by
    intro c' hc'
    change c' ∈ (C' : Set P) at hc'
    rw [← hC'eq, Set.mem_image] at hc'
    obtain ⟨c0, hc0, hc0eq⟩ := hc'
    rw [← hc0eq]
    calc (g * xP * g⁻¹) * (g * c0 * g⁻¹) * (g * xP * g⁻¹)⁻¹
        = g * (xP * c0 * xP⁻¹) * g⁻¹ := by group
      _ = g * c0 ^ 2 * g⁻¹ := by rw [hx0sq c0 hc0]
      _ = (g * c0 * g⁻¹) ^ 2 := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  let xX : X := e.symm x'
  have hxX : ∀ c ∈ C, xX * c * xX⁻¹ = c ^ 2 := by
    intro c hc
    apply e.injective
    have hc' : e c ∈ C' := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    calc e (xX * c * xX⁻¹)
        = e xX * e c * (e xX)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = x' * e c * x'⁻¹ := by rw [show e xX = x' from e.apply_symm_apply x']
      _ = (e c) ^ 2 := hx'sq (e c) hc'
      _ = e (c ^ 2) := by rw [map_pow]
  have hxXnorm : xX ∈ Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge (H := C.map (MulAut.conj xX)) (K := C)
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      change xX * c * xX⁻¹ ∈ C
      rw [hxX c hc]
      exact C.pow_mem hc 2
    · rw [Subgroup.card_map_of_injective (MulAut.conj xX).injective]
  have hxXorder : orderOf xX = 3 := by
    rw [show xX = e.symm x' from rfl]
    exact (MulEquiv.orderOf_eq e.symm x').trans hx'order
  exact ⟨xX, hxXnorm, hxXorder, hxX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
