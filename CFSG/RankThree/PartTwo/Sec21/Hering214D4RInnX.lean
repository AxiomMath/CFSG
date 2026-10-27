module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RLine
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RSL3
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Model
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

theorem eq_of_sl3Order_eq {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t)
    (h : s ^ 3 * ((s ^ 2 - 1) * (s ^ 3 - 1)) = t ^ 3 * ((t ^ 2 - 1) * (t ^ 3 - 1))) : s = t := by
  rw [← mul_assoc, ← mul_assoc] at h
  rcases lt_trichotomy s t with hst | hst | hst
  · exact absurd h (KFacts.sl3Order_lt (by omega) hst).ne
  · exact hst
  · exact absurd h.symm (KFacts.sl3Order_lt (by omega) hst).ne

section InnX


variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem inner_classX_four (P : D4Par n F σ) (hn : 2 ≤ n) (hev : Even n) {g₁ g₂ x : C0 σ}
    (hX : IsClassX σ g₁) (hg₂3 : g₂ ^ 3 = 1) (hg₂1 : g₂ ≠ 1) (h₁₂ : g₂ * g₁ = g₁ * g₂)
    (hx₁ : x * g₁ = g₁ * x) (hx₂ : x * g₂ * x⁻¹ = g₂⁻¹) :
    FourFixedMoved (MulAut.conj g₁) (MulAut.conj g₂) := by
  obtain ⟨Fq, _, _, h4, h3, e, hact⟩ := Sec4.E27.layer_linear_model P hn hev hX
  have hxc : x ∈ Sec4.E27.cenX σ g₁ := Subgroup.mem_centralizer_singleton_iff.mpr hx₁
  have hg₂c : g₂ ∈ Sec4.E27.cenX σ g₁ := Subgroup.mem_centralizer_singleton_iff.mpr h₁₂
  have hg₂D : g₂ ∈ Sec4.E27.layerSub σ g₁ := by
    have h1 : ⁅x, g₂⁆ ∈ Sec4.E27.layerSub σ g₁ := Subgroup.commutator_mem_commutator hxc hg₂c
    rwa [commutator_eq_of_inverts hx₂ hg₂3] at h1
  have hcard : Nat.card Fq = 2 ^ n := by
    have hD' := Sec4.E27.layer_card_even P hn hev hX
    have hS := CFSG.LieType.SteinbergBR.BlockPar.card_SL_three' (F := Fq)
    rw [Nat.card_congr e.toEquiv, hS] at hD'
    have hq4 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact eq_of_sl3Order_eq (by omega) hq4 hD'
  haveI : CharP Fq 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  obtain ⟨ω, hω, hω1⟩ := exists_primitive_cube_root h3
  obtain ⟨d₂, hd₂⟩ : ∃ d₂ : Sec4.E27.layerSub σ g₁, d₂ = ⟨g₂, hg₂D⟩ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Matrix.SpecialLinearGroup (Fin 3) Fq, h = e d₂ := ⟨_, rfl⟩
  have hd₂c : ((d₂ : Sec4.E27.layerSub σ g₁) : C0 σ) = g₂ := by rw [hd₂]
  have hh3 : h ^ 3 = 1 := by
    rw [hh, ← map_pow]
    have : d₂ ^ 3 = 1 := Subtype.ext (by simpa [hd₂c] using hg₂3)
    rw [this, map_one]
  have hh1 : h ≠ 1 := by
    intro hc
    apply hg₂1
    have : d₂ = 1 := e.injective ((hh ▸ hc).trans (map_one e).symm)
    rw [← hd₂c, this]
    rfl
  have hhc : (h : Matrix (Fin 3) (Fin 3) Fq) ^ 3 = (1 : Fq) • 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hh3, one_smul]
    rfl
  have hns : ∀ a : Fq, (h : Matrix (Fin 3) (Fin 3) Fq) ≠ a • 1 := by
    intro a ha
    obtain ⟨N, hN⟩ := hact x hxc
    have hinv := hN d₂ d₂⁻¹ (by
      simp only [Subgroup.coe_inv, hd₂c]
      exact hx₂.symm)
    have h1 : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) Fq) :
        Matrix (Fin 3) (Fin 3) Fq) =
        (N : Matrix (Fin 3) (Fin 3) Fq) * (h : Matrix (Fin 3) (Fin 3) Fq) *
          ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 3) Fq) : Matrix (Fin 3) (Fin 3) Fq) := by
      rw [← hh] at hinv
      rw [← hinv, hh, map_inv]
    have hNN : (N : Matrix (Fin 3) (Fin 3) Fq) *
        ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 3) Fq) : Matrix (Fin 3) (Fin 3) Fq) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [ha, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hNN] at h1
    have h2 : h⁻¹ = h := Subtype.ext (h1.trans ha.symm)
    have h3' : h * h = 1 := by
      calc h * h = h * h⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel h
    apply hh1
    calc h = h * h * h := by rw [h3', one_mul]
      _ = h ^ 3 := by rw [pow_three']
      _ = 1 := hh3
  obtain ⟨U, hUab, hU4, hUn, u₀, hu₀, hmove⟩ := sl3_four_of_pow_three hω h 1 hhc hns
  refine ⟨(U.map e.symm.toMonoidHom).map (Sec4.E27.layerSub σ g₁).subtype,
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hUab _) _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Sec4.E27.layerSub σ g₁).subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hU4]
  ·
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hwc : (e.symm u : C0 σ) ∈ Sec4.E27.cenX σ g₁ := by
      have hDc : Sec4.E27.layerSub σ g₁ ≤ Sec4.E27.cenX σ g₁ := by
        refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
        rw [commutatorElement_def]
        exact (Sec4.E27.cenX σ g₁).mul_mem ((Sec4.E27.cenX σ g₁).mul_mem
          ((Sec4.E27.cenX σ g₁).mul_mem ha hb) ((Sec4.E27.cenX σ g₁).inv_mem ha))
          ((Sec4.E27.cenX σ g₁).inv_mem hb)
      exact hDc (e.symm u).2
    have := Subgroup.mem_centralizer_singleton_iff.mp hwc
    rw [MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr this.symm
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨e.symm (h * u * h⁻¹), ⟨h * u * h⁻¹, hUn u hu, rfl⟩, ?_⟩
    have : e.symm h = d₂ := by rw [hh]; exact e.symm_apply_apply d₂
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, map_mul, map_inv, this,
      Subgroup.coe_mul, InvMemClass.coe_inv, hd₂c]
    rw [MulAut.conj_apply]
  · refine ⟨((e.symm u₀ : Sec4.E27.layerSub σ g₁) : C0 σ), ⟨_, ⟨u₀, hu₀, rfl⟩, rfl⟩,
      fun hcon => hmove ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    have : e.symm h = d₂ := by rw [hh]; exact e.symm_apply_apply d₂
    simp only [map_mul, map_inv, this, Subgroup.coe_mul, InvMemClass.coe_inv, hd₂c]
    rw [MulAut.conj_apply] at hcon
    exact hcon

end InnX

end CFSG.RankThree.PartTwo.Sec21.Hering214
