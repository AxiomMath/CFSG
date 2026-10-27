module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenG
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.inf_centralizer_eq_of_inf_centralizer_eq_bot (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hBC : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) = ⊥) {b : G}
    (hb : b ∈ conjSubgroup V₀ g) (hb1 : b ≠ 1) :
    eSub V₀ X T ⊓ centralizer (conjSubgroup V₀ g : Set G) =
      eSub V₀ X T ⊓ centralizer ({b} : Set G) := by
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hTI : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V₀ g) :=
    isTI_conjSubgroup_quasithin hX.cex.hyp.isTI g
  have hBX : conjSubgroup V₀ g ≤ X :=
    (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le).trans hX.mem.2.2.A_le
  have hBnorm : conjSubgroup V₀ g ≤ normalizer (eSub V₀ X T : Set G) :=
    hBX.trans (le_normalizer_conjClosure (V₀ ⊓ centralizer (T : Set G)) X)
  have hEB : eSub V₀ X T ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ centralizer (eSub V₀ X T : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        B2F.isElemAbelian_comm (Hyp167.isElemAbelian_eSub h1 hS hV₀ hX) hy hx.1
    have hx' : x ∈ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) := ⟨hx.2, hxC⟩
    rwa [hBC] at hx'
  exact eight_one hTI le_rfl hBnorm hEB hb hb1

theorem Hyp167.quad_of_inf_centralizer_eq_bot (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hBC : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) = ⊥) :
    ∀ a ∈ conjSubgroup V₀ g, ∀ b ∈ conjSubgroup V₀ g, ∀ e ∈ conjClosure V X,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹ := by
  intro a ha b hb e he
  by_cases hb1 : b = 1
  · subst hb1
    simp
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hIel : IsElemAbelian 2 (conjClosure V X) := Hyp167.isElemAbelian_I h1 hS hX hVO
  have hBel : IsElemAbelian 2 (conjSubgroup V₀ g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.elemAbelian₀ g
  have hb2 : b * b = 1 := by simpa [pow_two] using hBel.2 b hb
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hBX : conjSubgroup V₀ g ≤ X :=
    (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le).trans hX.mem.2.2.A_le
  have hBnorm : conjSubgroup V₀ g ≤ normalizer (conjClosure V X : Set G) :=
    hBX.trans (le_normalizer_conjClosure V X)
  have hEI : eSub V₀ X T ≤ conjClosure V X :=
    conjClosure_mono (inf_le_left.trans hX.cex.hyp.h6.le) le_rfl
  have hcI : b * e * b⁻¹ * e⁻¹ ∈ conjClosure V X := by
    have hf : b * e * b⁻¹ ∈ conjClosure V X :=
      (Subgroup.mem_normalizer_iff.1 (hBnorm hb) e).1 he
    exact (conjClosure V X).mul_mem hf ((conjClosure V X).inv_mem he)
  have hc2 : (b * e * b⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) = 1 := by
    simpa [pow_two] using hIel.2 (b * e * b⁻¹ * e⁻¹) hcI
  have hbc : b * (b * e * b⁻¹ * e⁻¹) * b⁻¹ = b * e * b⁻¹ * e⁻¹ := by
    have he1 : b * (b * e * b⁻¹ * e⁻¹) * b⁻¹ = (b * e * b⁻¹ * e⁻¹)⁻¹ := by
      have h1 : b * (b * e * b⁻¹ * e⁻¹) * b⁻¹ =
          (b * b) * e * b⁻¹ * e⁻¹ * b⁻¹ := by group
      rw [h1, hb2, one_mul]
      simp [mul_assoc, hbb]
    rw [he1]
    exact inv_eq_of_mul_eq_one_right hc2
  have hcomm : b * (b * e * b⁻¹ * e⁻¹) = (b * e * b⁻¹ * e⁻¹) * b :=
    mul_inv_eq_iff_eq_mul.1 hbc
  have hIB : conjClosure V X ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ centralizer (eSub V₀ X T : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        B2F.isElemAbelian_comm hIel (hEI hy) hx.1
    have hx' : x ∈ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) := ⟨hx.2, hxC⟩
    rwa [hBC] at hx'
  have hcC : b * e * b⁻¹ * e⁻¹ ∈
      conjClosure V X ⊓ centralizer ({b} : Set G) :=
    ⟨hcI, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm⟩
  rw [← eight_one (isTI_conjSubgroup_quasithin hX.cex.hyp.isTI g) le_rfl hBnorm hIB hb hb1]
    at hcC
  exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hcC.2 a ha)

end CFSG.LocalAnalysis.WeakClosure81

end
