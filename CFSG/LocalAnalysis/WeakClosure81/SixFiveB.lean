module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveA
import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem centralizer_le_conjM (h : Hyp65 n M V₀ V g) {x : G} (hx : x ∈ conjSubgroup V₀ g)
    (hx1 : x ≠ 1) : centralizer ({x} : Set G) ≤ conjSubgroup M g := by
  exact centralizer_le_M_of_mem_V₀ (M := conjSubgroup M g) (V₀ := conjSubgroup V₀ g)
    h.swap.isTI h.swap.normalizer₀ hx hx1

theorem V₀_inf_conjV (h : Hyp65 n M V₀ V g) : V₀ ⊓ conjSubgroup V g = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  have hxV0 : x ∈ V₀ := hx.1
  have hxVg : x ∈ conjSubgroup V g := hx.2
  have hcen : centralizer ({x} : Set G) ≤ M :=
    centralizer_le_M_of_mem_V₀ h.isTI h.normalizer₀ hxV0 hx1
  have hVg_le : conjSubgroup V g ≤ centralizer ({x} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (IsElemAbelian.comm h.swap.elemAbelian hw hxVg).symm
  exact h.not_conjV_le_M (hVg_le.trans hcen)

theorem conjV₀_inf_V (h : Hyp65 n M V₀ V g) : conjSubgroup V₀ g ⊓ V = ⊥ := by
  have hh := V₀_inf_conjV h.swap
  rw [conjSubgroup_conjSubgroup_inv] at hh
  exact hh

theorem Z0_le_U (h : Hyp65 n M V₀ V g) : Z0Of M V₀ g ≤ UOf M V g := by
  unfold Z0Of UOf
  exact inf_le_inf_right _ h.le

theorem Y_le_B (h : Hyp65 n M V₀ V g) : YOf M V₀ g ≤ BOf M V g := by
  unfold YOf BOf
  exact inf_le_inf_right _ (conjSubgroup_mono h.le g)

theorem Z0_ne_bot (h : Hyp65 n M V₀ V g) : Z0Of M V₀ g ≠ ⊥ := by
  exact h.inCalO1.1.1.2.2 h.ne_bot

theorem Y_ne_bot (h : Hyp65 n M V₀ V g) : YOf M V₀ g ≠ ⊥ := by
  exact h.inCalO1.1.2.2.2 h.ne_bot

theorem Y_le_centralizer_U (h : Hyp65 n M V₀ V g) :
    YOf M V₀ g ≤ centralizer (UOf M V g : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hyVg : y ∈ conjSubgroup V₀ g := hy.1
  have hyM : y ∈ M := hy.2
  have huV : u ∈ V := hu.1
  have huMg : u ∈ conjSubgroup M g := hu.2
  have hyN : y ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hyM
  have huN : u ∈ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [h.swap.normalizer₀]; exact huMg
  have hcV : y * u * y⁻¹ * u⁻¹ ∈ V := by
    have hyu : y * u * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN u).1 huV
    exact V.mul_mem hyu (V.inv_mem huV)
  have hcV0 : y * u * y⁻¹ * u⁻¹ ∈ conjSubgroup V₀ g := by
    have huy : u * y⁻¹ * u⁻¹ ∈ conjSubgroup V₀ g :=
      (Subgroup.mem_normalizer_iff.1 huN y⁻¹).1 ((conjSubgroup V₀ g).inv_mem hyVg)
    simpa only [mul_assoc] using (conjSubgroup V₀ g).mul_mem hyVg huy
  have hmem : y * u * y⁻¹ * u⁻¹ ∈ conjSubgroup V₀ g ⊓ V := ⟨hcV0, hcV⟩
  rw [conjV₀_inf_V h] at hmem
  have hc1 : ⁅y, u⁆ = 1 := by
    rw [commutatorElement_def]
    exact Subgroup.mem_bot.1 hmem
  exact (commutatorElement_eq_one_iff_mul_comm.1 hc1).symm

theorem Z0_le_centralizer_B (h : Hyp65 n M V₀ V g) :
    Z0Of M V₀ g ≤ centralizer (BOf M V g : Set G) := by
  have hh := Y_le_centralizer_U h.swap
  rw [YOf_swap, UOf_swap] at hh
  exact hh

theorem Y_le_cTilde (h : Hyp65 n M V₀ V g) : YOf M V₀ g ≤ F11.CTilde M V₀ V := by
  intro y hy
  have hyB : y ∈ BOf M V g := Y_le_B h hy
  have hyC : y ∈ centralizer (UOf M V g : Set G) := Y_le_centralizer_U h hy
  exact h.inCalO1.2.1 (show y ∈ conjSubgroup V g ⊓ M ⊓
    centralizer ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) from ⟨hyB, hyC⟩)

theorem commutator_Y_V_le_Z0 (h : Hyp65 n M V₀ V g) :
    ⁅YOf M V₀ g, V⁆ ≤ Z0Of M V₀ g := by
  rw [Subgroup.commutator_le]
  intro y hy v hv
  by_cases hy1 : y = 1
  · rw [hy1, commutatorElement_def]
    simp
  · have hyVg : y ∈ conjSubgroup V g := conjSubgroup_mono h.le g hy.1
    have hzV0 : ⁅y, v⁆ ∈ V₀ := by
      have hyc : y ∈ F11.CTilde M V₀ V := Y_le_cTilde h hy
      exact (FourteenTwo.mem_cTilde_iff_comm.1 hyc).2.2 v hv
    have hy2 : y * y = 1 := IsElemAbelian.mul_self_eq_one h.swap.elemAbelian hyVg
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hzEq : y * ⁅y, v⁆ = v * y * v⁻¹ := by
      rw [commutatorElement_def]
      calc y * (y * v * y⁻¹ * v⁻¹) = (y * y) * (v * y⁻¹ * v⁻¹) := by group
        _ = v * y⁻¹ * v⁻¹ := by rw [hy2, one_mul]
        _ = v * y * v⁻¹ := by rw [hyinv]
    have hyz2 : (y * ⁅y, v⁆) * (y * ⁅y, v⁆) = 1 := by
      rw [hzEq]
      calc (v * y * v⁻¹) * (v * y * v⁻¹) = v * (y * y) * v⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    have hz2 : ⁅y, v⁆ * ⁅y, v⁆ = 1 := h.elemAbelian.mul_self_eq_one (h.le hzV0)
    have h1 : (y * ⁅y, v⁆ * y) * ⁅y, v⁆ = ⁅y, v⁆ * ⁅y, v⁆ := by
      rw [mul_assoc, hyz2, hz2]
    have h2 : y * ⁅y, v⁆ * y = ⁅y, v⁆ := mul_right_cancel h1
    have hcomm : y * ⁅y, v⁆ = ⁅y, v⁆ * y := by
      calc y * ⁅y, v⁆ = (y * ⁅y, v⁆) * 1 := (mul_one _).symm
        _ = (y * ⁅y, v⁆) * (y * y) := by rw [hy2]
        _ = ((y * ⁅y, v⁆) * y) * y := by rw [← mul_assoc]
        _ = ⁅y, v⁆ * y := by rw [h2]
    have hzMg : ⁅y, v⁆ ∈ conjSubgroup M g := by
      have hcen : ⁅y, v⁆ ∈ centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hcomm
      exact centralizer_le_conjM h hy.1 hy1 hcen
    exact ⟨hzV0, hzMg⟩

theorem commutator_Z0_conjV_le_Y (h : Hyp65 n M V₀ V g) :
    ⁅Z0Of M V₀ g, conjSubgroup V g⁆ ≤ YOf M V₀ g := by
  have hh := commutator_Y_V_le_Z0 h.swap
  rw [YOf_swap, Z0Of_swap] at hh
  exact hh

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
