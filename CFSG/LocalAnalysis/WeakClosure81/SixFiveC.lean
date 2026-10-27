module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem Z0_Y_comm (h : Hyp65 n M V₀ V g) {z y : G} (hz : z ∈ Z0Of M V₀ g)
    (hy : y ∈ YOf M V₀ g) : z * y = y * z :=
  (Subgroup.mem_centralizer_iff.1 (Y_le_centralizer_U h hy)) z (Z0_le_U h hz)

theorem L0_coe_eq_mul (h : Hyp65 n M V₀ V g) :
    (L0Of M V₀ g : Set G) = (Z0Of M V₀ g : Set G) * (YOf M V₀ g : Set G) := by
  have hZ : Z0Of M V₀ g ≤ Subgroup.normalizer (YOf M V₀ g : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hy => (Z0_Y_comm h hz hy).symm
  rw [show L0Of M V₀ g = Z0Of M V₀ g ⊔ YOf M V₀ g from rfl]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZ

theorem L0_isElemAbelian (h : Hyp65 n M V₀ V g) : IsElemAbelian 2 (L0Of M V₀ g) := by
  have hZ : IsElemAbelian 2 (Z0Of M V₀ g) :=
    h.elemAbelian.mono (inf_le_left.trans h.le)
  have hY : IsElemAbelian 2 (YOf M V₀ g) :=
    h.swap.elemAbelian.mono (inf_le_left.trans (conjSubgroup_mono h.le g))
  rw [show L0Of M V₀ g = Z0Of M V₀ g ⊔ YOf M V₀ g from rfl]
  exact IsElemAbelian.sup_of_commute hZ hY fun a ha b hb => Z0_Y_comm h ha hb

theorem V_le_normalizer_L0 (h : Hyp65 n M V₀ V g) :
    V ≤ normalizer (L0Of M V₀ g : Set G) := by
  have hstep : ∀ v ∈ V, ∀ l ∈ L0Of M V₀ g, v * l * v⁻¹ ∈ L0Of M V₀ g := by
    intro v hv l hl
    have hl' : l ∈ (Z0Of M V₀ g : Set G) * (YOf M V₀ g : Set G) := by
      rw [← L0_coe_eq_mul h]
      exact hl
    rcases Set.mem_mul.1 hl' with ⟨z, hz, y, hy, hzy⟩
    have hzV : z ∈ V := (Subgroup.mem_inf.1 (Z0_le_U h hz)).1
    have hvz : v * z = z * v := h.elemAbelian.comm hv hzV
    have hcomm : ⁅v, y⁆ ∈ Z0Of M V₀ g := by
      have h1 : ⁅y, v⁆ ∈ ⁅YOf M V₀ g, V⁆ := Subgroup.commutator_mem_commutator hy hv
      have h2 : ⁅y, v⁆ ∈ Z0Of M V₀ g := commutator_Y_V_le_Z0 h h1
      have h3 : ⁅y, v⁆⁻¹ ∈ Z0Of M V₀ g := Subgroup.inv_mem _ h2
      rwa [commutatorElement_inv] at h3
    have hgoal : v * (z * y) * v⁻¹ = (z * ⁅v, y⁆) * y := by
      rw [commutatorElement_def]
      rw [show v * (z * y) = (v * z) * y by group, hvz]
      group
    rw [← hzy, hgoal]
    show (z * ⁅v, y⁆) * y ∈ Z0Of M V₀ g ⊔ YOf M V₀ g
    exact (Z0Of M V₀ g ⊔ YOf M V₀ g).mul_mem
      (Subgroup.mem_sup_left ((Z0Of M V₀ g).mul_mem hz hcomm)) (Subgroup.mem_sup_right hy)
  intro v hv
  refine Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hstep v hv l hl, fun hl => ?_⟩
  have h := hstep v⁻¹ (V.inv_mem hv) (v * l * v⁻¹) hl
  simpa [show v⁻¹ * (v * l * v⁻¹) * v = l by group] using h

theorem conjV_le_normalizer_L0 (h : Hyp65 n M V₀ V g) :
    conjSubgroup V g ≤ normalizer (L0Of M V₀ g : Set G) := by
  have := V_le_normalizer_L0 h.swap
  rwa [L0Of_swap] at this

theorem L_le_normalizer_L0 (h : Hyp65 n M V₀ V g) :
    LOf V g ≤ normalizer (L0Of M V₀ g : Set G) := by
  rw [show LOf V g = V ⊔ conjSubgroup V g from rfl]
  exact sup_le (V_le_normalizer_L0 h) (conjV_le_normalizer_L0 h)

theorem V_inf_centralizer_L0 (h : Hyp65 n M V₀ V g) :
    V ⊓ centralizer (L0Of M V₀ g : Set G) = UOf M V g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxcent⟩ := hx
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (Y_ne_bot h)
    have hyY : (a : G) ∈ YOf M V₀ g := a.2
    have hy1 : (a : G) ≠ 1 := fun hh => ha1 (Subtype.ext hh)
    have hxy : x ∈ centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hxcent (a : G) (Subgroup.mem_sup_right hyY)).symm
    exact ⟨hxV, centralizer_le_conjM h hyY.1 hy1 hxy⟩
  · refine le_inf inf_le_left ?_
    rw [Subgroup.le_centralizer_iff]
    show Z0Of M V₀ g ⊔ YOf M V₀ g ≤ centralizer (UOf M V g : Set G)
    refine sup_le ?_ (Y_le_centralizer_U h)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (h.elemAbelian.comm (Subgroup.mem_inf.1 (Z0_le_U h hz)).1
      (Subgroup.mem_inf.1 hu).1).symm

theorem L0_inf_centralizer_of_notMem_U (h : Hyp65 n M V₀ V g) {x : G} (hxV : x ∈ V)
    (hxU : x ∉ UOf M V g) :
    L0Of M V₀ g ⊓ centralizer ({x} : Set G) = Z0Of M V₀ g := by
  apply le_antisymm
  · intro l hl
    obtain ⟨hlL0, hlcent⟩ := hl
    have hl' : l ∈ (Z0Of M V₀ g : Set G) * (YOf M V₀ g : Set G) := by
      rw [← L0_coe_eq_mul h]
      exact hlL0
    rcases Set.mem_mul.1 hl' with ⟨z, hz, y, hy, hzy⟩
    have hzV : z ∈ V := (Subgroup.mem_inf.1 (Z0_le_U h hz)).1
    have hxl : x * l = l * x := (Subgroup.mem_centralizer_iff.1 hlcent) x (Set.mem_singleton x)
    have hxzi : x * z⁻¹ = z⁻¹ * x := h.elemAbelian.comm hxV (V.inv_mem hzV)
    by_cases hy1 : y = 1
    · rw [← hzy, hy1, mul_one]
      exact hz
    · exfalso
      apply hxU
      have hxy : x * y = y * x := by
        have h1 : y = z⁻¹ * l := by rw [← hzy]; group
        calc x * y = x * (z⁻¹ * l) := by rw [h1]
          _ = (x * z⁻¹) * l := by rw [mul_assoc]
          _ = (z⁻¹ * x) * l := by rw [hxzi]
          _ = z⁻¹ * (x * l) := by rw [mul_assoc]
          _ = z⁻¹ * (l * x) := by rw [hxl]
          _ = (z⁻¹ * l) * x := by rw [mul_assoc]
          _ = y * x := by rw [h1]
      have hxcent_y : x ∈ centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hxy
      exact ⟨hxV, centralizer_le_conjM h hy.1 hy1 hxcent_y⟩
  · intro z hz
    refine ⟨Subgroup.mem_sup_left hz, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (h.elemAbelian.comm hxV (Subgroup.mem_inf.1 (Z0_le_U h hz)).1).symm

theorem L0_inf_centralizer_of_notMem_B (h : Hyp65 n M V₀ V g) {x : G}
    (hxV : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    L0Of M V₀ g ⊓ centralizer ({x} : Set G) = YOf M V₀ g := by
  have hxU : x ∉ UOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
    rwa [UOf_swap]
  have := L0_inf_centralizer_of_notMem_U h.swap hxV hxU
  rwa [L0Of_swap, Z0Of_swap] at this

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
