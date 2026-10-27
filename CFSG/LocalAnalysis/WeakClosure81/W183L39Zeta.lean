module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
import CFSG.LocalAnalysis.WeakClosure81.W183Abs3
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183L39

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure SwapCfg (Y T L₁ L₂ : Subgroup (LGL 2 V)) (a : LGL 2 V) : Prop where
  two : Br2TwoComp Y T L₁ L₂
  mem : a ∈ Y
  sq : a * a = 1
  swap : cj a L₁ = L₂

variable {Y T L₁ L₂ : Subgroup (LGL 2 V)} {a : LGL 2 V}

theorem SwapCfg.conj_mem₁ (c : SwapCfg Y T L₁ L₂ a) {l : LGL 2 V} (hl : l ∈ L₁) :
    a * l * a⁻¹ ∈ L₂ := by
  have h : a * l * a⁻¹ ∈ cj a L₁ := by
    rw [mem_cj]
    have : a⁻¹ * (a * l * a⁻¹) * a = l := by group
    rwa [this]
  rwa [c.swap] at h

theorem SwapCfg.inf_eq_bot (c : SwapCfg Y T L₁ L₂ a) : L₁ ⊓ L₂ = ⊥ := by
  haveI := c.two.simple₁
  exact w183_inf_eq_bot_of_commute c.two.nonab₁ c.two.comm

@[expose] def zeta (a l : LGL 2 V) : LGL 2 V := l * (a * l * a⁻¹)

theorem zeta_mul (c : SwapCfg Y T L₁ L₂ a) {l l' : LGL 2 V} (hl : l ∈ L₁) (hl' : l' ∈ L₁) :
    zeta a (l * l') = zeta a l * zeta a l' := by
  have hm : a * l * a⁻¹ ∈ L₂ := c.conj_mem₁ hl
  have hcomm : l' * (a * l * a⁻¹) = (a * l * a⁻¹) * l' := c.two.comm l' hl' _ hm
  unfold zeta
  rw [show a * (l * l') * a⁻¹ = (a * l * a⁻¹) * (a * l' * a⁻¹) by group]
  calc l * l' * ((a * l * a⁻¹) * (a * l' * a⁻¹))
      = l * (l' * (a * l * a⁻¹)) * (a * l' * a⁻¹) := by group
    _ = l * ((a * l * a⁻¹) * l') * (a * l' * a⁻¹) := by rw [hcomm]
    _ = l * (a * l * a⁻¹) * (l' * (a * l' * a⁻¹)) := by group

theorem zeta_mem_Y (c : SwapCfg Y T L₁ L₂ a) {l : LGL 2 V} (hl : l ∈ L₁) : zeta a l ∈ Y := by
  unfold zeta
  exact Y.mul_mem (c.two.le₁ hl)
    (Y.mul_mem (Y.mul_mem c.mem (c.two.le₁ hl)) (Y.inv_mem c.mem))

theorem zeta_comm_a (c : SwapCfg Y T L₁ L₂ a) {l : LGL 2 V} (hl : l ∈ L₁) :
    a * zeta a l = zeta a l * a := by
  unfold zeta
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right c.sq
  have ham : a * (a * l * a⁻¹) * a⁻¹ = l := by
    rw [ha, show a * (a * l * a) * a = (a * a) * l * (a * a) by group]
    simp [c.sq]
  have hcomm : l * (a * l * a⁻¹) = (a * l * a⁻¹) * l :=
    c.two.comm l hl _ (c.conj_mem₁ hl)
  have key : a * (l * (a * l * a⁻¹)) * a⁻¹ = l * (a * l * a⁻¹) := by
    calc a * (l * (a * l * a⁻¹)) * a⁻¹
        = (a * l * a⁻¹) * (a * (a * l * a⁻¹) * a⁻¹) := by group
      _ = (a * l * a⁻¹) * l := by rw [ham]
      _ = l * (a * l * a⁻¹) := hcomm.symm
  exact mul_inv_eq_iff_eq_mul.mp key

theorem zeta_injective (c : SwapCfg Y T L₁ L₂ a) {l l' : LGL 2 V} (hl : l ∈ L₁) (hl' : l' ∈ L₁)
    (h : zeta a l = zeta a l') : l = l' := by
  unfold zeta at h
  have hm : a * l * a⁻¹ ∈ L₂ := c.conj_mem₁ hl
  have hm' : a * l' * a⁻¹ ∈ L₂ := c.conj_mem₁ hl'
  have heq : l'⁻¹ * l = (a * l' * a⁻¹) * (a * l * a⁻¹)⁻¹ := by
    have hh := congrArg (fun x => l'⁻¹ * x * (a * l * a⁻¹)⁻¹) h
    simpa [mul_assoc] using hh
  have hmem1 : l'⁻¹ * l ∈ L₁ := L₁.mul_mem (L₁.inv_mem hl') hl
  have hmem2 : l'⁻¹ * l ∈ L₂ := by
    rw [heq]
    exact L₂.mul_mem hm' (L₂.inv_mem hm)
  have hbot : l'⁻¹ * l ∈ (⊥ : Subgroup (LGL 2 V)) := by
    rw [← c.inf_eq_bot]
    exact Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
  rw [Subgroup.mem_bot] at hbot
  exact (inv_mul_eq_one.mp hbot).symm

theorem zeta_one : zeta a (1 : LGL 2 V) = 1 := by
  simp [zeta]

theorem zeta_inv (c : SwapCfg Y T L₁ L₂ a) {l : LGL 2 V} (hl : l ∈ L₁) :
    zeta a l⁻¹ = (zeta a l)⁻¹ := by
  have hl1 : l⁻¹ ∈ L₁ := L₁.inv_mem hl
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← zeta_mul c hl1 hl, inv_mul_cancel, zeta_one]

theorem zeta_conj {b : LGL 2 V} (hba : b * a = a * b) (l : LGL 2 V) :
    b * zeta a l * b⁻¹ = zeta a (b * l * b⁻¹) := by
  have hc : Commute b a := hba
  have hb1 : b * a * b⁻¹ = a := by rw [hba]; group
  have hb2 : b * a⁻¹ * b⁻¹ = a⁻¹ := by rw [hc.inv_right.eq]; group
  unfold zeta
  calc b * (l * (a * l * a⁻¹)) * b⁻¹
      = (b * l * b⁻¹) * (b * (a * l * a⁻¹) * b⁻¹) := by group
    _ = (b * l * b⁻¹) * ((b * a * b⁻¹) * (b * l * b⁻¹) * (b * a⁻¹ * b⁻¹)) := by
      group
    _ = (b * l * b⁻¹) * (a * (b * l * b⁻¹) * a⁻¹) := by rw [hb1, hb2]

theorem eq_one_of_comm_zeta (c : SwapCfg Y T L₁ L₂ a) {b : LGL 2 V} (hbY : b ∈ Y)
    (hba : b * a = a * b) (hbL : cj b L₁ = L₁)
    (h : ∀ l ∈ L₁, b * zeta a l = zeta a l * b) : b = 1 := by
  have hmem₁ : ∀ l ∈ L₁, b * l * b⁻¹ ∈ L₁ := by
    intro l hl
    have hcj : b * l * b⁻¹ ∈ cj b L₁ := by
      rw [mem_cj]
      have : b⁻¹ * (b * l * b⁻¹) * b = l := by group
      rwa [this]
    rwa [hbL] at hcj
  have hcommL₁ : ∀ l ∈ L₁, b * l = l * b := by
    intro l hl
    have hbl : b * l * b⁻¹ ∈ L₁ := hmem₁ l hl
    have e1 : b * zeta a l * b⁻¹ = zeta a l := by rw [h l hl]; group
    have e2 : b * zeta a l * b⁻¹ = zeta a (b * l * b⁻¹) := zeta_conj hba l
    have e3 : zeta a (b * l * b⁻¹) = zeta a l := by rw [← e2, e1]
    have e4 : b * l * b⁻¹ = l := zeta_injective c hbl hl e3
    exact mul_inv_eq_iff_eq_mul.mp e4
  have hcommL₂ : ∀ l ∈ L₂, b * l = l * b := by
    intro l hl
    have hlcj : l ∈ cj a L₁ := c.swap.symm ▸ hl
    obtain ⟨l₀, hl₀, hl₀eq⟩ := Subgroup.mem_map.mp hlcj
    have hl₀' : l = a * l₀ * a⁻¹ := by simpa [MulAut.conj_apply] using hl₀eq.symm
    rw [hl₀']
    have hb : Commute b a := hba
    have hb0 : Commute b l₀ := hcommL₁ l₀ hl₀
    have hbx : Commute b (a * l₀) := hb.mul_right hb0
    exact (hbx.mul_right hb.inv_right).eq
  exact c.two.cent b hbY hcommL₁ hcommL₂

end W183L39

end CFSG.LocalAnalysis.WeakClosure81

end
