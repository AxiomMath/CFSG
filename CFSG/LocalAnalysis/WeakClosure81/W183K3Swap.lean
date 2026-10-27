module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3Swap

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open Subgroup W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure SwapCfg (Y T L₁ L₂ : Subgroup (LGL 2 V)) (a : LGL 2 V) : Prop where
  two : Br3TwoComp Y T L₁ L₂
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

theorem SwapCfg.inf_le_centre (c : SwapCfg Y T L₁ L₂ a) : L₁ ⊓ L₂ ≤ quasiCentre L₁ := by
  intro l hl
  rw [Subgroup.mem_inf] at hl
  obtain ⟨hl₁, hl₂⟩ := hl
  rw [mem_quasiCentre]
  exact ⟨hl₁, fun l' hl' => (c.two.comm l' hl' l hl₂).symm⟩

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

theorem zeta_eq_iff (c : SwapCfg Y T L₁ L₂ a) {l l' : LGL 2 V} (hl : l ∈ L₁) (hl' : l' ∈ L₁)
    (h : zeta a l = zeta a l') : l'⁻¹ * l ∈ L₁ ⊓ L₂ := by
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
  exact Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩

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
    (hba : b * a = a * b) (hbb : b * b = 1) (hbL : cj b L₁ = L₁)
    (h : ∀ l ∈ L₁, b * zeta a l = zeta a l * b) : b = 1 := by
  have hmem₁L : ∀ l ∈ L₁, b * l * b⁻¹ ∈ L₁ := by
    intro l hl
    have hcj : b * l * b⁻¹ ∈ cj b L₁ := by
      rw [mem_cj]
      have : b⁻¹ * (b * l * b⁻¹) * b = l := by group
      rwa [this]
    rwa [hbL] at hcj
  have hmem₁ : ∀ l ∈ L₁, b * l * b⁻¹ * l⁻¹ ∈ quasiCentre L₁ := by
    intro l hl
    have hbl : b * l * b⁻¹ ∈ L₁ := hmem₁L l hl
    have e1 : b * zeta a l * b⁻¹ = zeta a l := by rw [h l hl]; group
    have e2 : b * zeta a l * b⁻¹ = zeta a (b * l * b⁻¹) := zeta_conj hba l
    have e3 : zeta a (b * l * b⁻¹) = zeta a l := by rw [← e2, e1]
    have hz : l⁻¹ * (b * l * b⁻¹) ∈ quasiCentre L₁ :=
      c.inf_le_centre (zeta_eq_iff c hbl hl e3)
    have hzl : (l⁻¹ * (b * l * b⁻¹)) * l = b * l * b⁻¹ := by
      rw [(mem_quasiCentre.mp hz).2 l hl]
      group
    have heq : b * l * b⁻¹ * l⁻¹ = l⁻¹ * (b * l * b⁻¹) := by
      calc b * l * b⁻¹ * l⁻¹
          = ((l⁻¹ * (b * l * b⁻¹)) * l) * l⁻¹ := by rw [hzl]
        _ = l⁻¹ * (b * l * b⁻¹) := by group
    rw [heq]
    exact hz
  have hcommL₁ : ∀ l ∈ L₁, b * l = l * b :=
    quasi_comm_of_comm_mod_centre c.two.quasi₁ hmem₁L hmem₁
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
  exact c.two.eq_one_of_isPGroup_cent hbY (k := 1) (by simpa [pow_two] using hbb)
    hcommL₁ hcommL₂

end W183K3Swap

end CFSG.LocalAnalysis.WeakClosure81

end
