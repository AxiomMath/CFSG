module

public import CFSG.LocalAnalysis.WeakClosure81.W183L39Fix
import CFSG.LocalAnalysis.WeakClosure81.W183Abs1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183L39

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {Y T L₁ L₂ : Subgroup (LGL 2 V)} {a : LGL 2 V}
variable {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem false_of_zeta_normalizes (c : SwapCfg Y T L₁ L₂ a) {D : Subgroup (LGL 2 V)}
    (hD : IsElemAbelian 2 D) (hDY : D ≤ Y) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁)
    (hN : ∀ l ∈ L₁, zeta a l ∈ Subgroup.normalizer (D : Set (LGL 2 V))) : False := by
  have hba : b * a = a * b := IsElemAbelian.comm hD hbD haD
  let N : Subgroup ↥L₁ :=
    { carrier := {l | zeta a (l : LGL 2 V) ∈ D}
      one_mem' := by
        change zeta a (1 : LGL 2 V) ∈ D
        rw [zeta_one]
        exact D.one_mem
      mul_mem' := by
        intro l l' hl hl'
        change zeta a ((l : LGL 2 V) * (l' : LGL 2 V)) ∈ D
        rw [zeta_mul c l.2 l'.2]
        exact D.mul_mem hl hl'
      inv_mem' := by
        intro l hl
        change zeta a ((l : LGL 2 V))⁻¹ ∈ D
        rw [zeta_inv c l.2]
        exact D.inv_mem hl }
  haveI hNnormal : N.Normal :=
    ⟨fun n hn g => by
      change zeta a ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) ∈ D
      rw [show zeta a ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹)
          = zeta a (g : LGL 2 V) * zeta a (n : LGL 2 V) * (zeta a (g : LGL 2 V))⁻¹ by
        rw [zeta_mul c (L₁.mul_mem g.2 n.2) (L₁.inv_mem g.2), zeta_mul c g.2 n.2,
          zeta_inv c g.2]]
      exact ((Subgroup.mem_set_normalizer_iff.mp (hN g g.2)
        (zeta a (n : LGL 2 V))).mp hn)⟩
  haveI := c.two.simple₁
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hcomm_l : ∀ l ∈ L₁, b * l = l * b := by
      intro l hl
      have hbl1L : b * l⁻¹ * b⁻¹ ∈ L₁ := by
        have hmem : b * l⁻¹ * b⁻¹ ∈ cj b L₁ := by
          rw [show b * l⁻¹ * b⁻¹ = (MulAut.conj b) l⁻¹ by simp [MulAut.conj_apply]]
          exact Subgroup.mem_map.mpr ⟨l⁻¹, L₁.inv_mem hl, rfl⟩
        rwa [hbL] at hmem
      have hz : zeta a (l * (b * l⁻¹ * b⁻¹)) ∈ D := by
        rw [zeta_mul c hl hbl1L]
        rw [show zeta a (b * l⁻¹ * b⁻¹) = b * (zeta a l)⁻¹ * b⁻¹ by
          rw [← zeta_conj (b := b) hba (l⁻¹), zeta_inv c hl]]
        have hzn : zeta a l ∈ Subgroup.normalizer (D : Set (LGL 2 V)) := hN l hl
        have hconj : zeta a l * b * (zeta a l)⁻¹ ∈ D :=
          ((Subgroup.mem_set_normalizer_iff.mp hzn) b).mp hbD
        have heq : zeta a l * (b * (zeta a l)⁻¹ * b⁻¹)
            = (zeta a l * b * (zeta a l)⁻¹) * b⁻¹ := by group
        rw [heq]
        exact D.mul_mem hconj (D.inv_mem hbD)
      have hmN : (⟨l * (b * l⁻¹ * b⁻¹), L₁.mul_mem hl hbl1L⟩ : ↥L₁) ∈ N := hz
      have hm1 : l * (b * l⁻¹ * b⁻¹) = 1 := by
        have hmem : (⟨l * (b * l⁻¹ * b⁻¹), L₁.mul_mem hl hbl1L⟩ : ↥L₁) ∈
            (⊥ : Subgroup ↥L₁) := by rw [← hbot]; exact hmN
        rw [Subgroup.mem_bot] at hmem
        simpa using congrArg Subtype.val hmem
      have hx : b * l⁻¹ * b⁻¹ = l⁻¹ := by
        calc b * l⁻¹ * b⁻¹ = l⁻¹ * (l * (b * l⁻¹ * b⁻¹)) := by group
          _ = l⁻¹ * 1 := by rw [hm1]
          _ = l⁻¹ := by group
      have hbl : b * l * b⁻¹ = l := by
        have := congrArg Inv.inv hx
        simpa [mul_inv_rev, mul_assoc] using this
      exact mul_inv_eq_iff_eq_mul.mp hbl
    refine hb1 (eq_one_of_comm_zeta c (hDY hbD) hba hbL ?_)
    intro l hl
    have hbl : b * l * b⁻¹ = l := mul_inv_eq_iff_eq_mul.mpr (hcomm_l l hl)
    have hconj := zeta_conj (b := b) hba l
    rw [hbl] at hconj
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · have hcommall : ∀ x ∈ L₁, ∀ y ∈ L₁, x * y = y * x := by
      intro x hx y hy
      have hxN : (⟨x, hx⟩ : ↥L₁) ∈ N := by rw [htop]; trivial
      have hyN : (⟨y, hy⟩ : ↥L₁) ∈ N := by rw [htop]; trivial
      have hzx : zeta a x ∈ D := hxN
      have hzy : zeta a y ∈ D := hyN
      apply zeta_injective c (L₁.mul_mem hx hy) (L₁.mul_mem hy hx)
      rw [zeta_mul c hx hy, zeta_mul c hy hx]
      exact IsElemAbelian.comm hD hzx hzy
    obtain ⟨p, hp, q, hq, hpq⟩ := c.two.nonab₁
    exact hpq (hcommall p hp q hq)

theorem false_of_fixed_vector (h : Assumption131 Y Γ VA i) (c : SwapCfg Y T L₁ L₂ a)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) {J : V} (hJ : J ∈ VA D) (hJ0 : J ≠ 0)
    (hfix : ∀ l ∈ L₁, zeta a l J = J) : False := by
  exact false_of_zeta_normalizes c (h.isElemAb D hD) (h.le_G D hD) haD hbD hb1 hbL
    fun l hl => h.stabilizer_le_normalizer hD hJ hJ0 (zeta_mem_Y c hl) (hfix l hl)

theorem false_of_good (h : Assumption131 Y Γ VA i) (c : SwapCfg Y T L₁ L₂ a)
    {D : Subgroup (LGL 2 V)} (hD : D ∈ Γ) (haD : a ∈ D) {b : LGL 2 V} (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbL : cj b L₁ = L₁) {B : Subgroup (LGL 2 V)} (hBD : B ≤ D)
    (hBi : mOf D B ≤ i) {v : V} (hvB : v ∈ fixSub B) (hav : a v ≠ v) : False := by
  have hba : b * a = a * b := IsElemAbelian.comm (h.isElemAb D hD) hbD haD
  have hJVA : a v - v ∈ VA D :=
    h.cond2 D hD B hBD hBi (sub_mem_commSpace (K := D) haD hvB)
  have hJ0 : a v - v ≠ 0 := sub_ne_zero.mpr hav
  let U : Set V := {u | ∃ w : V, u = a w - w}
  have hU : ∀ l ∈ L₁, ∀ u ∈ U, zeta a l u ∈ U := by
    intro l hl u hu
    obtain ⟨w, rfl⟩ := hu
    refine ⟨zeta a l w, ?_⟩
    have hcomm := congrArg (fun f : LGL 2 V => f w) (zeta_comm_a c hl)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hcomm
    simp only [map_sub, hcomm.symm]
  have hbU : ∀ u ∈ U, b u = u := by
    intro u hu
    obtain ⟨w, rfl⟩ := hu
    exact commSpace_eq_bot_iff.mp (h.quadratic D hD) b hbD (a w - w)
      (sub_mem_commSub D haD w)
  have hfixJ : ∀ l ∈ L₁, zeta a l (a v - v) = a v - v :=
    fun l hl => zeta_fixes_of_inner c (h.le_G D hD hbD) hba hb1 hbL U hU hbU l hl
      (a v - v) ⟨v, rfl⟩
  exact false_of_fixed_vector h c hD haD hbD hb1 hbL hJVA hJ0 hfixJ

end W183L39

end CFSG.LocalAnalysis.WeakClosure81

end
