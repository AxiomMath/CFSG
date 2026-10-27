module

public import CFSG.Quasithin.Vol2.Ch10SecKL7e
public import CFSG.Quasithin.Vol2.Ch10SecKL7g

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

theorem mQuot_congr {V X Y : Subgroup W} (hXY : X ⊓ V = Y ⊓ V) :
    E3.mQuot V X = E3.mQuot V Y := by
  rw [E3.mQuot, E3.mQuot, ← Subgroup.inf_relIndex_right, hXY, Subgroup.inf_relIndex_right]

theorem cdM_ge_two {γ : SL32} (hγ : γ ≠ 1) (hodd : Odd (orderOf γ)) : 2 ≤ cdM γ := by
  by_contra hlt
  rcases (show cdM γ = 0 ∨ cdM γ = 1 by omega) with h0 | h1
  · exact hγ (eq_one_of_cdM_eq_zero γ h0)
  · have h2 := orderOf_dvd_of_pow_eq_one (sq_eq_one_of_cdM_eq_one γ h1)
    have h3 : orderOf γ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact hγ (orderOf_eq_one_iff.1 h3)

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

theorem coe_π_symm {a : MulAut W} (ha : a ∈ L) :
    ((c.π (c.π.symm ⟨a, ha⟩) : ↥L) : MulAut W) = a := by
  rw [MulEquiv.apply_symm_apply]

theorem orderOf_π_symm {a : MulAut W} (ha : a ∈ L) :
    orderOf (c.π.symm ⟨a, ha⟩) = orderOf a := by
  rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]

include c in
theorem orderOf_dvd {a : MulAut W} (ha : a ∈ L) : orderOf a ∣ 168 := by
  have h1 := orderOf_dvd_natCard (⟨a, ha⟩ : ↥L)
  rw [← Nat.card_congr c.π.toEquiv, card_SL32] at h1
  have h2 : orderOf a = orderOf (⟨a, ha⟩ : ↥L) := Subgroup.orderOf_coe ⟨a, ha⟩
  rw [h2]
  exact h1

end Coord

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem finite_aut : Finite (MulAut W) := by
  have : Finite W := h.finite_W
  exact Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective

theorem rkIdx_L₀ (c₁ : Coord L₁ W₁) (c₂ : Coord L₂ W₂) (γ₁ γ₂ : SL32) :
    rkIdx (fixV (Subgroup.zpowers (((c₁.π γ₁ : ↥L₁) : MulAut W) *
      ((c₂.π γ₂ : ↥L₂) : MulAut W)))) =
      4 * cdM γ₁ + 4 * cdM γ₂ := by
  set a : MulAut W := ((c₁.π γ₁ : ↥L₁) : MulAut W) with ha_def
  set b : MulAut W := ((c₂.π γ₂ : ↥L₂) : MulAut W) with hb_def
  have ha : a ∈ L₁ := (c₁.π γ₁).2
  have hb : b ∈ L₂ := (c₂.π γ₂).2
  have h₁ : ∀ w ∈ W₁, (a * b) w ∈ W₁ := fun w hw => by
    rw [MulAut.mul_apply, h.fix₂ b hb w hw]
    exact c₁.map_mem ha hw
  have h₂ : ∀ w ∈ W₂, (a * b) w ∈ W₂ := fun w hw => by
    rw [MulAut.mul_apply, h.fix₁ a ha _ (c₂.map_mem hb hw)]
    exact c₂.map_mem hb hw
  rw [h.rkIdx_eq_add h₁ h₂]
  congr 1
  · rw [mQuot_congr (Y := fixV (Subgroup.zpowers a)), c₁.mQuot_fix]
    ext w
    simp only [Subgroup.mem_inf, mem_fixV_zp, MulAut.mul_apply]
    constructor
    · rintro ⟨hw1, hw2⟩
      exact ⟨by rwa [h.fix₂ b hb w hw2] at hw1, hw2⟩
    · rintro ⟨hw1, hw2⟩
      exact ⟨by rwa [h.fix₂ b hb w hw2], hw2⟩
  · rw [mQuot_congr (Y := fixV (Subgroup.zpowers b)), c₂.mQuot_fix]
    ext w
    simp only [Subgroup.mem_inf, mem_fixV_zp, MulAut.mul_apply]
    constructor
    · rintro ⟨hw1, hw2⟩
      exact ⟨by rwa [h.fix₁ a ha _ (c₂.map_mem hb hw2)] at hw1, hw2⟩
    · rintro ⟨hw1, hw2⟩
      exact ⟨by rw [hw1, h.fix₁ a ha w hw2], hw2⟩

theorem le_rkIdx_of_swap {x : MulAut W} (hx : x ∈ Mb)
    (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₂) : 12 ≤ rkIdx (fixV (Subgroup.zpowers x)) :=
  h.le_rkIdx_of_inf (eq_bot_iff.2 fun w hw => by
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    have h3 := h.map_mem_W₂_of_swap hx h1 hw2
    rw [mem_fixV_zp.1 hw1] at h3
    have : w ∈ W₁ ⊓ W₂ := ⟨hw2, h3⟩
    rwa [h.inf_W] at this)

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
