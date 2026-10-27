module

public import CFSG.Timmesfeld.Bridge.RootStructQD
public import CFSG.Timmesfeld.Exceptional.Polar

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

namespace OrderThreeAux

private def dseq (σ d : G) (j : ℤ) : G := (σ ^ j)⁻¹ * d * σ ^ j

private theorem dseq_zero (σ d : G) : dseq σ d 0 = d := by simp [dseq]

private theorem zpow_conj_dseq (σ d : G) (k j : ℤ) :
    σ ^ k * dseq σ d j * (σ ^ k)⁻¹ = dseq σ d (j - k) := by
  simp only [dseq]
  group

private theorem dseq_dseq (σ d : G) (i j : ℤ) : dseq σ (dseq σ d i) j = dseq σ d (i + j) := by
  simp only [dseq]
  group

private theorem conj_dseq_of_conj_eq_inv {σ d g : G} (h : g * σ * g⁻¹ = σ⁻¹) (j : ℤ) :
    g * dseq σ d j * g⁻¹ = dseq σ (g * d * g⁻¹) (-j) := by
  have hj : σ ^ (-j) = g * σ ^ j * g⁻¹ := by rw [← conj_zpow, h, inv_zpow']
  simp only [dseq]
  rw [hj]
  group

private theorem commute_of_dseq_eq {σ d : G} {i j : ℤ} (h : dseq σ d i = dseq σ d j) :
    Commute (σ ^ (i - j)) d := by
  have h1 := congrArg (fun y => σ ^ j * y * (σ ^ j)⁻¹) h
  simp only [zpow_conj_dseq, sub_self, dseq_zero] at h1
  simp only [dseq] at h1
  calc σ ^ (i - j) * d = σ ^ (i - j) * ((σ ^ (i - j))⁻¹ * d * σ ^ (i - j)) := by rw [h1]
    _ = d * σ ^ (i - j) := by group

private theorem zpow_eq_one_of_commute [Finite G] {x u d : G} (hx2 : x * x = 1)
    (hu2 : u * u = 1) (hxQ : x ∈ Moufang.twoCore d) (hodd : Odd (orderOf (x * u))) {m : ℤ}
    (hm : Commute ((x * u) ^ m) d) : (x * u) ^ m = 1 := by
  set h := (x * u) ^ m with hh
  have hxh : x * h * x = h⁻¹ := by
    rw [hh, mul_zpow_mul_eq_zpow_neg_mul hx2 hu2 m, mul_assoc, hx2, mul_one, zpow_neg]
  have hmem : x * (h * x * h⁻¹) ∈ Moufang.twoCore d :=
    (Moufang.twoCore d).mul_mem hxQ (Moufang.conj_mem_twoCore hm hxQ)
  rw [show x * (h * x * h⁻¹) = (h ^ 2)⁻¹ by
    rw [← mul_assoc, ← mul_assoc, hxh, sq, mul_inv_rev]] at hmem
  have hoddh : Odd (orderOf h) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers _ m))
  have h21 : h ^ 2 = 1 := Special.eq_one_of_mem_of_isPGroup (Moufang.isPGroup_twoCore d)
    (by simpa using (Moufang.twoCore d).inv_mem hmem) (Odd.of_dvd_nat hoddh (orderOf_pow_dvd 2))
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h21) with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hoddh
    exact absurd hoddh (by decide)

private theorem conj_mem_of_mem_closure {S : Set G} {H : Subgroup G} {g w : G}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ H) (hw : w ∈ Subgroup.closure S) : g * w * g⁻¹ ∈ H := by
  induction hw using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul a b _ _ iha ihb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact H.mul_mem iha ihb
  | inv a _ iha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact H.inv_mem iha

private theorem eq_of_mem_closure_pair {a b w : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (hw : w ∈ Subgroup.closure ({a, b} : Set G)) :
    w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  have key : ∀ s ∈ ({a, b} : Set G), ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (s * y = 1 ∨ s * y = a ∨ s * y = b ∨ s * y = a * b) := by
    rintro s (rfl | rfl) y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hab.eq.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab.eq, mul_assoc, hb, mul_one]))
  induction hw using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left s hs y _ ih => exact key s hs y ih
  | inv_mul_cancel s hs y _ ih =>
    have hs' : s⁻¹ = s := by
      rcases hs with rfl | rfl
      · exact inv_eq_of_mul_eq_one_right ha
      · exact inv_eq_of_mul_eq_one_right hb
    rw [hs']
    exact key s hs y ih

private theorem mul_mem_of_conj {f u : G} {W : Subgroup G} {e : ℤ → G}
    (hf2 : f * f = 1) (hu2 : u * u = 1) (hfu : (f * u) ^ 3 = 1)
    (hfW : ∀ w ∈ W, f * w * f ∈ W) (huW : ∀ w ∈ W, u * w * u ∈ W)
    (hue : ∀ j, u * e j * u = e (1 - j)) (hfe : ∀ j, ∃ w ∈ W, f * e j * f = e j * w)
    (he2 : ∀ j, e j * e j = 1) (j : ℤ) : e j * e (1 - j) ∈ W := by
  have hff : ∀ y : G, f * (f * y) = y := fun y => by rw [← mul_assoc, hf2, one_mul]
  have huu : ∀ y : G, u * (u * y) = y := fun y => by rw [← mul_assoc, hu2, one_mul]
  have hF : ∀ i, ∀ w ∈ W, ∃ w' ∈ W, f * (e i * w) * f = e i * w' := by
    intro i w hw
    obtain ⟨w₁, hw₁, h₁⟩ := hfe i
    refine ⟨w₁ * (f * w * f), W.mul_mem hw₁ (hfW w hw), ?_⟩
    calc f * (e i * w) * f = f * e i * f * (f * w * f) := by simp only [mul_assoc, hff]
      _ = e i * (w₁ * (f * w * f)) := by rw [h₁, mul_assoc]
  have hU : ∀ i w, u * (e i * w) * u = e (1 - i) * (u * w * u) := by
    intro i w
    calc u * (e i * w) * u = u * e i * u * (u * w * u) := by simp only [mul_assoc, huu]
      _ = e (1 - i) * (u * w * u) := by rw [hue]
  have hu5 : f * u * f * u * f = u := by
    have h : f * u * f * u * f * u = 1 := by
      rw [← hfu, pow_three]
      simp only [mul_assoc]
    calc f * u * f * u * f = f * u * f * u * f * u * u := by simp only [mul_assoc, hu2, mul_one]
      _ = u := by rw [h, one_mul]
  obtain ⟨w₁, hw₁, h₁⟩ := hF j 1 W.one_mem
  have h₂ := hU j w₁
  obtain ⟨w₃, hw₃, h₃⟩ := hF (1 - j) (u * w₁ * u) (huW w₁ hw₁)
  have h₄ := hU (1 - j) w₃
  rw [sub_sub_cancel] at h₄
  obtain ⟨w₅, hw₅, h₅⟩ := hF j (u * w₃ * u) (huW w₃ hw₃)
  have key : e (1 - j) = e j * w₅ := by
    rw [← hue j, ← h₅, ← h₄, ← h₃, ← h₂, ← h₁, mul_one]
    conv_lhs => rw [← hu5]
    simp only [mul_assoc]
  rw [key, ← mul_assoc, he2, one_mul]
  exact hw₅

private theorem zpow_three_eq_one {σ u : G} {e : ℤ → G} (hu2 : u * u = 1)
    (he2 : ∀ j, e j * e j = 1) (hcomm : ∀ i j, Commute (e i) (e j))
    (hshift : ∀ k j, σ ^ k * e j * (σ ^ k)⁻¹ = e (j - k))
    (hue : ∀ j, u * e j * u = e (1 - j))
    (hW : e 2 * e (-1) ∈ Subgroup.closure ({e 0, e 1} : Set G))
    (hdist : ∀ i j, e i = e j → σ ^ (i - j) = 1) (hodd : Odd (orderOf σ)) (hσ1 : σ ≠ 1) :
    σ ^ 3 = 1 := by
  have huu : ∀ y : G, u * (u * y) = y := fun y => by rw [← mul_assoc, hu2, one_mul]
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h) with h1 | h1
    · exact hσ1 (orderOf_eq_one_iff.1 h1)
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  have hu_w : u * (e 2 * e (-1)) * u = e 2 * e (-1) := by
    have h1 := hue 2
    have h2 := hue (-1)
    rw [show (1 : ℤ) - 2 = -1 by norm_num] at h1
    rw [show (1 : ℤ) - -1 = 2 by norm_num] at h2
    calc u * (e 2 * e (-1)) * u = u * e 2 * u * (u * e (-1) * u) := by
          simp only [mul_assoc, huu]
      _ = e (-1) * e 2 := by rw [h1, h2]
      _ = e 2 * e (-1) := (hcomm _ _).eq
  have hu0 : u * e 0 * u = e 1 := by rw [hue, sub_zero]
  have hu1 : u * e 1 * u = e 0 := by rw [hue, sub_self]
  rcases eq_of_mem_closure_pair (he2 0) (he2 1) (hcomm 0 1) hW with h | h | h | h
  ·
    have h21 : e 2 = e (-1) := by
      calc e 2 = e 2 * e (-1) * e (-1) := by rw [mul_assoc, he2, mul_one]
        _ = e (-1) := by rw [h, one_mul]
    have := hdist 2 (-1) h21
    rw [show (2 : ℤ) - -1 = 3 by norm_num] at this
    exact_mod_cast this
  ·
    exfalso
    have h10 : e 1 = e 0 := by rw [← hu0, ← h, hu_w]
    have := hdist 1 0 h10
    rw [sub_zero, zpow_one] at this
    exact hσ1 this
  ·
    exfalso
    have h01 : e 1 = e 0 := by rw [← hu1, ← h, hu_w]
    have := hdist 1 0 h01
    rw [sub_zero, zpow_one] at this
    exact hσ1 this
  ·
    exfalso
    have hp1 : σ * (e 0 * e 1) * σ⁻¹ = e (-1) * e 0 := by
      have h0 := hshift 1 0
      have h1 := hshift 1 1
      rw [zpow_one, show (0 : ℤ) - 1 = -1 by norm_num] at h0
      rw [zpow_one, sub_self] at h1
      calc σ * (e 0 * e 1) * σ⁻¹ = σ * e 0 * σ⁻¹ * (σ * e 1 * σ⁻¹) := by group
        _ = e (-1) * e 0 := by rw [h0, h1]
    have hp2 : σ⁻¹ * (e 0 * e 1) * σ = e 1 * e 2 := by
      have h0 := hshift (-1) 0
      have h1 := hshift (-1) 1
      rw [zpow_neg_one, inv_inv, show (0 : ℤ) - -1 = 1 by norm_num] at h0
      rw [zpow_neg_one, inv_inv, show (1 : ℤ) - -1 = 2 by norm_num] at h1
      calc σ⁻¹ * (e 0 * e 1) * σ = σ⁻¹ * e 0 * σ * (σ⁻¹ * e 1 * σ) := by group
        _ = e 1 * e 2 := by rw [h0, h1]
    have hrel : e 1 * e 2 = e (-1) * e 0 := by
      calc e 1 * e 2 = e 1 * (e 2 * e (-1) * e (-1)) := by rw [mul_assoc (e 2), he2, mul_one]
        _ = e 1 * (e 0 * e 1 * e (-1)) := by rw [h]
        _ = e 1 * (e 1 * e 0 * e (-1)) := by rw [(hcomm 0 1).eq]
        _ = e 0 * e (-1) := by
          rw [mul_assoc (e 1) (e 0), ← mul_assoc (e 1) (e 1), he2, one_mul]
        _ = e (-1) * e 0 := (hcomm 0 (-1)).eq
    have hc2 : Commute (σ ^ 2) (e 0 * e 1) := by
      have heq : σ * (e 0 * e 1) * σ⁻¹ = σ⁻¹ * (e 0 * e 1) * σ := by rw [hp1, hp2, hrel]
      calc σ ^ 2 * (e 0 * e 1) = σ * (σ * (e 0 * e 1) * σ⁻¹) * σ := by rw [sq]; group
        _ = σ * (σ⁻¹ * (e 0 * e 1) * σ) * σ := by rw [heq]
        _ = e 0 * e 1 * σ ^ 2 := by rw [sq]; group
    have hc : Commute σ (e 0 * e 1) := by
      obtain ⟨k, hk⟩ := hodd
      have := hc2.pow_left (k + 1)
      rwa [← pow_mul, show 2 * (k + 1) = orderOf σ + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul] at this
    have h12 : e 1 * e 2 = e 1 * e 0 := by
      rw [← hp2, hc.inv_left.eq, inv_mul_cancel_right, (hcomm 0 1).eq]
    have := hdist 2 0 (mul_left_cancel h12)
    rw [sub_zero] at this
    exact hσ2 (by exact_mod_cast this)

end OrderThreeAux

open OrderThreeAux

variable {D : Set G}

theorem orderOf_mul_eq_three_of_translation [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {d f u x : G} (hd : d ∈ D) (hf : f ∈ D) (hu : u ∈ D) (hx : x ∈ D)
    (hfd : Commute f d)
    (hfS : ∀ s ∈ D, Commute s d → s * d ∈ D → f * s * f⁻¹ = s ∨ f * s * f⁻¹ = s * d)
    (hfu : (f * u) ^ 3 = 1) (hud : orderOf (u * d) = 4)
    (hfdu : f * (u * d * u) * f⁻¹ = u * d * u * d)
    (hxQ : x ∈ Moufang.twoCore d) (hxu : ¬ Commute x u) (hodd : Odd (orderOf (x * u))) :
    orderOf (x * u) = 3 := by
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  have hx2 := hD.mul_self_eq_one hx
  have hu2 := hD.mul_self_eq_one hu
  have hf2 := hD.mul_self_eq_one hf
  have hfi : f⁻¹ = f := hD.inv_eq hf
  have hui : u⁻¹ = u := hD.inv_eq hu
  have hxi : x⁻¹ = x := hD.inv_eq hx
  have hxd : Commute x d := Moufang.commute_of_mem_twoCore hxQ
  have hxdx : x * d * x = d := by rw [hxd.eq, mul_assoc, hx2, mul_one]
  have hσ1 : x * u ≠ 1 := by
    intro h
    apply hxu
    rw [eq_inv_of_mul_eq_one_left h, hui]
  have hgmem : ∀ j : ℤ, ((x * u) ^ j)⁻¹ ∈ Subgroup.closure ({x, u} : Set G) := fun j =>
    Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) j)
  have hconj : ∀ j, dseq (x * u) d j = ((x * u) ^ j)⁻¹ * d * (((x * u) ^ j)⁻¹)⁻¹ := fun j => by
    rw [inv_inv]
    rfl
  have he0 : dseq (x * u) d 0 = d := dseq_zero _ _
  have he1 : dseq (x * u) d 1 = u * d * u := by
    show ((x * u) ^ (1 : ℤ))⁻¹ * d * (x * u) ^ (1 : ℤ) = u * d * u
    rw [zpow_one, mul_inv_rev, hui, hxi]
    calc u * x * d * (x * u) = u * (x * d * x) * u := by simp only [mul_assoc]
      _ = u * d * u := by rw [hxdx]
  have heD : ∀ j, dseq (x * u) d j ∈ D := fun j => by
    rw [hconj]
    exact hN _ d hd
  have he2 : ∀ j, dseq (x * u) d j * dseq (x * u) d j = 1 := fun j =>
    hD.mul_self_eq_one (heD j)
  have hcomm : ∀ i j, Commute (dseq (x * u) d i) (dseq (x * u) d j) := fun i j => by
    rw [hconj i, hconj j]
    exact commute_conj_of_odd_special hD hN hx hu hd hxu hodd hud hxd (hgmem i) (hgmem j)
  have hed : ∀ j, Commute (dseq (x * u) d j) d := fun j => by
    have := hcomm j 0
    rwa [he0] at this
  have hmulD : ∀ j, dseq (x * u) d j ≠ d → dseq (x * u) d j * d ∈ D := fun j hne => by
    have := mul_conj_mem_of_odd_special hD hN hx hu hd hxu hodd hud hxd (hgmem j)
      (by rw [← hconj]; exact hne)
    rw [← hconj, ← (hed j).eq] at this
    exact this
  have hdist : ∀ i j, dseq (x * u) d i = dseq (x * u) d j → (x * u) ^ (i - j) = 1 :=
    fun i j h => zpow_eq_one_of_commute hx2 hu2 hxQ hodd (commute_of_dseq_eq h)
  have huσ : u * (x * u) * u⁻¹ = (x * u)⁻¹ := by
    rw [mul_inv_rev, hui, hxi, mul_assoc, mul_assoc, hu2, mul_one]
  have hue : ∀ j, u * dseq (x * u) d j * u = dseq (x * u) d (1 - j) := fun j => by
    have := conj_dseq_of_conj_eq_inv (d := d) huσ j
    rw [hui, ← he1, dseq_dseq, ← sub_eq_add_neg] at this
    exact this
  set W := Subgroup.closure ({dseq (x * u) d 0, dseq (x * u) d 1} : Set G)
  have h0W : dseq (x * u) d 0 ∈ W := Subgroup.subset_closure (by simp)
  have h1W : dseq (x * u) d 1 ∈ W := Subgroup.subset_closure (by simp)
  have hdW : d ∈ W := by
    rw [← he0]
    exact h0W
  have hfW : ∀ w ∈ W, f * w * f ∈ W := by
    intro w hw
    have := conj_mem_of_mem_closure (g := f) (H := W)
      (S := {dseq (x * u) d 0, dseq (x * u) d 1}) ?_ hw
    · rwa [hfi] at this
    · rintro s (rfl | rfl)
      · rw [he0, hfd.eq, mul_inv_cancel_right]
        exact hdW
      · rw [he1, hfdu, ← he1]
        exact W.mul_mem h1W hdW
  have huW : ∀ w ∈ W, u * w * u ∈ W := by
    intro w hw
    have := conj_mem_of_mem_closure (g := u) (H := W)
      (S := {dseq (x * u) d 0, dseq (x * u) d 1}) ?_ hw
    · rwa [hui] at this
    · rintro s (rfl | rfl)
      · rw [hui, hue, sub_zero]
        exact h1W
      · rw [hui, hue, sub_self]
        exact h0W
  have hfe : ∀ j, ∃ w ∈ W, f * dseq (x * u) d j * f = dseq (x * u) d j * w := by
    intro j
    by_cases hj : dseq (x * u) d j = d
    · refine ⟨1, W.one_mem, ?_⟩
      rw [hj, mul_one, hfd.eq, mul_assoc, hf2, mul_one]
    · rcases hfS _ (heD j) (hed j) (hmulD j hj) with h | h
      · rw [hfi] at h
        exact ⟨1, W.one_mem, by rw [h, mul_one]⟩
      · rw [hfi] at h
        exact ⟨d, hdW, h⟩
  have hW2 : dseq (x * u) d 2 * dseq (x * u) d (-1) ∈ W := by
    have := mul_mem_of_conj hf2 hu2 hfu hfW huW hue hfe he2 2
    rwa [show (1 : ℤ) - 2 = -1 by norm_num] at this
  have h3 : (x * u) ^ 3 = 1 :=
    zpow_three_eq_one hu2 he2 hcomm (zpow_conj_dseq _ _) hue hW2 hdist hodd hσ1
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hσ1
  · exact h

end CFSG.Timmesfeld.Bridge
