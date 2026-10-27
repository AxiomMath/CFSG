module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TrackOf

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def IsReflection (ℓ : Line Γ) (k : ℤ) (f : G) : Prop :=
  f * f = 1 ∧ ∀ i : ℤ, f • ℓ.vert (k + i) = ℓ.vert (k - i)

@[expose] def IsLenTwoReflection (ℓ : Line Γ) (k : ℤ) (f : G) : Prop :=
  f * f = 1 ∧ f • ℓ.vert k = ℓ.vert k ∧ f • ℓ.vert (k + 1) = ℓ.vert (k - 1) ∧
    f • ℓ.vert (k + 2) = ℓ.vert (k - 2)

theorem IsReflection.fixes {ℓ : Line Γ} {k : ℤ} {f : G} (h : IsReflection ℓ k f) :
    f • ℓ.vert k = ℓ.vert k := by
  simpa using h.2 0

theorem Track.zpow_smul_vert (T : Track Γ G) (m j : ℤ) :
    T.τ ^ m • T.line.vert j = T.line.vert (j + 2 * m) := by
  induction m using Int.induction_on generalizing j with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one, mul_smul, T.trans, ih]
    congr 1
    omega
  | pred m ih =>
    have hinv : T.τ⁻¹ • T.line.vert j = T.line.vert (j - 2) := by
      rw [inv_smul_eq_iff]
      have := T.trans (j - 2)
      rw [show j - 2 + 2 = j by omega] at this
      exact this.symm
    rw [zpow_sub_one, mul_smul, hinv, ih]
    congr 1
    omega

theorem Track.reflect_of_inv (T : Track Γ G) {f : G} {c a : ℤ} (hf : f * T.τ * f⁻¹ = T.τ⁻¹)
    (h0 : f • T.line.vert a = T.line.vert (c - a))
    (h1 : f • T.line.vert (a + 1) = T.line.vert (c - (a + 1))) (i : ℤ) :
    f • T.line.vert i = T.line.vert (c - i) := by
  have hfτ : ∀ n : ℤ, f * T.τ ^ n = T.τ ^ (-n) * f := fun n => by
    have h := conj_zpow (a := f) (b := T.τ) (i := n)
    rw [hf, inv_zpow'] at h
    rw [h, inv_mul_cancel_right]
  have key : ∀ n j : ℤ, f • T.line.vert j = T.line.vert (c - j) →
      f • T.line.vert (j + 2 * n) = T.line.vert (c - (j + 2 * n)) := by
    intro n j hj
    rw [← T.zpow_smul_vert n j, ← mul_smul, hfτ n, mul_smul, hj, T.zpow_smul_vert]
    congr 1
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℤ, i = a + 2 * n ∨ i = a + 1 + 2 * n := ⟨(i - a) / 2, by omega⟩
  rcases hn with rfl | rfl
  · exact key n a h0
  · exact key n (a + 1) h1

theorem Track.isReflection_of_inv (T : Track Γ G) {f : G} {k : ℤ} (hf2 : f * f = 1)
    (hf : f * T.τ * f⁻¹ = T.τ⁻¹) (h0 : f • T.line.vert k = T.line.vert k)
    (h1 : f • T.line.vert (k + 1) = T.line.vert (k - 1)) : IsReflection T.line k f :=
  ⟨hf2, fun i => by
    have := T.reflect_of_inv (c := 2 * k) (a := k) hf (by rwa [show 2 * k - k = k by omega])
      (by rwa [show 2 * k - (k + 1) = k - 1 by omega]) (k + i)
    rwa [show 2 * k - (k + i) = k - i by omega] at this⟩

section Pair

variable (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) {α β : V} {x y : G}
  (hαβ : Γ.Adj α β) (h : CrossPair α β x y)

theorem trackOfPair_vert_three :
    (trackOfPair hadj hαβ h).line.vert 3 = y • α := by
  have := (trackOfPair hadj hαβ h).trans 1
  rw [trackOfPair_vert_one hadj hαβ h, trackOfPair_τ, mul_smul, h.x_fix] at this
  exact this.symm

theorem trackOfPair_inv_x (hx : x * x = 1) (hy : y * y = 1) :
    x * (trackOfPair hadj hαβ h).τ * x⁻¹ = (trackOfPair hadj hαβ h).τ⁻¹ := by
  rw [trackOfPair_τ, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  simp only [mul_assoc, hx, mul_one]

theorem trackOfPair_inv_y (hx : x * x = 1) (hy : y * y = 1) :
    y * (trackOfPair hadj hαβ h).τ * y⁻¹ = (trackOfPair hadj hαβ h).τ⁻¹ := by
  rw [trackOfPair_τ, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
    ← mul_assoc y y x, hy, one_mul]

theorem trackOfPair_smul_two_x (hx : x * x = 1) :
    x • (trackOfPair hadj hαβ h).line.vert 2 = (trackOfPair hadj hαβ h).line.vert 0 := by
  rw [trackOfPair_vert_two hadj hαβ h, trackOfPair_vert_zero hadj hαβ h,
    inv_eq_of_mul_eq_one_right hx]

theorem trackOfPair_reflection_x (hx : x * x = 1) (hy : y * y = 1) :
    IsReflection (trackOfPair hadj hαβ h).line 1 x := by
  refine (trackOfPair hadj hαβ h).isReflection_of_inv hx (trackOfPair_inv_x hadj hαβ h hx hy) ?_ ?_
  · rw [trackOfPair_vert_one hadj hαβ h]
    exact h.x_fix
  · rw [show (1 : ℤ) + 1 = 2 by omega, show (1 : ℤ) - 1 = 0 by omega]
    exact trackOfPair_smul_two_x hadj hαβ h hx

theorem trackOfPair_reflection_y (hx : x * x = 1) (hy : y * y = 1) :
    IsReflection (trackOfPair hadj hαβ h).line 2 y := by
  refine (trackOfPair hadj hαβ h).isReflection_of_inv hy (trackOfPair_inv_y hadj hαβ h hx hy) ?_ ?_
  · rw [trackOfPair_vert_two hadj hαβ h]
    exact h.y_fix
  · rw [show (2 : ℤ) + 1 = 3 by omega, show (2 : ℤ) - 1 = 1 by omega,
      trackOfPair_vert_three hadj hαβ h, trackOfPair_vert_one hadj hαβ h, ← mul_smul, hy, one_smul]

theorem trackOfPair_lenTwo (hx : x * x = 1) (hy2 : (y * y) • α = α) :
    IsLenTwoReflection (trackOfPair hadj hαβ h).line 1 x := by
  refine ⟨hx, ?_, ?_, ?_⟩
  · rw [trackOfPair_vert_one hadj hαβ h]
    exact h.x_fix
  · rw [show (1 : ℤ) + 1 = 2 by omega, show (1 : ℤ) - 1 = 0 by omega]
    exact trackOfPair_smul_two_x hadj hαβ h hx
  · have hneg : (trackOfPair hadj hαβ h).line.vert (-1) = (x * y⁻¹) • α := by
      have := (trackOfPair hadj hαβ h).trans (-1)
      rw [show (-1 : ℤ) + 2 = 1 by omega, trackOfPair_vert_one hadj hαβ h] at this
      rw [eq_inv_smul_iff.2 this, trackOfPair_τ, mul_inv_rev, inv_eq_of_mul_eq_one_right hx]
    rw [show (1 : ℤ) + 2 = 3 by omega, show (1 : ℤ) - 2 = -1 by omega, hneg,
      trackOfPair_vert_three hadj hαβ h, mul_smul]
    congr 1
    rw [eq_comm, inv_smul_eq_iff, ← mul_smul, hy2]

end Pair

end CFSG.Quasithin.Fan86
