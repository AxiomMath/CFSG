module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHModule
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH

open Equiv

variable {K S : Type} [Group K] [Group S]

@[expose] def cm (u v : S) : S := u * v * u⁻¹ * v⁻¹

theorem cm_inv_comm (u v : S) : cm u v = (cm v u)⁻¹ := by simp only [cm]; group

theorem map_cm (ρ : K →* MulAut S) (k : K) (u v : S) : ρ k (cm u v) = cm (ρ k u) (ρ k v) := by
  simp [cm]

section Central

variable (hcc : ∀ u v : S, cm u v ∈ Subgroup.center S)
include hcc

theorem cm_mul_left (u v w : S) : cm (u * v) w = cm u w * cm v w := by
  have ht : ∀ g : S, g * cm v w = cm v w * g := Subgroup.mem_center_iff.1 (hcc v w)
  calc cm (u * v) w = (u * cm v w * u⁻¹) * cm u w := by simp only [cm]; group
    _ = cm v w * cm u w := by rw [ht u]; simp
    _ = cm u w * cm v w := (Subgroup.mem_center_iff.1 (hcc v w) (cm u w)).symm

theorem cm_mul_right (u v w : S) : cm u (v * w) = cm u v * cm u w := by
  have h1 : cm u (v * w) = (cm v u * cm w u)⁻¹ := by
    rw [cm_inv_comm u (v * w), cm_mul_left hcc]
  rw [h1, mul_inv_rev, ← cm_inv_comm u v, ← cm_inv_comm u w]
  exact (Subgroup.mem_center_iff.1 (hcc u v) (cm u w))

end Central

section Fpf

variable [Finite S] {ρ : K →* MulAut S} (hρ : Fpf ρ) (hcc : ∀ u v : S, cm u v ∈ Subgroup.center S)
include hρ hcc

theorem cm_self_img {y : K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (u : S) : cm u (ρ y u) = 1 := by
  have h3 : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have habd := burnside_triple h3 (hρ y hy3 hy1) u
  have key : ∀ a b d : S, ρ y a = b → ρ y b = d → a * b * d = 1 → cm a b = 1 := by
    intro a b d hb hd habd
    have hdd : d = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habd
    have hda : d * a = b⁻¹ := by rw [hdd]; group
    have h1 : cm b (d * a) = 1 := by rw [hda]; simp [cm]
    rw [cm_mul_right hcc] at h1
    have h2 : cm b d = cm a b := by
      rw [eq_inv_of_mul_eq_one_left h1, cm_inv_comm b a, inv_inv]
    have h4 : ρ y (cm a b) = cm a b := by rw [map_cm, hb, hd, h2]
    exact hρ y hy3 hy1 _ h4
  exact key u (ρ y u) (ρ y (ρ y u)) rfl rfl habd

theorem cm_swap {y : K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (u v : S) :
    cm u (ρ y v) = cm (ρ y u) v := by
  have h := cm_self_img hρ hcc hy3 hy1 (u * v)
  rw [map_mul, cm_mul_left hcc, cm_mul_right hcc, cm_mul_right hcc, cm_self_img hρ hcc hy3 hy1 u,
    cm_self_img hρ hcc hy3 hy1 v, one_mul, mul_one] at h
  exact (eq_inv_of_mul_eq_one_left h).trans (cm_inv_comm _ _).symm

theorem cm_right {y : K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (u v : S) :
    cm u (ρ y v) = ρ y⁻¹ (cm u v) := by
  have hy3' : y⁻¹ ^ 3 = 1 := by rw [inv_pow, hy3, inv_one]
  have hy1' : y⁻¹ ≠ 1 := inv_ne_one.2 hy1
  have hyy : y⁻¹ * y⁻¹ = y := by
    calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * y ^ 3 := by rw [hy3, mul_one]
      _ = y := by group
  have h := cm_swap hρ hcc hy3' hy1' u (ρ y⁻¹ v)
  have e : ρ y⁻¹ (ρ y⁻¹ v) = ρ y v := by
    rw [← MulAut.mul_apply, ← map_mul, hyy]
  rw [e, ← map_cm] at h
  exact h

theorem cm_left {y : K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (u v : S) :
    cm (ρ y u) v = ρ y⁻¹ (cm u v) := by
  rw [← cm_swap hρ hcc hy3 hy1, cm_right hρ hcc hy3 hy1]

end Fpf

section Subgroups

variable {ρ : K →* MulAut S}

theorem pred_right {g : K} (hg : ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v)) (u v : S) :
    cm u (ρ g v) = ρ g⁻¹ (cm u v) := by
  rw [cm_inv_comm u (ρ g v), hg v u, ← map_inv, cm_inv_comm u v]

theorem pred_comm {g h : K} (hg : ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v))
    (hh : ∀ u v : S, cm (ρ h u) v = ρ h⁻¹ (cm u v)) (u v : S) :
    ρ g⁻¹ (ρ h⁻¹ (cm u v)) = ρ h⁻¹ (ρ g⁻¹ (cm u v)) := by
  have e1 : cm (ρ g u) (ρ h v) = ρ g⁻¹ (ρ h⁻¹ (cm u v)) := by rw [hg, pred_right hh]
  have e2 : cm (ρ h v) (ρ g u) = ρ h⁻¹ (ρ g⁻¹ (cm v u)) := by rw [hh, pred_right hg]
  rw [← e1, cm_inv_comm, e2, ← map_inv, ← map_inv, ← cm_inv_comm u v]

@[expose] def HH (ρ : K →* MulAut S) : Subgroup K where
  carrier := {g | ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v)}
  mul_mem' := by
    intro g h hg hh u v
    have hg' : ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v) := hg
    have hh' : ∀ u v : S, cm (ρ h u) v = ρ h⁻¹ (cm u v) := hh
    calc cm (ρ (g * h) u) v = cm (ρ g (ρ h u)) v := by rw [map_mul, MulAut.mul_apply]
      _ = ρ g⁻¹ (ρ h⁻¹ (cm u v)) := by rw [hg', hh']
      _ = ρ h⁻¹ (ρ g⁻¹ (cm u v)) := pred_comm hg' hh' u v
      _ = ρ (g * h)⁻¹ (cm u v) := by rw [mul_inv_rev, map_mul, MulAut.mul_apply]
  one_mem' := by intro u v; simp
  inv_mem' := by
    intro g hg u v
    have hg' : ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v) := hg
    have h1 := hg' (ρ g⁻¹ u) v
    have hk : ρ g (ρ g⁻¹ u) = u := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [hk] at h1
    have h2 := congrArg (ρ g) h1
    have hk2 : ρ g (ρ g⁻¹ (cm (ρ g⁻¹ u) v)) = cm (ρ g⁻¹ u) v := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [hk2] at h2
    rw [inv_inv]
    exact h2.symm

theorem HH_normal (ρ : K →* MulAut S) : (HH ρ).Normal := by
  refine ⟨fun n hn k => ?_⟩
  have hn' : ∀ u v : S, cm (ρ n u) v = ρ n⁻¹ (cm u v) := hn
  intro u v
  have hk : ∀ w : S, ρ k (ρ k⁻¹ w) = w := fun w => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h := congrArg (ρ k) (hn' (ρ k⁻¹ u) (ρ k⁻¹ v))
  rw [map_cm ρ k, ← map_cm ρ k⁻¹ u v] at h
  simp only [MulAut.mul_apply, hk] at h
  have e1 : ρ (k * n * k⁻¹) u = ρ k (ρ n (ρ k⁻¹ u)) := by
    simp [map_mul, MulAut.mul_apply]
  have e2 : (k * n * k⁻¹)⁻¹ = k * n⁻¹ * k⁻¹ := by group
  show cm (ρ (k * n * k⁻¹) u) v = ρ (k * n * k⁻¹)⁻¹ (cm u v)
  rw [e1, e2]
  simp only [map_mul, MulAut.mul_apply]
  exact h

@[expose] def PP (ρ : K →* MulAut S) : Subgroup K where
  carrier := {g | ∀ u v : S, ρ g (cm u v) = cm u v}
  mul_mem' := by
    intro g h hg hh u v
    have hg' : ∀ u v : S, ρ g (cm u v) = cm u v := hg
    have hh' : ∀ u v : S, ρ h (cm u v) = cm u v := hh
    rw [map_mul, MulAut.mul_apply, hh', hg']
  one_mem' := by intro u v; simp
  inv_mem' := by
    intro g hg u v
    have hg' : ∀ u v : S, ρ g (cm u v) = cm u v := hg
    have := congrArg (ρ g⁻¹) (hg' u v)
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
    exact this.symm

theorem PP_normal (ρ : K →* MulAut S) : (PP ρ).Normal := by
  refine ⟨fun n hn k => ?_⟩
  have hn' : ∀ u v : S, ρ n (cm u v) = cm u v := hn
  intro u v
  have hk : ∀ w : S, ρ k (ρ k⁻¹ w) = w := fun w => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  show ρ (k * n * k⁻¹) (cm u v) = cm u v
  have h := congrArg (ρ k) (hn' (ρ k⁻¹ u) (ρ k⁻¹ v))
  rw [← map_cm ρ k⁻¹ u v] at h
  simp only [MulAut.mul_apply, hk] at h
  simpa [map_mul, MulAut.mul_apply] using h

end Subgroups

theorem comm_of_class_two [Finite S] [IsSimpleGroup K] (e : K ≃* A5) {ρ : K →* MulAut S}
    (hρ : Fpf ρ) (hcc : ∀ u v : S, cm u v ∈ Subgroup.center S) (u v : S) : u * v = v * u := by
  suffices hc : cm u v = 1 by
    have h2 : u * v * u⁻¹ = v := mul_inv_eq_one.1 hc
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v * u := by rw [h2]
  let y0 : K := e.symm (mk5 c[0, 1, 2])
  have hy0_3 : y0 ^ 3 = 1 := by
    have : (mk5 c[0, 1, 2]) ^ 3 = 1 := by decide
    rw [← map_pow, this, map_one]
  have hy0_1 : y0 ≠ 1 := by
    intro h
    have : (mk5 c[0, 1, 2]) = 1 := by simpa [y0] using h
    revert this; decide
  have hHH : HH ρ = ⊤ := by
    haveI := HH_normal ρ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (HH ρ) with h | h
    · exfalso
      have : y0 ∈ HH ρ := fun u v => cm_left hρ hcc hy0_3 hy0_1 u v
      rw [h, Subgroup.mem_bot] at this
      exact hy0_1 this
    · exact h
  have hcube : ∀ g : K, ∀ u v : S, ρ (g ^ 3) (cm u v) = cm u v := by
    intro g u v
    have hg : ∀ u v : S, cm (ρ g u) v = ρ g⁻¹ (cm u v) := by
      have : g ∈ HH ρ := by rw [hHH]; exact Subgroup.mem_top g
      exact this
    have hX : ρ g (cm u v) = ρ g⁻¹ (ρ g⁻¹ (cm u v)) := by
      rw [map_cm, hg, pred_right hg]
    have e3 : g ^ 3 = (g * g) * g := pow_three' g
    rw [e3, map_mul, MulAut.mul_apply, hX]
    simp only [← MulAut.mul_apply, ← map_mul]
    have : g * g * g⁻¹ * g⁻¹ = 1 := by group
    simp [this]
  let g0 : K := e.symm z5
  have hg0 : g0 ^ 3 ≠ 1 := by
    intro h
    have : z5 ^ 3 = 1 := by
      have := congrArg e h
      simpa [g0, map_pow] using this
    revert this; decide
  have hPP : PP ρ = ⊤ := by
    haveI := PP_normal ρ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (PP ρ) with h | h
    · exfalso
      have : g0 ^ 3 ∈ PP ρ := fun u v => hcube g0 u v
      rw [h, Subgroup.mem_bot] at this
      exact hg0 this
    · exact h
  have hy : y0 ∈ PP ρ := by rw [hPP]; exact Subgroup.mem_top y0
  exact hρ y0 hy0_3 hy0_1 _ (hy u v)

end CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH
