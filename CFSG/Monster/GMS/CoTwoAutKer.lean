module

public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Monster.GMS.CoTwoModule
public import CFSG.Monster.GMS.LeechCohTwo

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act

namespace CoTwoAutKer

theorem co1Act_perp
    {v : Fin 24 → ZMod 2} {g : Co1} (hg : g ∈ co1Stab v)
    {w : Fin 24 → ZMod 2} (hw : bil₀ w v = 0) : bil₀ (co1Act g w) v = 0 := by
  have h := Leech.bil₀_co1Act g w v
  rw [show co1Act g v = v from hg] at h
  rw [h, hw]

theorem add01 {v a b : Fin 24 → ZMod 2} (ha : a = 0 ∨ a = v) (hb : b = 0 ∨ b = v) :
    a + b = 0 ∨ a + b = v := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left; rw [add_zero]
  · right; rw [zero_add]
  · right; rw [add_zero]
  · left; rw [vec_add_self]

theorem smul01 {v : Fin 24 → ZMod 2} {g : Co1} (hg : g ∈ co1Stab v) {a : Fin 24 → ZMod 2}
    (ha : a = 0 ∨ a = v) : co1Act g a = 0 ∨ co1Act g a = v := by
  rcases ha with rfl | rfl
  · left; exact map_zero _
  · right; exact hg

@[expose] def kerTriv
    (v : Fin 24 → ZMod 2) : Subgroup Co1 where
  carrier := {h | h ∈ co1Stab v ∧ ∀ w, bil₀ w v = 0 → co1Act h w + w = 0 ∨ co1Act h w + w = v}
  mul_mem' := by
    rintro g h ⟨hg, hgw⟩ ⟨hh, hhw⟩
    refine ⟨mul_mem hg hh, fun w hw => ?_⟩
    have e : co1Act (g * h) w + w = co1Act g (co1Act h w + w) + (co1Act g w + w) := by
      rw [CoTwoModule.co1Act_mul_apply, map_add, add_assoc, ← add_assoc (co1Act g w) (co1Act g w),
        vec_add_self, zero_add]
    rw [e]
    exact add01 (smul01 hg (hhw w hw)) (hgw w hw)
  one_mem' := by
    refine ⟨one_mem _, fun w _ => Or.inl ?_⟩
    rw [map_one, Module.End.one_apply]
    exact vec_add_self w
  inv_mem' := by
    rintro h ⟨hh, hhw⟩
    refine ⟨inv_mem hh, fun w hw => ?_⟩
    have hw' : bil₀ (co1Act h⁻¹ w) v = 0 := co1Act_perp (inv_mem hh) hw
    have := hhw _ hw'
    rw [CoTwoModule.co1Act_apply_inv, add_comm] at this
    exact this

theorem kerTriv_normal
    (v : Fin 24 → ZMod 2) :
    ∀ k ∈ co1Stab v, ∀ n ∈ kerTriv v, k * n * k⁻¹ ∈ kerTriv v := by
  rintro k hk n ⟨hn, hnw⟩
  refine ⟨mul_mem (mul_mem hk hn) (inv_mem hk), fun w hw => ?_⟩
  have hw' : bil₀ (co1Act k⁻¹ w) v = 0 := co1Act_perp (inv_mem hk) hw
  have h := smul01 hk (hnw _ hw')
  rw [map_add, CoTwoModule.co1Act_apply_inv] at h
  rw [CoTwoModule.co1Act_mul_apply, CoTwoModule.co1Act_mul_apply]
  exact h

theorem pow_four_eq_one
    {v : Fin 24 → ZMod 2} {n : Co1} (hn : n ∈ kerTriv v) : n ^ 4 = 1 := by
  obtain ⟨hn1, hn2⟩ := hn
  have hA : co1Act n v = v := hn1
  set d : (Fin 24 → ZMod 2) → (Fin 24 → ZMod 2) := fun x => co1Act n x + x with hd
  have hdadd : ∀ a b, d (a + b) = d a + d b := fun a b => by
    show co1Act n (a + b) + (a + b) = (co1Act n a + a) + (co1Act n b + b)
    rw [map_add, add_add_add_comm]
  have hdperp : ∀ x, bil₀ (d x) v = 0 := fun x => by
    show bil₀ (co1Act n x + x) v = 0
    rw [Leech.bil₀_add_left]
    have := Leech.bil₀_co1Act n x v
    rw [hA] at this
    rw [this]
    exact CharTwo.add_self_eq_zero _
  have hdv : d v = 0 := by
    show co1Act n v + v = 0
    rw [hA]
    exact vec_add_self v
  have hd0 : d 0 = 0 := by
    show co1Act n 0 + 0 = 0
    rw [map_zero, add_zero]
  have hdd : ∀ x, d (d x) = 0 ∨ d (d x) = v := fun x => hn2 _ (hdperp x)
  have hddd : ∀ x, d (d (d x)) = 0 := fun x => by
    rcases hdd x with h | h
    · rw [h, hd0]
    · rw [h, hdv]
  have hAx : ∀ x, co1Act n x = x + d x := fun x => by
    show _ = x + (co1Act n x + x)
    rw [add_comm (co1Act n x) x, ← add_assoc, vec_add_self, zero_add]
  have hn2x : ∀ x, co1Act (n * n) x = x + d (d x) := fun x => by
    have h1 := hAx x
    have h2 := hAx (d x)
    rw [CoTwoModule.co1Act_mul_apply]
    calc co1Act n (co1Act n x) = co1Act n (x + d x) := by rw [← h1]
      _ = co1Act n x + co1Act n (d x) := map_add _ _ _
      _ = (x + d x) + (d x + d (d x)) := by rw [← h1, ← h2]
      _ = x + d (d x) := by rw [add_assoc x (d x), ← add_assoc (d x) (d x), vec_add_self, zero_add]
  have hn4 : ∀ x, co1Act (n ^ 4) x = x := fun x => by
    have e : n ^ 4 = (n * n) * (n * n) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [e, CoTwoModule.co1Act_mul_apply, hn2x, hn2x, hdadd x (d (d x)),
      hdadd (d x) (d (d (d x))), hddd (d x), add_zero, add_assoc, vec_add_self, add_zero]
  exact LeechCoh.co1_eq_one_of_forall_act _ hn4

theorem isPGroup_kerTriv
    (v : Fin 24 → ZMod 2) : IsPGroup 2 (kerTriv v) := fun g => ⟨2, by
  have h : (g : Co1) ^ 4 = 1 := pow_four_eq_one g.2
  exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h)⟩

theorem kerTriv_eq_bot
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 0) : kerTriv v = ⊥ :=
  co2StabFacts v hv (co1Stab v) le_rfl (by omega) (kerTriv v) (fun _ hh => hh.1)
    (kerTriv_normal v) (isPGroup_kerTriv v)

theorem eq_one_of_trivial_on_perp
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 0) {g : Co1}
    (hg : g ∈ co1Stab v)
    (h : ∀ w, bil₀ w v = 0 → co1Act g w + w = 0 ∨ co1Act g w + w = v) : g = 1 := by
  have : g ∈ kerTriv v := ⟨hg, h⟩
  rw [kerTriv_eq_bot hv] at this
  exact Subgroup.mem_bot.1 this

end CoTwoAutKer

end CFSG.Monster.GMS
