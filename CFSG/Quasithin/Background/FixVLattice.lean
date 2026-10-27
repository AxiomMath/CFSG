module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.Background.CommVBasics
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

namespace FixVLat

variable {V : Type*} [CommGroup V]

theorem mem_fixV_sup {A B : Subgroup (MulAut V)} {v : V} (hA : v ∈ fixV A) (hB : v ∈ fixV B) :
    v ∈ fixV (A ⊔ B) := by
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA x hx
    · exact hB x hx
  | one => rfl
  | mul x y _ _ hx hy => rw [MulAut.mul_apply, hy, hx]
  | inv x _ hx =>
    calc x⁻¹ v = x⁻¹ (x v) := by rw [hx]
      _ = v := by simp

theorem fixV_sup_eq (A B : Subgroup (MulAut V)) : fixV (A ⊔ B) = fixV A ⊓ fixV B :=
  le_antisymm (fun _ hv => ⟨fun x hx => hv x (le_sup_left (a := A) hx),
      fun x hx => hv x (le_sup_right (b := B) hx)⟩)
    fun _ hv => mem_fixV_sup hv.1 hv.2

theorem commV_le_iff {X : Subgroup (MulAut V)} {U : Subgroup V} :
    commV X ≤ U ↔ ∀ x ∈ X, ∀ v : V, x v * v⁻¹ ∈ U := by
  constructor
  · intro h x hx v
    exact h (Subgroup.subset_closure ⟨x, hx, v, rfl⟩)
  · intro h
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact h x hx v

theorem commV_closure_le {S : Set (MulAut V)} {W : Subgroup V}
    (h : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W) : commV (Subgroup.closure S) ≤ W := by
  rw [commV_le_iff]
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem s hs => exact fun v => h s hs v
  | one => intro v; simp
  | mul x y _ _ ihx ihy =>
    intro v
    have h1 := W.mul_mem (ihx (y v)) (ihy v)
    have h2 : x (y v) * (y v)⁻¹ * (y v * v⁻¹) = (x * y) v * v⁻¹ := by
      show x (y v) * (y v)⁻¹ * (y v * v⁻¹) = x (y v) * v⁻¹
      group
    rw [h2] at h1
    exact h1
  | inv x _ ihx =>
    intro v
    have h1 := W.inv_mem (ihx (x⁻¹ v))
    have h2 : (x (x⁻¹ v) * (x⁻¹ v)⁻¹)⁻¹ = x⁻¹ v * v⁻¹ := by
      rw [show x (x⁻¹ v) = v from by simp]
      group
    rw [h2] at h1
    exact h1

theorem commV_sup_le (A B : Subgroup (MulAut V)) : commV (A ⊔ B) ≤ commV A ⊔ commV B := by
  rw [Subgroup.sup_eq_closure]
  refine commV_closure_le fun s hs v => ?_
  rcases hs with hs | hs
  · exact le_sup_left (a := commV A) (Subgroup.subset_closure ⟨s, hs, v, rfl⟩)
  · exact le_sup_right (b := commV B) (Subgroup.subset_closure ⟨s, hs, v, rfl⟩)

theorem commV_bot : commV (⊥ : Subgroup (MulAut V)) = ⊥ := by
  rw [commV, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨x, hx, v, rfl⟩
  rw [Subgroup.mem_bot] at hx
  subst hx
  simp

theorem eq_bot_of_commV_eq_bot {X : Subgroup (MulAut V)} (h : commV X = ⊥) : X = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  ext v
  have h1 := commV_le_iff.1 h.le x hx v
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem index_fixV_zpowers_conj (g y : MulAut V) :
    (fixV (Subgroup.zpowers (g * y * g⁻¹))).index = (fixV (Subgroup.zpowers y)).index := by
  rw [fixV_zpowers_conj]
  exact Subgroup.index_map_equiv _ g

theorem le_stabSub_fixV_of_le_normalizer {X K : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) : X ≤ stabSub (fixV K) := by
  intro x hx v
  have hc : ∀ k ∈ K, x⁻¹ * k * x ∈ K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem hx)) k).mp hk
    simpa using this
  have hc' : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hXN hx) k).mp hk
  constructor
  · intro hv k hk
    have h1 := hv (x * k * x⁻¹) (hc' k hk)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
    exact x.injective h1
  · intro hv k hk
    have h1 := hv (x⁻¹ * k * x) (hc k hk)
    simp only [MulAut.mul_apply] at h1
    have := congrArg x h1
    simpa [MulAut.apply_inv_self] using this

theorem mem_stabSub_commV_of_mem_normalizer {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) : g ∈ stabSub (commV X) := by
  intro u
  constructor
  · intro hu
    have := commV_apply_mem_of_mem_normalizer (Subgroup.inv_mem _ hg) hu
    rwa [MulAut.inv_apply_self] at this
  · exact commV_apply_mem_of_mem_normalizer hg

end FixVLat

end CFSG.Quasithin
