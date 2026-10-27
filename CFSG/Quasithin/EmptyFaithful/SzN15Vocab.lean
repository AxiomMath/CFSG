module

public import CFSG.Quasithin.Background.CommVBasics
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.SzN15

variable {V : Type} [CommGroup V]

@[expose] def fixMod (S : Subgroup (MulAut V)) (U Z : Subgroup V) : Subgroup V where
  carrier := {u | u ∈ U ∧ ∀ s ∈ S, s u * u⁻¹ ∈ Z}
  one_mem' := ⟨U.one_mem, fun s _ => by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨U.mul_mem hu hv, fun s hs => ?_⟩
    have h := Z.mul_mem (hu' s hs) (hv' s hs)
    have e : s (u * v) * (u * v)⁻¹ = (s u * u⁻¹) * (s v * v⁻¹) := by
      rw [map_mul, mul_inv_rev, mul_comm v⁻¹ u⁻¹, mul_mul_mul_comm]
    rw [e]; exact h
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨U.inv_mem hu, fun s hs => ?_⟩
    have h := Z.inv_mem (hu' s hs)
    have e : s u⁻¹ * (u⁻¹)⁻¹ = (s u * u⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
    rw [e]; exact h

theorem mem_fixMod {S : Subgroup (MulAut V)} {U Z : Subgroup V} {u : V} :
    u ∈ fixMod S U Z ↔ u ∈ U ∧ ∀ s ∈ S, s u * u⁻¹ ∈ Z := Iff.rfl

@[expose] def setStab (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ u, u ∈ W ↔ x u ∈ W}
  one_mem' := fun u => Iff.rfl
  mul_mem' := fun {x y} hx hy u => by
    rw [hy u, hx (y u)]; rfl
  inv_mem' := fun {x} hx u => by
    rw [hx (x⁻¹ u)]
    simp

theorem mem_setStab {W : Subgroup V} {x : MulAut V} : x ∈ setStab W ↔ ∀ u, u ∈ W ↔ x u ∈ W := Iff.rfl

theorem conj_mem_setStab {W : Subgroup V} {a x : MulAut V} (ha : ∀ u, u ∈ W ↔ a u ∈ W)
    (hx : x ∈ setStab W) : a * x * a⁻¹ ∈ setStab W := by
  intro u
  have h1 : a⁻¹ u ∈ W ↔ u ∈ W := by rw [ha (a⁻¹ u)]; simp
  show u ∈ W ↔ a (x (a⁻¹ u)) ∈ W
  rw [← ha (x (a⁻¹ u)), ← hx (a⁻¹ u), h1]

theorem fixMod_inv {S : Subgroup (MulAut V)} {U Z : Subgroup V} {a : MulAut V}
    (haS : a ∈ Subgroup.normalizer (S : Set (MulAut V))) (haU : ∀ u, u ∈ U ↔ a u ∈ U)
    (haZ : ∀ u, u ∈ Z ↔ a u ∈ Z) : ∀ u, u ∈ fixMod S U Z ↔ a u ∈ fixMod S U Z := by
  intro u
  rw [mem_fixMod, mem_fixMod, ← haU u]
  refine and_congr_right fun _ => ?_
  have hS : ∀ s : MulAut V, s ∈ S ↔ a⁻¹ * s * a ∈ S := by
    intro s
    have := Subgroup.mem_normalizer_iff.1 (inv_mem haS) s
    simpa using this
  constructor
  · intro h s hs
    have h' := h (a⁻¹ * s * a) ((hS s).1 hs)
    rw [haZ] at h'
    convert h' using 1
    simp [map_mul]
  · intro h s hs
    have h' := h (a * s * a⁻¹) (by
      have := Subgroup.mem_normalizer_iff.1 haS s
      exact this.1 hs)
    rw [haZ]
    convert h' using 1
    simp [map_mul]


theorem fixV_iff_apply {X : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (X : Set (MulAut V))) : ∀ u, u ∈ fixV X ↔ a u ∈ fixV X := by
  intro u
  rw [mem_fixV, mem_fixV]
  constructor
  · intro h x hx
    have hx' : a⁻¹ * x * a ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) x).1 hx
      simpa using this
    have h1 := h _ hx'
    calc x (a u) = a ((a⁻¹ * x * a) u) := by simp [MulAut.mul_apply]
      _ = a u := by rw [h1]
  · intro h x hx
    have hx' : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 ha x).1 hx
    have h1 := h _ hx'
    have h2 : a (x u) = a u := by simpa [MulAut.mul_apply] using h1
    exact a.injective h2

theorem commV_apply_mem_of_normalizer {X : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (X : Set (MulAut V))) {u : V} (hu : u ∈ commV X) :
    a u ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer ha hu

theorem commV_iff_apply {X : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ Subgroup.normalizer (X : Set (MulAut V))) : ∀ u, u ∈ commV X ↔ a u ∈ commV X :=
  fun u => ⟨commV_apply_mem_of_normalizer ha, fun h => by
    have := commV_apply_mem_of_normalizer (inv_mem ha) h
    simpa using this⟩

theorem inf_iff_apply {A B : Subgroup V} {a : MulAut V} (hA : ∀ u, u ∈ A ↔ a u ∈ A)
    (hB : ∀ u, u ∈ B ↔ a u ∈ B) : ∀ u, u ∈ A ⊓ B ↔ a u ∈ A ⊓ B := fun u => by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA u, hB u]


theorem bot_iff_apply (a : MulAut V) : ∀ u : V, u ∈ (⊥ : Subgroup V) ↔ a u ∈ (⊥ : Subgroup V) := by
  intro u
  rw [Subgroup.mem_bot, Subgroup.mem_bot]
  exact ⟨fun h => by rw [h, map_one], fun h => a.injective (by rw [h, map_one])⟩


section TwoSummands

variable {I₀ I₁ : Subgroup V} {S X : Subgroup (MulAut V)}

theorem mem_fixMod_bot {S : Subgroup (MulAut V)} {U : Subgroup V} {u : V} :
    u ∈ fixMod S U ⊥ ↔ u ∈ U ∧ ∀ s ∈ S, s u = u := by
  rw [mem_fixMod]
  refine and_congr_right fun _ => forall_congr' fun s => forall_congr' fun _ => ?_
  rw [Subgroup.mem_bot, mul_inv_eq_one]

theorem fixMod_two_mem {S X : Subgroup (MulAut V)} (hSX : S ≤ X) (hdis : Disjoint I₀ I₁)
    (hI₀ : ∀ x : ↥X, ∀ u, u ∈ I₀ ↔ (x : MulAut V) u ∈ I₀)
    (hI₁ : ∀ x : ↥X, ∀ u, u ∈ I₁ ↔ (x : MulAut V) u ∈ I₁) {u : V}
    (hu : u ∈ fixMod S (I₀ ⊔ I₁) ⊥) :
    ∃ u₀ u₁, u₀ ∈ fixMod S I₀ ⊥ ∧ u₁ ∈ fixMod S I₁ ⊥ ∧ u₀ * u₁ = u := by
  rw [mem_fixMod_bot] at hu
  obtain ⟨hU, hs⟩ := hu
  obtain ⟨u₀, h₀, u₁, h₁, rfl⟩ := Subgroup.mem_sup.1 hU
  refine ⟨u₀, u₁, ?_, ?_, rfl⟩
  · rw [mem_fixMod_bot]
    refine ⟨h₀, fun s hsS => ?_⟩
    have e := hs s hsS
    rw [map_mul] at e
    have p₀ : s u₀ * u₀⁻¹ ∈ I₀ := I₀.mul_mem ((hI₀ ⟨s, hSX hsS⟩ u₀).1 h₀) (I₀.inv_mem h₀)
    have p₁ : s u₁ * u₁⁻¹ ∈ I₁ := I₁.mul_mem ((hI₁ ⟨s, hSX hsS⟩ u₁).1 h₁) (I₁.inv_mem h₁)
    have hprod : (s u₀ * u₀⁻¹) * (s u₁ * u₁⁻¹) = 1 := by
      calc (s u₀ * u₀⁻¹) * (s u₁ * u₁⁻¹) = (s u₀ * s u₁) * (u₀ * u₁)⁻¹ := by
            rw [mul_inv, mul_mul_mul_comm]
        _ = 1 := by rw [e]; exact mul_inv_cancel _
    have hp0 : s u₀ * u₀⁻¹ = 1 := by
      have : s u₀ * u₀⁻¹ = (s u₁ * u₁⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      have h2 : s u₀ * u₀⁻¹ ∈ I₁ := by rw [this]; exact I₁.inv_mem p₁
      have := hdis.le_bot ⟨p₀, h2⟩
      exact Subgroup.mem_bot.1 this
    exact mul_inv_eq_one.1 hp0
  · rw [mem_fixMod_bot]
    refine ⟨h₁, fun s hsS => ?_⟩
    have e := hs s hsS
    rw [map_mul] at e
    have p₀ : s u₀ * u₀⁻¹ ∈ I₀ := I₀.mul_mem ((hI₀ ⟨s, hSX hsS⟩ u₀).1 h₀) (I₀.inv_mem h₀)
    have p₁ : s u₁ * u₁⁻¹ ∈ I₁ := I₁.mul_mem ((hI₁ ⟨s, hSX hsS⟩ u₁).1 h₁) (I₁.inv_mem h₁)
    have hprod : (s u₀ * u₀⁻¹) * (s u₁ * u₁⁻¹) = 1 := by
      calc (s u₀ * u₀⁻¹) * (s u₁ * u₁⁻¹) = (s u₀ * s u₁) * (u₀ * u₁)⁻¹ := by
            rw [mul_inv, mul_mul_mul_comm]
        _ = 1 := by rw [e]; exact mul_inv_cancel _
    have hp1 : s u₁ * u₁⁻¹ = 1 := by
      have : s u₁ * u₁⁻¹ = (s u₀ * u₀⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      have h2 : s u₁ * u₁⁻¹ ∈ I₀ := by rw [this]; exact I₀.inv_mem p₀
      have := hdis.le_bot ⟨h2, p₁⟩
      exact Subgroup.mem_bot.1 this
    exact mul_inv_eq_one.1 hp1


theorem fixMod_two_stable {S X : Subgroup (MulAut V)} (x : ↥X)
    (hSX : S ≤ X) (hdis : Disjoint I₀ I₁)
    (hI₀ : ∀ x : ↥X, ∀ u, u ∈ I₀ ↔ (x : MulAut V) u ∈ I₀)
    (hI₁ : ∀ x : ↥X, ∀ u, u ∈ I₁ ↔ (x : MulAut V) u ∈ I₁)
    (h₀ : ∀ w, w ∈ fixMod S I₀ ⊥ → (x : MulAut V) w ∈ fixMod S I₀ ⊥)
    (h₁ : ∀ w, w ∈ fixMod S I₁ ⊥ → (x : MulAut V) w ∈ fixMod S I₁ ⊥) :
    ∀ u, u ∈ fixMod S (I₀ ⊔ I₁) ⊥ → (x : MulAut V) u ∈ fixMod S (I₀ ⊔ I₁) ⊥ := by
  intro u hu
  obtain ⟨u₀, u₁, hu₀, hu₁, rfl⟩ := fixMod_two_mem hSX hdis hI₀ hI₁ hu
  have h0 := h₀ u₀ hu₀
  have h1 := h₁ u₁ hu₁
  rw [mem_fixMod_bot] at h0 h1 ⊢
  refine ⟨?_, fun s hs => ?_⟩
  · rw [map_mul]
    exact Subgroup.mul_mem_sup h0.1 h1.1
  · rw [map_mul, map_mul, h0.2 s hs, h1.2 s hs]

theorem setStab_two_iff {S X : Subgroup (MulAut V)} (x : ↥X)
    (hSX : S ≤ X) (hdis : Disjoint I₀ I₁)
    (hI₀ : ∀ x : ↥X, ∀ u, u ∈ I₀ ↔ (x : MulAut V) u ∈ I₀)
    (hI₁ : ∀ x : ↥X, ∀ u, u ∈ I₁ ↔ (x : MulAut V) u ∈ I₁)
    (h₀ : (x : MulAut V) ∈ setStab (fixMod S I₀ ⊥)) (h₁ : (x : MulAut V) ∈ setStab (fixMod S I₁ ⊥))
    (h₀' : (x⁻¹ : ↥X) ∈ (setStab (fixMod S I₀ ⊥)).comap X.subtype)
    (h₁' : (x⁻¹ : ↥X) ∈ (setStab (fixMod S I₁ ⊥)).comap X.subtype) :
    (x : MulAut V) ∈ setStab (fixMod S (I₀ ⊔ I₁) ⊥) := by
  have f1 := fixMod_two_stable x hSX hdis hI₀ hI₁ (fun w hw => (h₀ w).1 hw) (fun w hw => (h₁ w).1 hw)
  have f2 := fixMod_two_stable x⁻¹ hSX hdis hI₀ hI₁ (fun w hw => (h₀' w).1 hw)
    (fun w hw => (h₁' w).1 hw)
  intro u
  refine ⟨f1 u, fun hxu => ?_⟩
  have := f2 _ hxu
  simpa using this

end TwoSummands

end CFSG.Quasithin.SzN15
