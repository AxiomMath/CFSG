module

public import CFSG.Monster.B.Classical.PlaneData
import all CFSG.Fischer.F4
public import Mathlib.Tactic.Basify

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer

@[expose] def IsOn (a p : Fin 21) : Prop := ∑ k, Ω a k * Ω p k = 0

instance (a p : Fin 21) : Decidable (IsOn a p) := by unfold IsOn; infer_instance

theorem mem_projLine {a p : Fin 21} : p ∈ projLine a ↔ IsOn a p := by
  simp [projLine, IsOn]

@[expose] def cross (u v : Fin 3 → F4) : Fin 3 → F4 :=
  ![u 1 * v 2 + u 2 * v 1, u 2 * v 0 + u 0 * v 2, u 0 * v 1 + u 1 * v 0]

@[expose] def join (x y : Fin 21) : Fin 21 := normIdx (cross (Ω x) (Ω y))

@[expose] def meet (a b : Fin 21) : Fin 21 := normIdx (cross (Ω a) (Ω b))

theorem join_spec : ∀ x y : Fin 21, x ≠ y → IsOn (join x y) x ∧ IsOn (join x y) y := by
  decide +kernel

theorem join_unique : ∀ x y a : Fin 21, x ≠ y → IsOn a x → IsOn a y → a = join x y := by
  decide +kernel

theorem meet_spec : ∀ a b : Fin 21, a ≠ b → IsOn a (meet a b) ∧ IsOn b (meet a b) := by
  decide +kernel

theorem meet_unique : ∀ a b p : Fin 21, a ≠ b → IsOn a p → IsOn b p → p = meet a b := by
  decide +kernel

theorem exists_isOn : ∀ x : Fin 21, ∃ a, IsOn a x := by
  decide +kernel

@[expose] def lineMask : Fin 21 → ℕ :=
  ![139810, 481, 1082404, 544816, 329768, 31, 279618, 1118466, 559234, 7681, 590404, 295696,
    1065608, 1966081, 168008, 149764, 197776, 122881, 1058896, 533768, 274564]

theorem testBit_lineMask : ∀ a p : Fin 21, (lineMask a).testBit p = true ↔ IsOn a p := by
  decide +kernel

theorem mask_projLine : ∀ a : Fin 21, mask (projLine a) = lineMask a := by
  decide +kernel

theorem projLine_injective : Function.Injective projLine := by
  intro a b h
  have h' := congrArg mask h
  rw [mask_projLine, mask_projLine] at h'
  revert a b
  decide +kernel

@[expose] def lineThru : Fin 21 → Fin 21 → ℕ :=
  ![![2097151, 31, 31, 31, 31, 481, 481, 481, 481, 7681, 7681, 7681, 7681, 122881, 122881, 122881,
    122881, 1966081, 1966081, 1966081, 1966081],
    ![31, 2097151, 31, 31, 31, 139810, 279618, 559234, 1118466, 139810, 279618, 559234, 1118466,
      139810, 279618, 559234, 1118466, 139810, 279618, 559234, 1118466],
    ![31, 31, 2097151, 31, 31, 1082404, 590404, 274564, 149764, 590404, 1082404, 149764, 274564,
      274564, 149764, 1082404, 590404, 149764, 274564, 590404, 1082404],
    ![31, 31, 31, 2097151, 31, 329768, 168008, 1065608, 533768, 1065608, 533768, 329768, 168008,
      533768, 1065608, 168008, 329768, 168008, 329768, 533768, 1065608],
    ![31, 31, 31, 31, 2097151, 544816, 1058896, 197776, 295696, 295696, 197776, 1058896, 544816,
      1058896, 544816, 295696, 197776, 197776, 295696, 544816, 1058896],
    ![481, 139810, 1082404, 329768, 544816, 2097151, 481, 481, 481, 139810, 1082404, 329768, 544816,
      139810, 544816, 1082404, 329768, 139810, 329768, 544816, 1082404],
    ![481, 279618, 590404, 168008, 1058896, 481, 2097151, 481, 481, 590404, 279618, 1058896, 168008,
      1058896, 279618, 168008, 590404, 168008, 279618, 590404, 1058896],
    ![481, 559234, 274564, 1065608, 197776, 481, 481, 2097151, 481, 1065608, 197776, 559234, 274564,
      274564, 1065608, 559234, 197776, 197776, 274564, 559234, 1065608],
    ![481, 1118466, 149764, 533768, 295696, 481, 481, 481, 2097151, 295696, 533768, 149764, 1118466,
      533768, 149764, 295696, 1118466, 149764, 295696, 533768, 1118466],
    ![7681, 139810, 590404, 1065608, 295696, 139810, 590404, 1065608, 295696, 2097151, 7681, 7681,
      7681, 139810, 1065608, 295696, 590404, 139810, 295696, 590404, 1065608],
    ![7681, 279618, 1082404, 533768, 197776, 1082404, 279618, 197776, 533768, 7681, 2097151, 7681,
      7681, 533768, 279618, 1082404, 197776, 197776, 279618, 533768, 1082404],
    ![7681, 559234, 149764, 329768, 1058896, 329768, 1058896, 559234, 149764, 7681, 7681, 2097151,
      7681, 1058896, 149764, 559234, 329768, 149764, 329768, 559234, 1058896],
    ![7681, 1118466, 274564, 168008, 544816, 544816, 168008, 274564, 1118466, 7681, 7681, 7681,
      2097151, 274564, 544816, 168008, 1118466, 168008, 274564, 544816, 1118466],
    ![122881, 139810, 274564, 533768, 1058896, 139810, 1058896, 274564, 533768, 139810, 533768,
      1058896, 274564, 2097151, 122881, 122881, 122881, 139810, 274564, 533768, 1058896],
    ![122881, 279618, 149764, 1065608, 544816, 544816, 279618, 1065608, 149764, 1065608, 279618,
      149764, 544816, 122881, 2097151, 122881, 122881, 149764, 279618, 544816, 1065608],
    ![122881, 559234, 1082404, 168008, 295696, 1082404, 168008, 559234, 295696, 295696, 1082404,
      559234, 168008, 122881, 122881, 2097151, 122881, 168008, 295696, 559234, 1082404],
    ![122881, 1118466, 590404, 329768, 197776, 329768, 590404, 197776, 1118466, 590404, 197776,
      329768, 1118466, 122881, 122881, 122881, 2097151, 197776, 329768, 590404, 1118466],
    ![1966081, 139810, 149764, 168008, 197776, 139810, 168008, 197776, 149764, 139810, 197776,
      149764, 168008, 139810, 149764, 168008, 197776, 2097151, 1966081, 1966081, 1966081],
    ![1966081, 279618, 274564, 329768, 295696, 329768, 279618, 274564, 295696, 295696, 279618,
      329768, 274564, 274564, 279618, 295696, 329768, 1966081, 2097151, 1966081, 1966081],
    ![1966081, 559234, 590404, 533768, 544816, 544816, 590404, 559234, 533768, 590404, 533768,
      559234, 544816, 533768, 544816, 559234, 590404, 1966081, 1966081, 2097151, 1966081],
    ![1966081, 1118466, 1082404, 1065608, 1058896, 1082404, 1058896, 1065608, 1118466, 1065608,
      1082404, 1058896, 1118466, 1058896, 1065608, 1082404, 1118466, 1966081, 1966081, 1966081,
      2097151]]

theorem lineThru_of_ne : ∀ x y : Fin 21, x ≠ y → lineThru x y = lineMask (join x y) := by
  decide +kernel

theorem lineThru_self : ∀ x : Fin 21, lineThru x x = 2 ^ 21 - 1 := by
  decide +kernel

@[expose] def colB (x y z : Fin 21) : Bool := (lineThru x y).testBit z

theorem collinear3_of_ne {x y : Fin 21} (hxy : x ≠ y) (z : Fin 21) :
    Collinear3 x y z ↔ IsOn (join x y) z := by
  constructor
  · rintro ⟨a, hx, hy, hz⟩
    rw [mem_projLine] at hx hy hz
    rwa [← join_unique x y a hxy hx hy]
  · intro hz
    exact ⟨join x y, mem_projLine.2 (join_spec x y hxy).1, mem_projLine.2 (join_spec x y hxy).2,
      mem_projLine.2 hz⟩

theorem collinear3_self (x z : Fin 21) : Collinear3 x x z := by
  by_cases hxz : x = z
  · subst hxz
    obtain ⟨a, ha⟩ := exists_isOn x
    exact ⟨a, mem_projLine.2 ha, mem_projLine.2 ha, mem_projLine.2 ha⟩
  · exact ⟨join x z, mem_projLine.2 (join_spec x z hxz).1, mem_projLine.2 (join_spec x z hxz).1,
      mem_projLine.2 (join_spec x z hxz).2⟩

theorem colB_iff (x y z : Fin 21) : colB x y z = true ↔ Collinear3 x y z := by
  by_cases hxy : x = y
  · subst hxy
    refine iff_of_true ?_ (collinear3_self x z)
    rw [colB, lineThru_self]
    revert z
    decide +kernel
  · rw [collinear3_of_ne hxy, colB, lineThru_of_ne x y hxy, testBit_lineMask]

@[expose] def lineAut : Subgroup (Equiv.Perm (Fin 21)) where
  carrier := {σ | ∀ a, ∃ b, (projLine a).map σ.toEmbedding = projLine b}
  mul_mem' {σ τ} hσ hτ a := by
    obtain ⟨b, hb⟩ := hτ a
    obtain ⟨c, hc⟩ := hσ b
    refine ⟨c, ?_⟩
    rw [← hc, ← hb, Finset.map_map]
    rfl
  one_mem' a := ⟨a, Finset.map_refl⟩
  inv_mem' {σ} hσ a := by
    choose f hf using hσ
    have hinj : Function.Injective f := by
      intro a b hab
      apply projLine_injective
      have h := (hf a).trans ((congrArg projLine hab).trans (hf b).symm)
      exact Finset.map_injective _ h
    obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 hinj a
    refine ⟨c, ?_⟩
    rw [← hc, ← hf c, Finset.map_map]
    ext p
    simp

theorem mem_lineAut {σ : Equiv.Perm (Fin 21)} :
    σ ∈ lineAut ↔ ∀ a, ∃ b, (projLine a).map σ.toEmbedding = projLine b := Iff.rfl

variable {σ : Equiv.Perm (Fin 21)}

theorem map_projLine_join (hσ : σ ∈ lineAut) {x y : Fin 21} (hxy : x ≠ y) :
    (projLine (join x y)).map σ.toEmbedding = projLine (join (σ x) (σ y)) := by
  obtain ⟨b, hb⟩ := hσ (join x y)
  have hx : σ x ∈ projLine b := by
    rw [← hb]
    exact Finset.mem_map_of_mem _ (mem_projLine.2 (join_spec x y hxy).1)
  have hy : σ y ∈ projLine b := by
    rw [← hb]
    exact Finset.mem_map_of_mem _ (mem_projLine.2 (join_spec x y hxy).2)
  rw [hb, join_unique (σ x) (σ y) b (σ.injective.ne hxy) (mem_projLine.1 hx) (mem_projLine.1 hy)]

theorem collinear3_map (hσ : σ ∈ lineAut) {x y z : Fin 21} (h : Collinear3 x y z) :
    Collinear3 (σ x) (σ y) (σ z) := by
  obtain ⟨a, hx, hy, hz⟩ := h
  obtain ⟨b, hb⟩ := hσ a
  refine ⟨b, ?_, ?_, ?_⟩ <;> rw [← hb] <;> exact Finset.mem_map_of_mem _ ‹_›

theorem collinear3_map_iff (hσ : σ ∈ lineAut) {x y z : Fin 21} :
    Collinear3 (σ x) (σ y) (σ z) ↔ Collinear3 x y z := by
  refine ⟨fun h => ?_, collinear3_map hσ⟩
  have := collinear3_map (inv_mem hσ) h
  simpa using this

theorem map_projLine_join_of_fix (hσ : σ ∈ lineAut) {x y : Fin 21} (hxy : x ≠ y)
    (hx : σ x = x) (hy : σ y = y) :
    (projLine (join x y)).map σ.toEmbedding = projLine (join x y) := by
  rw [map_projLine_join hσ hxy, hx, hy]

theorem apply_meet_of_fix {a b : Fin 21} (hab : a ≠ b)
    (ha : (projLine a).map σ.toEmbedding = projLine a)
    (hb : (projLine b).map σ.toEmbedding = projLine b) : σ (meet a b) = meet a b := by
  have h1 : σ (meet a b) ∈ projLine a := by
    rw [← ha]
    exact Finset.mem_map_of_mem _ (mem_projLine.2 (meet_spec a b hab).1)
  have h2 : σ (meet a b) ∈ projLine b := by
    rw [← hb]
    exact Finset.mem_map_of_mem _ (mem_projLine.2 (meet_spec a b hab).2)
  exact meet_unique a b _ hab (mem_projLine.1 h1) (mem_projLine.1 h2)

inductive JMStep
  | line (a x y : Fin 21)
  | point (p a b : Fin 21)

@[expose] def JMStep.valid (P L : List (Fin 21)) : JMStep → Bool
  | .line a x y => decide (x ∈ P) && decide (y ∈ P) && decide (x ≠ y) && decide (a = join x y)
  | .point p a b => decide (a ∈ L) && decide (b ∈ L) && decide (a ≠ b) && decide (p = meet a b)

@[expose] def JMStep.add : JMStep → List (Fin 21) × List (Fin 21) → List (Fin 21) × List (Fin 21)
  | .line a _ _, (P, L) => (P, a :: L)
  | .point p _ _, (P, L) => (p :: P, L)

@[expose] def JMStep.run : List JMStep → List (Fin 21) × List (Fin 21) →
    Option (List (Fin 21) × List (Fin 21))
  | [], s => some s
  | t :: ts, s => if t.valid s.1 s.2 then JMStep.run ts (t.add s) else none

theorem JMStep.run_sound (hσ : σ ∈ lineAut) :
    ∀ (ts : List JMStep) (s r : List (Fin 21) × List (Fin 21)), JMStep.run ts s = some r →
      (∀ p ∈ s.1, σ p = p) → (∀ a ∈ s.2, (projLine a).map σ.toEmbedding = projLine a) →
      ∀ p ∈ r.1, σ p = p
  | [], s, r, h, hP, _ => by
    simp only [JMStep.run, Option.some.injEq] at h
    subst h
    exact hP
  | t :: ts, ⟨P, L⟩, r, h, hP, hL => by
    simp only [JMStep.run] at h
    split_ifs at h with hv
    cases t with
    | line a x y =>
      simp only [JMStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨⟨hx, hy⟩, hxy⟩, rfl⟩ := hv
      refine JMStep.run_sound hσ ts _ r h hP ?_
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact map_projLine_join_of_fix hσ hxy (hP x hx) (hP y hy)
      · exact hL b hb
    | point p a b =>
      simp only [JMStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨⟨ha, hb⟩, hab⟩, rfl⟩ := hv
      refine JMStep.run_sound hσ ts _ r h ?_ hL
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact apply_meet_of_fix hab (hL a ha) (hL b hb)
      · exact hP q hq

@[expose] def frameTrace : List JMStep :=
  [.line 5 0 1, .line 1 0 5, .line 9 0 10, .line 17 0 13, .line 0 1 5, .line 6 1 10,
    .line 2 5 10, .line 19 10 13, .point 9 0 9, .point 6 1 6, .point 8 1 19, .point 2 2 5,
    .point 15 2 17, .point 3 5 19, .point 14 6 17, .line 7 1 8, .line 8 1 15, .line 10 2 6,
    .line 15 2 8, .line 20 2 13, .line 4 3 5, .line 14 3 6, .line 12 3 9, .line 3 5 14,
    .line 18 6 13, .line 11 8 9, .point 17 0 14, .point 7 1 8, .point 20 2 7, .point 4 3 5,
    .point 12 3 7, .point 19 3 8, .point 18 4 6, .point 16 4 7, .point 11 4 8, .line 13 0 17,
    .line 16 4 7]

theorem frameTrace_run : ∃ r, JMStep.run frameTrace ([5, 1, 0, 10, 13], []) = some r ∧
    ∀ p : Fin 21, p ∈ r.1 := by
  refine ⟨_, rfl, ?_⟩
  decide +kernel

theorem eq_one_of_fix_five (hσ : σ ∈ lineAut) (h5 : σ 5 = 5) (h1 : σ 1 = 1) (h0 : σ 0 = 0)
    (h10 : σ 10 = 10) (h13 : σ 13 = 13) : σ = 1 := by
  obtain ⟨r, hr, hall⟩ := frameTrace_run
  have := JMStep.run_sound hσ frameTrace _ r hr (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption) (by simp)
  exact Equiv.ext fun p => this p (hall p)

end CFSG.Monster.B.Classical.Plane
