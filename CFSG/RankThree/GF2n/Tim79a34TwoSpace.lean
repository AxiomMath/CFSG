module

public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.RankThree.GF2n.Tim79a34TwoModel
public import Mathlib.Tactic.Group
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoSpace

section Part1

open CFSG.RankThree.GF2n.Tim79a.TwoModel
open scoped commutatorElement

variable {G : Type} [Group G]

structure PCoords (P V : Subgroup G) (θ : P → Vec4) : Prop where
  add : ∀ p q, θ (p * q) = θ p + θ q
  surj : Function.Surjective θ
  ker : ∀ p, θ p = 0 ↔ (p : G) ∈ V
  comm : ∀ p q : P, ⁅(p : G), (q : G)⁆ = 1 ↔ bf (θ p) (θ q) = 0
  sq : ∀ p : P, (p : G) * p = 1 ↔ qf (θ p) = 0

end Part1

section Part2

open CFSG.RankThree.GF2n.Tim79a.TwoModel
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

open _root_.Classical in
@[expose] noncomputable def comBit (x y : G) : ZMod 2 :=
  if ⁅x, y⁆ = 1 then 0 else 1

open _root_.Classical in
@[expose] noncomputable def sqBit (x : G) : ZMod 2 :=
  if x * x = 1 then 0 else 1

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

theorem zmod2_eq_of_add_eq_zero : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := by decide

theorem comBit_eq_zero_iff {x y : G} : comBit x y = 0 ↔ ⁅x, y⁆ = 1 := by
  unfold comBit
  by_cases h : ⁅x, y⁆ = 1 <;> simp [h]

theorem sqBit_eq_zero_iff {x : G} : sqBit x = 0 ↔ x * x = 1 := by
  unfold sqBit
  by_cases h : x * x = 1 <;> simp [h]

theorem comBit_comm (x y : G) : comBit x y = comBit y x := by
  have h : ⁅x, y⁆ = 1 ↔ ⁅y, x⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm]
    exact eq_comm
  unfold comBit
  by_cases h1 : ⁅x, y⁆ = 1
  · rw [if_pos h1, if_pos (h.mp h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (h.mpr h2))]

theorem comBit_self (x : G) : comBit x x = 0 := by
  rw [comBit_eq_zero_iff, commutatorElement_self]

theorem comBit_one_left (x : G) : comBit (1 : G) x = 0 := by
  rw [comBit_eq_zero_iff, commutatorElement_one_left]

theorem comBit_one_right (x : G) : comBit x (1 : G) = 0 := by
  rw [comBit_eq_zero_iff, commutatorElement_one_right]

theorem sqBit_one : sqBit (1 : G) = 0 := by
  rw [sqBit_eq_zero_iff, one_mul]

theorem comm_mul_left' (p q r : G) (hc : ⁅q, r⁆ * p = p * ⁅q, r⁆) :
    ⁅p * q, r⁆ = ⁅q, r⁆ * ⁅p, r⁆ := by
  have hc' : p * ⁅q, r⁆ = ⁅q, r⁆ * p := hc.symm
  calc ⁅p * q, r⁆ = p * ⁅q, r⁆ * p⁻¹ * ⁅p, r⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅q, r⁆ * p * p⁻¹ * ⁅p, r⁆ := by rw [hc']
    _ = ⁅q, r⁆ * ⁅p, r⁆ := by group

theorem sq_mul_identity (p q : G) (hp : ⁅q, p⁆ * p = p * ⁅q, p⁆)
    (hq : ⁅q, p⁆ * q = q * ⁅q, p⁆) : p * q * (p * q) = p * p * (q * q) * ⁅q, p⁆ := by
  have hqp : q * p = ⁅q, p⁆ * (p * q) := by
    simp only [commutatorElement_def]; group
  have hqq : ⁅q, p⁆ * (q * q) = q * q * ⁅q, p⁆ := by
    calc ⁅q, p⁆ * (q * q) = ⁅q, p⁆ * q * q := by group
      _ = q * ⁅q, p⁆ * q := by rw [hq]
      _ = q * (⁅q, p⁆ * q) := by group
      _ = q * (q * ⁅q, p⁆) := by rw [hq]
      _ = q * q * ⁅q, p⁆ := by group
  calc p * q * (p * q) = p * (q * p) * q := by group
    _ = p * (⁅q, p⁆ * (p * q)) * q := by rw [hqp]
    _ = p * (⁅q, p⁆ * p) * q * q := by group
    _ = p * (p * ⁅q, p⁆) * q * q := by rw [hp]
    _ = p * p * (⁅q, p⁆ * (q * q)) := by group
    _ = p * p * (q * q * ⁅q, p⁆) := by rw [hqq]
    _ = p * p * (q * q) * ⁅q, p⁆ := by group

structure CoordSetup (P V F : Subgroup G) (a t0 t1 : G) : Prop where
  hVP : V ≤ P
  hFP : F ≤ P
  hP : Nat.card P = 64
  hV : Nat.card V = 4
  ha : a ∈ V
  ha1 : a ≠ 1
  hVc : ∀ z ∈ V, ∀ p ∈ P, z * p = p * z
  hcV : ∀ p ∈ P, (∀ q ∈ P, p * q = q * p) → p ∈ V
  hVsq : ∀ z ∈ V, z * z = 1
  hcomm : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = a
  hsq : ∀ p ∈ P, p * p = 1 ∨ p * p = a
  hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f
  hFsq : ∀ f ∈ F, f * f = 1
  ht0 : t0 ∈ F
  ht1 : t1 ∈ F
  hind : ∀ z ∈ V, z ≠ t0 ∧ z ≠ t1 ∧ z ≠ t0 * t1

structure CoordFrame (P V F : Subgroup G) (a t0 t1 w0 w1 : G) : Prop extends
    CoordSetup P V F a t0 t1 where
  w0P : w0 ∈ P
  w1P : w1 ∈ P
  sw0 : sqBit w0 = 0
  sw1 : sqBit w1 = 0
  k00 : comBit t0 w0 = 1
  k01 : comBit t1 w0 = 0
  k10 : comBit t0 w1 = 0
  k11 : comBit t1 w1 = 1
  kw : comBit w0 w1 = 0

theorem comm_mem_V {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {p q : G} (hp : p ∈ P) (hq : q ∈ P) : ⁅p, q⁆ ∈ V := by
  rcases S.hcomm p hp q hq with h | h
  · rw [h]
    exact V.one_mem
  · rw [h]
    exact S.ha

theorem comBit_mul_left {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {p q r : G} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    comBit (p * q) r = comBit p r + comBit q r := by
  have hc : ⁅q, r⁆ * p = p * ⁅q, r⁆ := S.hVc _ (comm_mem_V S hq hr) p hp
  unfold comBit
  rw [comm_mul_left' p q r hc]
  rcases S.hcomm p hp r hr with h1 | h1 <;> rcases S.hcomm q hq r hr with h2 | h2 <;>
    simp [h1, h2, S.ha1, S.hVsq a S.ha, one_add_one_zmod2]

theorem comBit_mul_right {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {p q r : G} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    comBit p (q * r) = comBit p q + comBit p r := by
  rw [comBit_comm p (q * r), comBit_mul_left S hq hr hp, comBit_comm q p, comBit_comm r p]

theorem comBit_central_left {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {z p : G} (hz : z ∈ V) (hp : p ∈ P) : comBit z p = 0 :=
  comBit_eq_zero_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (S.hVc z hz p hp))

theorem comBit_central_right {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {p z : G} (hp : p ∈ P) (hz : z ∈ V) : comBit p z = 0 := by
  rw [comBit_comm]
  exact comBit_central_left S hz hp

theorem comBit_F {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {f g : G} (hf : f ∈ F) (hg : g ∈ F) : comBit f g = 0 :=
  comBit_eq_zero_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (S.hFc f hf g hg))

theorem sqBit_mul {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {p q : G} (hp : p ∈ P) (hq : q ∈ P) :
    sqBit (p * q) = sqBit p + sqBit q + comBit p q := by
  have hc1 : ⁅q, p⁆ * p = p * ⁅q, p⁆ := S.hVc _ (comm_mem_V S hq hp) p hp
  have hc2 : ⁅q, p⁆ * q = q * ⁅q, p⁆ := S.hVc _ (comm_mem_V S hq hp) q hq
  rw [comBit_comm p q]
  unfold sqBit comBit
  rw [sq_mul_identity p q hc1 hc2]
  rcases S.hsq p hp with h1 | h1 <;> rcases S.hsq q hq with h2 | h2 <;>
    rcases S.hcomm q hq p hp with h3 | h3 <;>
    simp [h1, h2, h3, S.ha1, S.hVsq a S.ha, one_add_one_zmod2]

theorem sqBit_F {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {f : G} (hf : f ∈ F) : sqBit f = 0 :=
  sqBit_eq_zero_iff.mpr (S.hFsq f hf)

theorem sqBit_central {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {z : G} (hz : z ∈ V) : sqBit z = 0 :=
  sqBit_eq_zero_iff.mpr (S.hVsq z hz)

theorem exists_p10 {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1) {s t : G}
    (hs : s ∈ F) (ht : t ∈ F) (hi : ∀ z ∈ V, z ≠ s ∧ z ≠ t ∧ z ≠ s * t) :
    ∃ p ∈ P, comBit s p = 1 ∧ comBit t p = 0 := by
  by_contra H
  have H' : ∀ p ∈ P, comBit s p = 1 → comBit t p ≠ 0 :=
    fun p hp h1 h2 => H ⟨p, hp, h1, h2⟩
  have hsP : s ∈ P := S.hFP hs
  have htP : t ∈ P := S.hFP ht
  obtain ⟨p₁, hp₁, hk₁⟩ : ∃ p ∈ P, comBit s p = 1 := by
    by_contra H1
    have hcen : ∀ q ∈ P, s * q = q * s := by
      intro q hq
      have h0 : comBit s q = 0 := by
        rcases zmod2_cases (comBit s q) with h | h
        · exact h
        · exact absurd ⟨q, hq, h⟩ H1
      exact commutatorElement_eq_one_iff_mul_comm.mp (comBit_eq_zero_iff.mp h0)
    exact (hi s (S.hcV s hsP hcen)).1 rfl
  have hk₂ : comBit t p₁ = 1 := by
    rcases zmod2_cases (comBit t p₁) with h | h
    · exact absurd h (H' p₁ hp₁ hk₁)
    · exact h
  have hiii : ∀ p ∈ P, comBit t p = 1 → comBit s p = 1 := by
    intro p hp hp1
    by_contra hne
    have h0 : comBit s p = 0 := (zmod2_cases (comBit s p)).resolve_right hne
    have hq : p * p₁ ∈ P := P.mul_mem hp hp₁
    have e1 : comBit s (p * p₁) = 1 := by
      rw [comBit_mul_right S hsP hp hp₁, h0, hk₁, zero_add]
    have e2 : comBit t (p * p₁) = 0 := by
      rw [comBit_mul_right S htP hp hp₁, hp1, hk₂] <;> decide
    exact H' (p * p₁) hq e1 e2
  have hiv : ∀ p ∈ P, comBit s p = comBit t p := by
    intro p hp
    rcases zmod2_cases (comBit t p) with h | h
    · rw [h]
      rcases zmod2_cases (comBit s p) with h' | h'
      · exact h'
      · exact absurd h (H' p hp h')
    · rw [h]
      exact hiii p hp h
  have hv : ∀ p ∈ P, ⁅s * t, p⁆ = 1 := by
    intro p hp
    refine comBit_eq_zero_iff.mp ?_
    rw [comBit_mul_left S hsP htP hp, hiv p hp]
    exact zmod2_add_self _
  have hst : s * t ∈ V :=
    S.hcV (s * t) (P.mul_mem hsP htP)
      (fun q hq => commutatorElement_eq_one_iff_mul_comm.mp (hv q hq))
  exact (hi (s * t) hst).2.2 rfl

theorem exists_normal {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1)
    {f g u : G} (hf : f ∈ F) (hg : g ∈ F) (hu : u ∈ P) (h1 : comBit f u = 1)
    (h2 : comBit g u = 0) : ∃ w ∈ P, sqBit w = 0 ∧ comBit f w = 1 ∧ comBit g w = 0 := by
  by_cases hs : sqBit u = 0
  · exact ⟨u, hu, hs, h1, h2⟩
  · have hs1 : sqBit u = 1 := (zmod2_cases _).resolve_left hs
    have hfP : f ∈ P := S.hFP hf
    refine ⟨u * f, P.mul_mem hu hfP, ?_, ?_, ?_⟩
    · rw [sqBit_mul S hu hfP, sqBit_F S hf, comBit_comm u f, h1, hs1] <;> decide
    · rw [comBit_mul_right S hfP hu hfP, h1, comBit_self, add_zero]
    · rw [comBit_mul_right S (S.hFP hg) hu hfP, h2, comBit_F S hg hf, add_zero]

theorem exists_fix {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1) {w0 w1 : G}
    (h0 : w0 ∈ P) (h1 : w1 ∈ P) (hs : sqBit w1 = 0) (ha : comBit t0 w1 = 0)
    (hb : comBit t1 w1 = 1) (hk : comBit t0 w0 = 1) :
    ∃ w ∈ P, sqBit w = 0 ∧ comBit t0 w = 0 ∧ comBit t1 w = 1 ∧ comBit w0 w = 0 := by
  by_cases hc : comBit w0 w1 = 0
  · exact ⟨w1, h1, hs, ha, hb, hc⟩
  · have hc1 : comBit w0 w1 = 1 := (zmod2_cases _).resolve_left hc
    have ht0P : t0 ∈ P := S.hFP S.ht0
    have ht1P : t1 ∈ P := S.hFP S.ht1
    refine ⟨w1 * t0, P.mul_mem h1 ht0P, ?_, ?_, ?_, ?_⟩
    · rw [sqBit_mul S h1 ht0P, hs, sqBit_F S S.ht0, comBit_comm w1 t0, ha] <;> decide
    · rw [comBit_mul_right S ht0P h1 ht0P, ha, comBit_self, add_zero]
    · rw [comBit_mul_right S ht1P h1 ht0P, hb, comBit_F S S.ht1 S.ht0, add_zero]
    · rw [comBit_mul_right S h0 h1 ht0P, hc1, comBit_comm w0 t0, hk] <;> decide

theorem exists_frame {P V F : Subgroup G} {a t0 t1 : G} (S : CoordSetup P V F a t0 t1) :
    ∃ w0 w1 : G, CoordFrame P V F a t0 t1 w0 w1 := by
  have hind' : ∀ z ∈ V, z ≠ t1 ∧ z ≠ t0 ∧ z ≠ t1 * t0 := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := S.hind z hz
    refine ⟨h2, h1, ?_⟩
    rw [← S.hFc t0 S.ht0 t1 S.ht1]
    exact h3
  obtain ⟨u0, hu0P, hu0a, hu0b⟩ := exists_p10 S S.ht0 S.ht1 S.hind
  obtain ⟨u1, hu1P, hu1a, hu1b⟩ := exists_p10 S S.ht1 S.ht0 hind'
  obtain ⟨w0, hw0P, hw0s, hw0a, hw0b⟩ := exists_normal S S.ht0 S.ht1 hu0P hu0a hu0b
  obtain ⟨w1', hw1P, hw1s, hw1a, hw1b⟩ := exists_normal S S.ht1 S.ht0 hu1P hu1a hu1b
  obtain ⟨w1, hw1P', hw1s', hw1b', hw1a', hw1c⟩ :=
    exists_fix S hw0P hw1P hw1s hw1b hw1a hw0a
  exact ⟨w0, w1, ⟨S, hw0P, hw1P', hw0s, hw1s', hw0a, hw0b, hw1b', hw1a', hw1c⟩⟩

theorem bf_add_left' (x y z : Vec4) : bf (x + y) z = bf x z + bf y z := by
  unfold bf
  simp only [Pi.add_apply]
  ring

theorem ite_one_mem {Q : Subgroup G} {g : G} (hg : g ∈ Q) (c : ZMod 2) :
    (if c = 0 then (1 : G) else g) ∈ Q := by
  split_ifs
  · exact Q.one_mem
  · exact hg

theorem ite_vanish {d : G → ZMod 2} (h1 : d 1 = 0) {g : G} (hg : d g = 0) (c : ZMod 2) :
    d (if c = 0 then (1 : G) else g) = 0 := by
  split_ifs
  · exact h1
  · exact hg

@[expose] def sectMap (t0 t1 w0 w1 : G) (c : Vec4) : G :=
  (if c 0 = 0 then 1 else t0) * (if c 1 = 0 then 1 else t1) *
    (if c 2 = 0 then 1 else w0) * (if c 3 = 0 then 1 else w1)

@[expose] noncomputable def coordMap (t0 t1 w0 w1 x : G) : Vec4 :=
  ![comBit w0 x, comBit w1 x, comBit t0 x, comBit t1 x]

theorem sectMap_zero {t0 t1 w0 w1 : G} : sectMap t0 t1 w0 w1 0 = 1 := by
  simp [sectMap]

theorem coordMap_one {t0 t1 w0 w1 : G} : coordMap t0 t1 w0 w1 1 = 0 := by
  funext i
  fin_cases i <;> simp [coordMap, comBit_one_right]

theorem coordMap_mul {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    coordMap t0 t1 w0 w1 (x * y) = coordMap t0 t1 w0 w1 x + coordMap t0 t1 w0 w1 y := by
  have h0 := comBit_mul_right S.toCoordSetup S.w0P hx hy
  have h1 := comBit_mul_right S.toCoordSetup S.w1P hx hy
  have h2 := comBit_mul_right S.toCoordSetup (S.hFP S.ht0) hx hy
  have h3 := comBit_mul_right S.toCoordSetup (S.hFP S.ht1) hx hy
  funext i
  fin_cases i <;> simp [coordMap, h0, h1, h2, h3]

theorem coordMap_V {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {z : G} (hz : z ∈ V) :
    coordMap t0 t1 w0 w1 z = 0 := by
  have h0 := comBit_central_right S.toCoordSetup S.w0P hz
  have h1 := comBit_central_right S.toCoordSetup S.w1P hz
  have h2 := comBit_central_right S.toCoordSetup (S.hFP S.ht0) hz
  have h3 := comBit_central_right S.toCoordSetup (S.hFP S.ht1) hz
  funext i
  fin_cases i <;> simp [coordMap, h0, h1, h2, h3]

theorem coordMap_t0 {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : coordMap t0 t1 w0 w1 t0 = e0 := by
  have h0 : comBit w0 t0 = 1 := by
    rw [comBit_comm]
    exact S.k00
  have h1 : comBit w1 t0 = 0 := by
    rw [comBit_comm]
    exact S.k10
  have h2 : comBit t0 t0 = 0 := comBit_self t0
  have h3 : comBit t1 t0 = 0 := comBit_F S.toCoordSetup S.ht1 S.ht0
  funext i
  fin_cases i <;> simp [coordMap, e0, h0, h1, h2, h3]

theorem coordMap_t1 {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : coordMap t0 t1 w0 w1 t1 = e1 := by
  have h0 : comBit w0 t1 = 0 := by
    rw [comBit_comm]
    exact S.k01
  have h1 : comBit w1 t1 = 1 := by
    rw [comBit_comm]
    exact S.k11
  have h2 : comBit t0 t1 = 0 := comBit_F S.toCoordSetup S.ht0 S.ht1
  have h3 : comBit t1 t1 = 0 := comBit_self t1
  funext i
  fin_cases i <;> simp [coordMap, e1, h0, h1, h2, h3]

theorem coordMap_w0 {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : coordMap t0 t1 w0 w1 w0 = e2 := by
  have h0 : comBit w0 w0 = 0 := comBit_self w0
  have h1 : comBit w1 w0 = 0 := by
    rw [comBit_comm]
    exact S.kw
  have h2 : comBit t0 w0 = 1 := S.k00
  have h3 : comBit t1 w0 = 0 := S.k01
  funext i
  fin_cases i <;> simp [coordMap, e2, h0, h1, h2, h3]

theorem coordMap_w1 {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : coordMap t0 t1 w0 w1 w1 = e3 := by
  have h0 : comBit w0 w1 = 0 := S.kw
  have h1 : comBit w1 w1 = 0 := comBit_self w1
  have h2 : comBit t0 w1 = 0 := S.k10
  have h3 : comBit t1 w1 = 1 := S.k11
  funext i
  fin_cases i <;> simp [coordMap, e3, h0, h1, h2, h3]

theorem coordMap_ite {t0 t1 w0 w1 g : G} {v : Vec4} (hg : coordMap t0 t1 w0 w1 g = v)
    (c : ZMod 2) : coordMap t0 t1 w0 w1 (if c = 0 then (1 : G) else g) = c • v := by
  rcases zmod2_cases c with rfl | rfl
  · rw [if_pos rfl, coordMap_one, zero_smul]
  · rw [if_neg one_ne_zero, one_smul, hg]

theorem sectMap_mem {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) (c : Vec4) : sectMap t0 t1 w0 w1 c ∈ P := by
  unfold sectMap
  exact P.mul_mem (P.mul_mem (P.mul_mem (ite_one_mem (S.hFP S.ht0) (c 0))
    (ite_one_mem (S.hFP S.ht1) (c 1))) (ite_one_mem S.w0P (c 2))) (ite_one_mem S.w1P (c 3))

theorem coordMap_sect {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) (c : Vec4) :
    coordMap t0 t1 w0 w1 (sectMap t0 t1 w0 w1 c) = c := by
  have m0 : (if c 0 = 0 then (1 : G) else t0) ∈ P := ite_one_mem (S.hFP S.ht0) (c 0)
  have m1 : (if c 1 = 0 then (1 : G) else t1) ∈ P := ite_one_mem (S.hFP S.ht1) (c 1)
  have m2 : (if c 2 = 0 then (1 : G) else w0) ∈ P := ite_one_mem S.w0P (c 2)
  have m3 : (if c 3 = 0 then (1 : G) else w1) ∈ P := ite_one_mem S.w1P (c 3)
  unfold sectMap
  rw [coordMap_mul S (P.mul_mem (P.mul_mem m0 m1) m2) m3,
    coordMap_mul S (P.mul_mem m0 m1) m2, coordMap_mul S m0 m1,
    coordMap_ite (coordMap_t0 S) (c 0), coordMap_ite (coordMap_t1 S) (c 1),
    coordMap_ite (coordMap_w0 S) (c 2), coordMap_ite (coordMap_w1 S) (c 3)]
  exact (vec4_eq_sum c).symm

theorem card_vec4 : Nat.card Vec4 = 16 := by
  show Nat.card (Fin 4 → ZMod 2) = 16
  rw [Nat.card_fun]
  simp

@[expose] def psiMap {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) (q : Vec4 × V) : P :=
  ⟨sectMap t0 t1 w0 w1 q.1 * q.2, P.mul_mem (sectMap_mem S q.1) (S.hVP q.2.2)⟩

theorem psiMap_injective {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : Function.Injective (psiMap S) := by
  rintro ⟨c, u⟩ ⟨c', u'⟩ h
  have h1 : sectMap t0 t1 w0 w1 c * (u : G) = sectMap t0 t1 w0 w1 c' * (u' : G) :=
    congrArg Subtype.val h
  have hc : c = c' := by
    have h2 := congrArg (coordMap t0 t1 w0 w1) h1
    rw [coordMap_mul S (sectMap_mem S c) (S.hVP u.2),
      coordMap_mul S (sectMap_mem S c') (S.hVP u'.2), coordMap_sect S, coordMap_sect S,
      coordMap_V S u.2, coordMap_V S u'.2, add_zero, add_zero] at h2
    exact h2
  subst hc
  have hu : (u : G) = (u' : G) := mul_left_cancel h1
  have hu' : u = u' := Subtype.ext hu
  rw [hu']

theorem psiMap_surjective {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) : Function.Surjective (psiMap S) := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [S.hP]; norm_num)
  have hcard : Nat.card (Vec4 × V) = Nat.card P := by
    rw [Nat.card_prod, card_vec4, S.hV, S.hP] <;> norm_num
  exact ((Nat.bijective_iff_injective_and_card (psiMap S)).mpr
    ⟨psiMap_injective S, hcard⟩).2

theorem normal_form {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {x : G} (hx : x ∈ P) :
    ∃ z ∈ V, x = sectMap t0 t1 w0 w1 (coordMap t0 t1 w0 w1 x) * z := by
  obtain ⟨⟨c, u⟩, hcu⟩ := psiMap_surjective S ⟨x, hx⟩
  have hx' : sectMap t0 t1 w0 w1 c * (u : G) = x := congrArg Subtype.val hcu
  have hcoord : coordMap t0 t1 w0 w1 x = c := by
    rw [← hx', coordMap_mul S (sectMap_mem S c) (S.hVP u.2), coordMap_sect S,
      coordMap_V S u.2, add_zero]
  exact ⟨(u : G), u.2, by rw [hcoord, hx']⟩

theorem coordMap_eq_zero_iff {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {x : G} (hx : x ∈ P) :
    coordMap t0 t1 w0 w1 x = 0 ↔ x ∈ V := by
  constructor
  · intro h
    obtain ⟨z, hz, hxz⟩ := normal_form S hx
    rw [h, sectMap_zero, one_mul] at hxz
    rw [hxz]
    exact hz
  · intro h
    exact coordMap_V S h

theorem vanish_of_additive {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {d : G → ZMod 2}
    (hadd : ∀ x y : G, x ∈ P → y ∈ P → d (x * y) = d x + d y) (hz : ∀ z ∈ V, d z = 0)
    (h1 : d 1 = 0) (hg0 : d t0 = 0) (hg1 : d t1 = 0) (hw0 : d w0 = 0) (hw1 : d w1 = 0) :
    ∀ x ∈ P, d x = 0 := by
  have hsect : ∀ c : Vec4, d (sectMap t0 t1 w0 w1 c) = 0 := by
    intro c
    have m0 : (if c 0 = 0 then (1 : G) else t0) ∈ P := ite_one_mem (S.hFP S.ht0) (c 0)
    have m1 : (if c 1 = 0 then (1 : G) else t1) ∈ P := ite_one_mem (S.hFP S.ht1) (c 1)
    have m2 : (if c 2 = 0 then (1 : G) else w0) ∈ P := ite_one_mem S.w0P (c 2)
    have m3 : (if c 3 = 0 then (1 : G) else w1) ∈ P := ite_one_mem S.w1P (c 3)
    unfold sectMap
    rw [hadd _ _ (P.mul_mem (P.mul_mem m0 m1) m2) m3, hadd _ _ (P.mul_mem m0 m1) m2,
      hadd _ _ m0 m1, ite_vanish h1 hg0 (c 0), ite_vanish h1 hg1 (c 1),
      ite_vanish h1 hw0 (c 2), ite_vanish h1 hw1 (c 3)] <;> simp
  intro x hx
  obtain ⟨z, hzV, hxz⟩ := normal_form S hx
  rw [hxz, hadd _ _ (sectMap_mem S _) (S.hVP hzV), hsect, hz z hzV, zero_add]

theorem comBit_eq_coord {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    comBit x y = bf (coordMap t0 t1 w0 w1 x) (coordMap t0 t1 w0 w1 y) := by
  have key : ∀ p ∈ P,
      comBit p y + bf (coordMap t0 t1 w0 w1 p) (coordMap t0 t1 w0 w1 y) = 0 := by
    refine vanish_of_additive S (d := fun p => comBit p y +
      bf (coordMap t0 t1 w0 w1 p) (coordMap t0 t1 w0 w1 y)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro p q hp hq
      show comBit (p * q) y + bf (coordMap t0 t1 w0 w1 (p * q)) (coordMap t0 t1 w0 w1 y) =
        (comBit p y + bf (coordMap t0 t1 w0 w1 p) (coordMap t0 t1 w0 w1 y)) +
          (comBit q y + bf (coordMap t0 t1 w0 w1 q) (coordMap t0 t1 w0 w1 y))
      rw [comBit_mul_left S.toCoordSetup hp hq hy, coordMap_mul S hp hq, bf_add_left']
      ring
    · intro z hz
      show comBit z y + bf (coordMap t0 t1 w0 w1 z) (coordMap t0 t1 w0 w1 y) = 0
      rw [comBit_central_left S.toCoordSetup hz hy, coordMap_V S hz]
      simp [bf]
    · show comBit 1 y + bf (coordMap t0 t1 w0 w1 1) (coordMap t0 t1 w0 w1 y) = 0
      rw [comBit_one_left, coordMap_one]
      simp [bf]
    · show comBit t0 y + bf (coordMap t0 t1 w0 w1 t0) (coordMap t0 t1 w0 w1 y) = 0
      rw [coordMap_t0 S]
      simp [bf, e0, coordMap, zmod2_add_self]
    · show comBit t1 y + bf (coordMap t0 t1 w0 w1 t1) (coordMap t0 t1 w0 w1 y) = 0
      rw [coordMap_t1 S]
      simp [bf, e1, coordMap, zmod2_add_self]
    · show comBit w0 y + bf (coordMap t0 t1 w0 w1 w0) (coordMap t0 t1 w0 w1 y) = 0
      rw [coordMap_w0 S]
      simp [bf, e2, coordMap, zmod2_add_self]
    · show comBit w1 y + bf (coordMap t0 t1 w0 w1 w1) (coordMap t0 t1 w0 w1 y) = 0
      rw [coordMap_w1 S]
      simp [bf, e3, coordMap, zmod2_add_self]
  exact zmod2_eq_of_add_eq_zero _ _ (key x hx)

theorem sqBit_eq_coord {P V F : Subgroup G} {a t0 t1 w0 w1 : G}
    (S : CoordFrame P V F a t0 t1 w0 w1) {x : G} (hx : x ∈ P) :
    sqBit x = qf (coordMap t0 t1 w0 w1 x) := by
  have key : ∀ p ∈ P, sqBit p + qf (coordMap t0 t1 w0 w1 p) = 0 := by
    refine vanish_of_additive S (d := fun p => sqBit p + qf (coordMap t0 t1 w0 w1 p))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro p q hp hq
      show sqBit (p * q) + qf (coordMap t0 t1 w0 w1 (p * q)) =
        (sqBit p + qf (coordMap t0 t1 w0 w1 p)) + (sqBit q + qf (coordMap t0 t1 w0 w1 q))
      rw [sqBit_mul S.toCoordSetup hp hq, coordMap_mul S hp hq, qf_add,
        comBit_eq_coord S hp hq]
      linear_combination (bf (coordMap t0 t1 w0 w1 p) (coordMap t0 t1 w0 w1 q)) *
        two_eq_zero_zmod2
    · intro z hz
      show sqBit z + qf (coordMap t0 t1 w0 w1 z) = 0
      rw [sqBit_central S.toCoordSetup hz, coordMap_V S hz]
      simp [qf]
    · show sqBit 1 + qf (coordMap t0 t1 w0 w1 1) = 0
      rw [sqBit_one, coordMap_one]
      simp [qf]
    · show sqBit t0 + qf (coordMap t0 t1 w0 w1 t0) = 0
      rw [sqBit_F S.toCoordSetup S.ht0, coordMap_t0 S]
      simp [qf, e0]
    · show sqBit t1 + qf (coordMap t0 t1 w0 w1 t1) = 0
      rw [sqBit_F S.toCoordSetup S.ht1, coordMap_t1 S]
      simp [qf, e1]
    · show sqBit w0 + qf (coordMap t0 t1 w0 w1 w0) = 0
      rw [S.sw0, coordMap_w0 S]
      simp [qf, e2]
    · show sqBit w1 + qf (coordMap t0 t1 w0 w1 w1) = 0
      rw [S.sw1, coordMap_w1 S]
      simp [qf, e3]
  exact zmod2_eq_of_add_eq_zero _ _ (key x hx)

end Helpers

theorem exists_coords {G : Type} [Group G] (P V F : Subgroup G) (a t0 t1 : G)
    (hVP : V ≤ P) (hFP : F ≤ P) (ha : a ∈ V) (ha1 : a ≠ 1)
    (hP : Nat.card P = 64) (hV : Nat.card V = 4)
    (hVc : ∀ z ∈ V, ∀ p ∈ P, z * p = p * z)
    (hcV : ∀ p ∈ P, (∀ q ∈ P, p * q = q * p) → p ∈ V)
    (hVsq : ∀ z ∈ V, z * z = 1)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = a)
    (hsq : ∀ p ∈ P, p * p = 1 ∨ p * p = a)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) (hFsq : ∀ f ∈ F, f * f = 1)
    (ht0 : t0 ∈ F) (ht1 : t1 ∈ F) (hind : ∀ z ∈ V, z ≠ t0 ∧ z ≠ t1 ∧ z ≠ t0 * t1) :
    ∃ θ : P → Vec4, PCoords P V θ ∧ (∀ p : P, (p : G) ∈ F → inFt (θ p)) ∧
      (∀ x, inFt x → ∃ p : P, (p : G) ∈ F ∧ θ p = x) ∧
      θ ⟨t0, hFP ht0⟩ = e0 ∧ θ ⟨t1, hFP ht1⟩ = e1 := by
  obtain ⟨w0, w1, S⟩ := exists_frame
    (⟨hVP, hFP, hP, hV, ha, ha1, hVc, hcV, hVsq, hcomm, hsq, hFc, hFsq, ht0, ht1, hind⟩ :
      CoordSetup P V F a t0 t1)
  refine ⟨fun p => coordMap t0 t1 w0 w1 (p : G), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q
      show coordMap t0 t1 w0 w1 ((p * q : P) : G) =
        coordMap t0 t1 w0 w1 (p : G) + coordMap t0 t1 w0 w1 (q : G)
      rw [Subgroup.coe_mul]
      exact coordMap_mul S p.2 q.2
    · intro c
      exact ⟨⟨sectMap t0 t1 w0 w1 c, sectMap_mem S c⟩, coordMap_sect S c⟩
    · intro p
      exact ⟨fun h => (coordMap_eq_zero_iff S p.2).mp h, fun h => coordMap_V S h⟩
    · intro p q
      show ⁅(p : G), (q : G)⁆ = 1 ↔
        bf (coordMap t0 t1 w0 w1 (p : G)) (coordMap t0 t1 w0 w1 (q : G)) = 0
      rw [← comBit_eq_zero_iff, comBit_eq_coord S p.2 q.2]
    · intro p
      show (p : G) * (p : G) = 1 ↔ qf (coordMap t0 t1 w0 w1 (p : G)) = 0
      rw [← sqBit_eq_zero_iff, sqBit_eq_coord S p.2]
  · intro p hp
    show coordMap t0 t1 w0 w1 (p : G) 2 = 0 ∧ coordMap t0 t1 w0 w1 (p : G) 3 = 0
    exact ⟨comBit_F S.toCoordSetup S.ht0 hp, comBit_F S.toCoordSetup S.ht1 hp⟩
  · intro x hx
    have hx' : x 2 = 0 ∧ x 3 = 0 := hx
    obtain ⟨hx2, hx3⟩ := hx'
    refine ⟨⟨sectMap t0 t1 w0 w1 x, sectMap_mem S x⟩, ?_, coordMap_sect S x⟩
    show sectMap t0 t1 w0 w1 x ∈ F
    unfold sectMap
    rw [if_pos hx2, if_pos hx3, mul_one, mul_one]
    exact F.mul_mem (ite_one_mem S.ht0 (x 0)) (ite_one_mem S.ht1 (x 1))
  · exact coordMap_t0 S
  · exact coordMap_t1 S

end Part2

end CFSG.RankThree.GF2n.Tim79a.TwoSpace
