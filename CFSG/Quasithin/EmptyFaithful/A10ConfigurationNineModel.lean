module

import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def t0Pred (w : Wc) : Bool :=
  dList.contains w.a && dList.contains w.b && (vList.contains (w.a⁻¹ * w.b) == !w.e)

theorem t0Pred_mul : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool, ∀ a' ∈ dList, ∀ b' ∈ dList,
    ∀ e' : Bool, t0Pred ⟨a, b, e⟩ = true → t0Pred ⟨a', b', e'⟩ = true →
      t0Pred ((⟨a, b, e⟩ : Wc) * ⟨a', b', e'⟩) = true := by decide +kernel

theorem t0Pred_inv : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool, t0Pred ⟨a, b, e⟩ = true →
    t0Pred (⟨a, b, e⟩ : Wc)⁻¹ = true := by decide +kernel

theorem mem_dList_of_t0Pred {w : Wc} (h : t0Pred w = true) : w.a ∈ dList ∧ w.b ∈ dList := by
  simp only [t0Pred, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1.1, by simpa using h.1.2⟩

def T0h : Subgroup Wc where
  carrier := {w | t0Pred w = true}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨a, b, e⟩ ⟨a', b', e'⟩ ha hb
    obtain ⟨ha1, ha2⟩ := mem_dList_of_t0Pred ha
    obtain ⟨hb1, hb2⟩ := mem_dList_of_t0Pred hb
    exact t0Pred_mul a ha1 b ha2 e a' hb1 b' hb2 e' ha hb
  inv_mem' := by
    rintro ⟨a, b, e⟩ ha
    obtain ⟨ha1, ha2⟩ := mem_dList_of_t0Pred ha
    exact t0Pred_inv a ha1 b ha2 e ha

theorem mem_T0h {w : Wc} : w ∈ T0h ↔ t0Pred w = true := Iff.rfl

instance : DecidablePred (· ∈ T0h) := fun x => decidable_of_iff (t0Pred x = true) mem_T0h.symm

theorem forall_mem_T0h {P : Wc → Prop}
    (h : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool, (⟨a, b, e⟩ : Wc) ∈ T0h → P ⟨a, b, e⟩) :
    ∀ x ∈ T0h, P x := by
  rintro ⟨a, b, e⟩ hx
  obtain ⟨ha, hb⟩ := mem_dList_of_t0Pred hx
  exact h a ha b hb e hx

theorem T0h_le_Th : T0h ≤ Th := by
  intro w hw
  obtain ⟨ha, hb⟩ := mem_dList_of_t0Pred hw
  exact ⟨mem_D.2 ha, mem_D.2 hb⟩

theorem Th_conj_T0h : ∀ h ∈ Th, ∀ k ∈ T0h, h * k * h⁻¹ ∈ T0h :=
  forall_mem_Th fun a ha b hb e => forall_mem_T0h fun a' ha' b' hb' e' => by
    revert a ha b hb e a' ha' b' hb' e'
    decide +kernel

theorem mul_mem_T0h_of_not_mem : ∀ x ∈ Th, ∀ y ∈ Th, x ∉ T0h → y ∉ T0h → x * y ∈ T0h :=
  forall_mem_Th fun a ha b hb e => forall_mem_Th fun a' ha' b' hb' e' => by
    revert a ha b hb e a' ha' b' hb' e'
    decide +kernel

theorem commutator_Th_le_T0h : ⁅Th, Th⁆ ≤ T0h := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  by_cases hxK : x ∈ T0h
  · have h1 : y * x⁻¹ * y⁻¹ ∈ T0h := Th_conj_T0h y hy x⁻¹ (T0h.inv_mem hxK)
    have := T0h.mul_mem hxK h1
    simpa [mul_assoc] using this
  · by_cases hyK : y ∈ T0h
    · have h1 : x * y * x⁻¹ ∈ T0h := Th_conj_T0h x hx y hyK
      have := T0h.mul_mem h1 (T0h.inv_mem hyK)
      simpa [mul_assoc] using this
    · have h1 : x * y ∈ T0h := mul_mem_T0h_of_not_mem x hx y hy hxK hyK
      have h2 : y * x ∈ T0h := mul_mem_T0h_of_not_mem y hy x hx hyK hxK
      have := T0h.mul_mem h1 (T0h.inv_mem h2)
      simpa [mul_assoc] using this

theorem T0h_involution : ∀ w ∈ T0h, w ≠ 1 → w * w = 1 →
    D1 w = true ∨ D2 w = true ∨ D4 w = true :=
  forall_mem_T0h fun a ha b hb e => by
    revert a ha b hb e
    decide +kernel

theorem B_decomp : ∀ w : Wc, w ∈ A2 →
    w = 1 ∨ w = z0 ∨ D2 w = true ∨ D4 w = true ∨ D3 w = true ∨ D5 w = true := by
  decide +kernel

theorem exists_order_three_model : ∃ w : Wc, w ^ 3 = 1 ∧ w ≠ 1 :=
  ⟨⟨c3, 1, false⟩, by decide +kernel, by decide +kernel⟩

theorem u4_mem_A2 : u4 ∈ A2 := by decide +kernel

theorem D4_u4 : D4 u4 = true := by decide +kernel

theorem u3_mem_A2 : u3 ∈ A2 := by decide +kernel
theorem D3_u3 : D3 u3 = true := by decide +kernel
theorem u3_ne_one : u3 ≠ 1 := by decide +kernel
theorem u3_sq : u3 * u3 = 1 := by decide +kernel
theorem u3_ne_z0 : u3 ≠ z0 := by decide +kernel
theorem D2_u3 : D2 u3 = false := by decide +kernel
theorem D4_u3 : D4 u3 = false := by decide +kernel
theorem u5_mem_A2 : u5 ∈ A2 := by decide +kernel
theorem D5_u5 : D5 u5 = true := by decide +kernel

def Yset (a b : Bool) : Finset Wc :=
  Finset.univ.filter fun w =>
    w = z0 ∨ (a = true ∧ w ∈ A2 ∧ D3 w = true) ∨ (b = true ∧ w ∈ A2 ∧ D5 w = true)

theorem card_Yset (a b : Bool) : (Yset a b).card = 1 + 4 * a.toNat + 4 * b.toNat := by
  cases a <;> cases b <;> decide +kernel

theorem mem_Yset {a b : Bool} {w : Wc} : w ∈ Yset a b ↔
    w = z0 ∨ (a = true ∧ w ∈ A2 ∧ D3 w = true) ∨ (b = true ∧ w ∈ A2 ∧ D5 w = true) := by
  simp [Yset]

theorem zset_classify (P : Wc → Prop) (h1 : P z0) (h2 : ∀ w, P w → w ∈ A2)
    (h3 : ∀ w, P w → w ≠ 1 ∧ D2 w = false ∧ D4 w = false)
    (h4 : ∀ w, P w → ∀ v ∈ Th, P (v⁻¹ * w * v)) :
    ∃ a b : Bool, (∀ w, P w ↔ w ∈ Yset a b) ∧ (a = true ↔ P u3) ∧ (b = true ↔ P u5) := by
  classical
  refine ⟨decide (P u3), decide (P u5), ?_, by simp, by simp⟩
  intro w
  rw [mem_Yset]
  constructor
  · intro hw
    obtain ⟨hw1, hw2, hw4⟩ := h3 w hw
    rcases B_decomp w (h2 w hw) with h | h | h | h | h | h
    · exact absurd h hw1
    · exact Or.inl h
    · rw [hw2] at h
      exact absurd h (by decide)
    · rw [hw4] at h
      exact absurd h (by decide)
    · right
      left
      refine ⟨?_, h2 w hw, h⟩
      obtain ⟨v, hv, hvw⟩ := B_orbit_D3 w (h2 w hw) h u3 u3_mem_A2 D3_u3
      have : P u3 := by
        rw [← hvw]
        exact h4 w hw v hv
      simpa using this
    · right
      right
      refine ⟨?_, h2 w hw, h⟩
      obtain ⟨v, hv, hvw⟩ := B_orbit_D5 w (h2 w hw) h u5 u5_mem_A2 D5_u5
      have : P u5 := by
        rw [← hvw]
        exact h4 w hw v hv
      simpa using this
  · rintro (h | ⟨ha, hwA, hD⟩ | ⟨hb, hwA, hD⟩)
    · rw [h]
      exact h1
    · have hPu3 : P u3 := by simpa using ha
      obtain ⟨v, hv, hvw⟩ := B_orbit_D3 u3 u3_mem_A2 D3_u3 w hwA hD
      rw [← hvw]
      exact h4 u3 hPu3 v hv
    · have hPu5 : P u5 := by simpa using hb
      obtain ⟨v, hv, hvw⟩ := B_orbit_D5 u5 u5_mem_A2 D5_u5 w hwA hD
      rw [← hvw]
      exact h4 u5 hPu5 v hv

end CFSG.Quasithin.A10
