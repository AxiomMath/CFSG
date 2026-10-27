module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.F53B3.NoE

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_eq_one_of_odd_pow {l e : G} {m : ℕ} (hm : Odd m) (hl : l ^ m = 1)
    (h2 : ⁅l, e⁆ * ⁅l, e⁆ = 1) (hc : l * ⁅l, e⁆ = ⁅l, e⁆ * l) : ⁅l, e⁆ = 1 := by
  obtain ⟨j, rfl⟩ := hm
  have hconj : l * ⁅l, e⁆ * l⁻¹ = ⁅l, e⁆ := by rw [hc]; group
  have hle : l * e * l⁻¹ = ⁅l, e⁆ * e := by simp only [commutatorElement_def]; group
  have key : ∀ k : ℕ, l ^ k * e * (l ^ k)⁻¹ = ⁅l, e⁆ ^ k * e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : l ^ (k + 1) * e * (l ^ (k + 1))⁻¹ = l * (l ^ k * e * (l ^ k)⁻¹) * l⁻¹ := by
        group
      have e2 : l * (⁅l, e⁆ ^ k * e) * l⁻¹ = (l * ⁅l, e⁆ * l⁻¹) ^ k * (l * e * l⁻¹) := by
        rw [conj_pow]; group
      rw [e1, ih, e2, hconj, hle, pow_succ]
      group
  have h1 := key (2 * j + 1)
  simp only [hl, inv_one, mul_one, one_mul] at h1
  have h3 : ⁅l, e⁆ ^ (2 * j + 1) = ⁅l, e⁆ := by
    rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  rw [h3] at h1
  simpa using h1.symm

structure PairBase (H E V Z : Subgroup G) : Prop where
  E_le : E ≤ H
  normE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E
  normV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V
  comm_V : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  central : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z
  sq_Z : ∀ z ∈ Z, z * z = 1

structure Pairing (H E V Z : Subgroup G) : Prop extends PairBase H E V Z where
  mem_Z : ∀ e ∈ E, ∀ v ∈ V, ⁅e, v⁆ ∈ Z

namespace PairBase

variable {H E V Z : Subgroup G} (h : PairBase H E V Z)

include h

theorem pair_mem_V {e v : G} (he : e ∈ E) (hv : v ∈ V) : ⁅e, v⁆ ∈ V := by
  rw [commutatorElement_def]
  exact V.mul_mem (h.normV e (h.E_le he) v hv) (V.inv_mem hv)

theorem pair_mul_right {e v v' : G} (he : e ∈ E) (hv : v ∈ V) (hv' : v' ∈ V) :
    ⁅e, v * v'⁆ = ⁅e, v⁆ * ⁅e, v'⁆ := by
  have h1 : v * ⁅e, v'⁆ = ⁅e, v'⁆ * v := h.comm_V v hv _ (h.pair_mem_V he hv')
  calc ⁅e, v * v'⁆ = ⁅e, v⁆ * (v * ⁅e, v'⁆ * v⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅e, v⁆ * ⁅e, v'⁆ := by rw [h1, mul_inv_cancel_right]

end PairBase

namespace Pairing

variable {H E V Z : Subgroup G} (h : Pairing H E V Z)

include h

theorem sq_pair {e v : G} (he : e ∈ E) (hv : v ∈ V) : ⁅e, v⁆ * ⁅e, v⁆ = 1 :=
  h.sq_Z _ (h.mem_Z e he v hv)

theorem pair_mul_left {e e' v : G} (he : e ∈ E) (he' : e' ∈ E) (hv : v ∈ V) :
    ⁅e * e', v⁆ = ⁅e', v⁆ * ⁅e, v⁆ := by
  have h1 : e * ⁅e', v⁆ * e⁻¹ = ⁅e', v⁆ :=
    h.central _ (h.mem_Z e' he' v hv) e (h.E_le he)
  calc ⁅e * e', v⁆ = (e * ⁅e', v⁆ * e⁻¹) * ⁅e, v⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅e', v⁆ * ⁅e, v⁆ := by rw [h1]

theorem pair_inv_right {e v : G} (he : e ∈ E) (hv : v ∈ V) : ⁅e, v⁻¹⁆ = ⁅e, v⁆ := by
  have h1 : ⁅e, v⁆ * ⁅e, v⁻¹⁆ = 1 := by
    rw [← h.toPairBase.pair_mul_right he hv (V.inv_mem hv), mul_inv_cancel]
    simp [commutatorElement_def]
  exact mul_left_cancel (h1.trans (h.sq_pair he hv).symm)

theorem pair_inv_left {e v : G} (he : e ∈ E) (hv : v ∈ V) : ⁅e⁻¹, v⁆ = ⁅e, v⁆ := by
  have h1 : ⁅e, v⁆ * ⁅e⁻¹, v⁆ = 1 := by
    rw [← h.pair_mul_left (E.inv_mem he) he hv, inv_mul_cancel]
    simp [commutatorElement_def]
  exact mul_left_cancel (h1.trans (h.sq_pair he hv).symm)

theorem pair_conj {g e v : G} (hg : g ∈ H) (he : e ∈ E) (hv : v ∈ V) :
    ⁅g * e * g⁻¹, g * v * g⁻¹⁆ = ⁅e, v⁆ := by
  have h1 : g * ⁅e, v⁆ * g⁻¹ = ⁅e, v⁆ := h.central _ (h.mem_Z e he v hv) g hg
  calc ⁅g * e * g⁻¹, g * v * g⁻¹⁆ = g * ⁅e, v⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅e, v⁆ := h1

theorem comm_comm_eq_one {C : Subgroup G} (hCV : C ≤ V) {e l c : G} (he : e ∈ E) (hl : l ∈ H)
    (hc : c ∈ C) (hlc : l * c * l⁻¹ = c) : ⁅⁅e, l⁆, c⁆ = 1 := by
  have hcV : c ∈ V := hCV hc
  have hle : l * e⁻¹ * l⁻¹ ∈ E := h.normE l hl _ (E.inv_mem he)
  have e1 : ⁅e, l⁆ = e * (l * e⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
  rw [e1, h.pair_mul_left he hle hcV]
  have e2 : ⁅l * e⁻¹ * l⁻¹, c⁆ = ⁅e, c⁆ := by
    calc ⁅l * e⁻¹ * l⁻¹, c⁆ = ⁅l * e⁻¹ * l⁻¹, l * c * l⁻¹⁆ := by rw [hlc]
      _ = ⁅e⁻¹, c⁆ := h.pair_conj hl (E.inv_mem he) hcV
      _ = ⁅e, c⁆ := h.pair_inv_left he hcV
  rw [e2]
  exact h.sq_pair he hcV

theorem key {C : Subgroup G} (hCV : C ≤ V) {d e w : G} (hd : d ∈ H) (he : e ∈ E) (hw : w ∈ V)
    (hC : ∀ c ∈ C, ⁅e, c⁆ = 1)
    (hmod : ∃ c ∈ C, (d * w * d⁻¹) * (d⁻¹ * w * d) = w⁻¹ * c) :
    ⁅⁅d, e⁆, ⁅d, w⁆⁆ = ⁅e, w⁆ := by
  obtain ⟨c, hcC, hcw⟩ := hmod
  have hdinv : d⁻¹ ∈ H := H.inv_mem hd
  have he' : d * e * d⁻¹ ∈ E := h.normE d hd e he
  have hw' : d * w * d⁻¹ ∈ V := h.normV d hd w hw
  have hw'' : d⁻¹ * w * d ∈ V := by simpa using h.normV d⁻¹ hdinv w hw
  have hwi : w⁻¹ ∈ V := V.inv_mem hw
  have hew : ⁅d, e⁆ = (d * e * d⁻¹) * e⁻¹ := rfl
  have hdw : ⁅d, w⁆ = (d * w * d⁻¹) * w⁻¹ := rfl
  have a1 : ⁅d * e * d⁻¹, d * w * d⁻¹⁆ = ⁅e, w⁆ := h.pair_conj hd he hw
  have a2 : ⁅d * e * d⁻¹, w⁻¹⁆ = ⁅e, d⁻¹ * w * d⁆ := by
    rw [h.pair_inv_right he' hw]
    have h3 := h.pair_conj hdinv he' hw
    have e3 : d⁻¹ * (d * e * d⁻¹) * d⁻¹⁻¹ = e := by group
    have e4 : d⁻¹ * w * d⁻¹⁻¹ = d⁻¹ * w * d := by rw [inv_inv]
    rw [e3, e4] at h3
    exact h3.symm
  have a3 : ⁅e⁻¹, d * w * d⁻¹⁆ = ⁅e, d * w * d⁻¹⁆ := h.pair_inv_left he hw'
  have a4 : ⁅e⁻¹, w⁻¹⁆ = ⁅e, w⁆ := by rw [h.pair_inv_left he hwi, h.pair_inv_right he hw]
  have hbc : ⁅e, d * w * d⁻¹⁆ * ⁅e, d⁻¹ * w * d⁆ = ⁅e, w⁆ := by
    rw [← h.toPairBase.pair_mul_right he hw' hw'', hcw,
      h.toPairBase.pair_mul_right he hwi (hCV hcC), h.pair_inv_right he hw, hC c hcC, mul_one]
  rw [hew, hdw, h.pair_mul_left he' (E.inv_mem he) (V.mul_mem hw' hwi),
    h.toPairBase.pair_mul_right (E.inv_mem he) hw' hwi,
    h.toPairBase.pair_mul_right he' hw' hwi, a1, a2, a3, a4]
  calc ⁅e, d * w * d⁻¹⁆ * ⁅e, w⁆ * (⁅e, w⁆ * ⁅e, d⁻¹ * w * d⁆)
      = ⁅e, d * w * d⁻¹⁆ * (⁅e, w⁆ * ⁅e, w⁆) * ⁅e, d⁻¹ * w * d⁆ := by simp only [mul_assoc]
    _ = ⁅e, d * w * d⁻¹⁆ * ⁅e, d⁻¹ * w * d⁆ := by rw [h.sq_pair he hw, mul_one]
    _ = ⁅e, w⁆ := hbc

end Pairing

theorem three_conj {d w w₁ w₂ w₃ : G} (h1 : d * w * d⁻¹ = w₁) (h2 : d * w₁ * d⁻¹ = w₂)
    (h3 : d * w₂ * d⁻¹ = w₃) (hu : (w₂ * w₁) * w⁻¹ = w⁻¹ * (w₂ * w₁)) :
    d * (w₂ * w₁ * w) * d⁻¹ * (w₂ * w₁ * w)⁻¹ = w₃ * w⁻¹ := by
  have e : d * (w₂ * w₁ * w) * d⁻¹ = (d * w₂ * d⁻¹) * (d * w₁ * d⁻¹) * (d * w * d⁻¹) := by group
  rw [e, h1, h2, h3]
  calc w₃ * w₂ * w₁ * (w₂ * w₁ * w)⁻¹ = w₃ * ((w₂ * w₁) * w⁻¹ * (w₂ * w₁)⁻¹) := by group
    _ = w₃ * w⁻¹ := by rw [hu]; group

theorem exists_mod {H V C : Subgroup G} {d : G} (hd : d ∈ H)
    (normV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) (normC : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C)
    (comm_V : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hfix : ∀ y ∈ V, d * y * d⁻¹ * y⁻¹ ∈ C → y ∈ C)
    (hcube : ∀ w ∈ V, d ^ 3 * w * (d ^ 3)⁻¹ * w⁻¹ ∈ C) {w : G} (hw : w ∈ V) :
    ∃ c ∈ C, (d * w * d⁻¹) * (d⁻¹ * w * d) = w⁻¹ * c := by
  have hdi : d⁻¹ ∈ H := H.inv_mem hd
  obtain ⟨w₁, hw₁d⟩ : ∃ w₁, d * w * d⁻¹ = w₁ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂d⟩ : ∃ w₂, d * w₁ * d⁻¹ = w₂ := ⟨_, rfl⟩
  obtain ⟨w₃, hw₃d⟩ : ∃ w₃, d * w₂ * d⁻¹ = w₃ := ⟨_, rfl⟩
  have hw₁ : w₁ ∈ V := hw₁d ▸ normV d hd w hw
  have hw₂ : w₂ ∈ V := hw₂d ▸ normV d hd w₁ hw₁
  have hw₃ : w₃ = d ^ 3 * w * (d ^ 3)⁻¹ := by
    rw [← hw₃d, ← hw₂d, ← hw₁d, pow_three']; group
  have hy : w₂ * w₁ * w ∈ V := V.mul_mem (V.mul_mem hw₂ hw₁) hw
  have hu : (w₂ * w₁) * w⁻¹ = w⁻¹ * (w₂ * w₁) :=
    comm_V _ (V.mul_mem hw₂ hw₁) _ (V.inv_mem hw)
  have hyc : d * (w₂ * w₁ * w) * d⁻¹ * (w₂ * w₁ * w)⁻¹ ∈ C := by
    rw [three_conj hw₁d hw₂d hw₃d hu, hw₃]
    exact hcube w hw
  have hyC : w₂ * w₁ * w ∈ C := hfix _ hy hyc
  refine ⟨d⁻¹ * (w₂ * w₁ * w) * d, by simpa using normC d⁻¹ hdi _ hyC, ?_⟩
  have hd2 : d⁻¹ * w₂ * d = w₁ := by rw [← hw₂d]; group
  have hd1 : d⁻¹ * w₁ * d = w := by rw [← hw₁d]; group
  have e : d⁻¹ * (w₂ * w₁ * w) * d = w₁ * w * (d⁻¹ * w * d) := by
    calc d⁻¹ * (w₂ * w₁ * w) * d = (d⁻¹ * w₂ * d) * (d⁻¹ * w₁ * d) * (d⁻¹ * w * d) := by group
      _ = w₁ * w * (d⁻¹ * w * d) := by rw [hd2, hd1]
  rw [e, hw₁d]
  have hcomm : w₁ * w = w * w₁ := comm_V _ hw₁ _ hw
  calc w₁ * (d⁻¹ * w * d) = (w⁻¹ * (w₁ * w)) * (d⁻¹ * w * d) := by rw [hcomm]; group
    _ = w⁻¹ * (w₁ * w * (d⁻¹ * w * d)) := by group

end CFSG.Quasithin.F53B3.NoE
