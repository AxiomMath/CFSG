module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def isTr (a : S4) : Bool := a ∈ trList
def isVn (a : S4) : Bool := a ∈ vnList
def isOne (a : S4) : Bool := a == 1

def D1 (x : Wc) : Bool := !x.e && isVn x.a && isVn x.b
def D2 (x : Wc) : Bool := !x.e && ((isVn x.a && isOne x.b) || (isOne x.a && isVn x.b))
def D3 (x : Wc) : Bool := !x.e && ((isTr x.a && isOne x.b) || (isOne x.a && isTr x.b))
def D4 (x : Wc) : Bool := !x.e && isTr x.a && isTr x.b
def D5 (x : Wc) : Bool := !x.e && ((isTr x.a && isVn x.b) || (isVn x.a && isTr x.b))
def D6 (x : Wc) : Bool := x.e && (x * x == 1)

def u3 : Wc := ⟨f1, 1, false⟩
def u4 : Wc := ⟨f1, f1, false⟩
def u5 : Wc := ⟨f1, tau, false⟩

theorem cls_iff {rep : Wc} {D : Wc → Bool} (h1 : ∀ w : Wc, D (w⁻¹ * rep * w) = true)
    (h2 : ∀ y : Wc, D y = true → ∃ w : Wc, w⁻¹ * rep * w = y) (y : Wc) :
    (∃ w : Wc, w⁻¹ * rep * w = y) ↔ D y = true :=
  ⟨fun ⟨w, hw⟩ => hw ▸ h1 w, h2 y⟩

theorem cls_z0 (y : Wc) : (∃ w : Wc, w⁻¹ * z0 * w = y) ↔ D1 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem cls_t0 (y : Wc) : (∃ w : Wc, w⁻¹ * t0 * w = y) ↔ D2 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem cls_u3 (y : Wc) : (∃ w : Wc, w⁻¹ * u3 * w = y) ↔ D3 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem cls_u4 (y : Wc) : (∃ w : Wc, w⁻¹ * u4 * w = y) ↔ D4 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem cls_u5 (y : Wc) : (∃ w : Wc, w⁻¹ * u5 * w = y) ↔ D5 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem cls_s0 (y : Wc) : (∃ w : Wc, w⁻¹ * s0 * w = y) ↔ D6 y = true :=
  cls_iff (by decide +kernel) (by decide +kernel) y

theorem involution_partition : ∀ x : Wc, x * x = 1 → x ≠ 1 →
    D1 x = true ∨ D2 x = true ∨ D3 x = true ∨ D4 x = true ∨ D5 x = true ∨ D6 x = true := by
  decide +kernel

theorem D_exclusive : ∀ x : Wc,
    (D1 x = true → D2 x = false ∧ D3 x = false ∧ D4 x = false ∧ D5 x = false ∧ D6 x = false) ∧
    (D2 x = true → D3 x = false ∧ D4 x = false ∧ D5 x = false ∧ D6 x = false) ∧
    (D3 x = true → D4 x = false ∧ D5 x = false ∧ D6 x = false) ∧
    (D4 x = true → D5 x = false ∧ D6 x = false) ∧ (D5 x = true → D6 x = false) := by
  decide +kernel

theorem D1_z0 : D1 z0 = true := by decide +kernel
theorem D6_s0 : D6 s0 = true := by decide +kernel
theorem not_D1_t0 : D1 t0 = false := by decide +kernel

theorem t0_not_conj_z0 : ¬ ∃ w : Wc, w⁻¹ * z0 * w = t0 := fun h => by
  have := (cls_z0 t0).1 h
  rw [not_D1_t0] at this
  exact Bool.noConfusion this

theorem B_D1 : ∀ x : Wc, x ∈ A2 → D1 x = true → x = z0 := by decide +kernel
theorem B_orbit_D3 : ∀ x : Wc, x ∈ A2 → D3 x = true → ∀ y : Wc, y ∈ A2 → D3 y = true →
    ∃ w : Wc, w ∈ Th ∧ w⁻¹ * x * w = y := by decide +kernel
theorem B_orbit_D4 : ∀ x : Wc, x ∈ A2 → D4 x = true → ∀ y : Wc, y ∈ A2 → D4 y = true →
    ∃ w : Wc, w ∈ Th ∧ w⁻¹ * x * w = y := by decide +kernel
theorem B_orbit_D5 : ∀ x : Wc, x ∈ A2 → D5 x = true → ∀ y : Wc, y ∈ A2 → D5 y = true →
    ∃ w : Wc, w ∈ Th ∧ w⁻¹ * x * w = y := by decide +kernel

theorem exists_three_central_of_conj {rep x : Wc}
    (hc : ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * rep = rep * c) (hx : ∃ w : Wc, w⁻¹ * rep * w = x) :
    ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * x = x * c := by
  obtain ⟨c, hc3, hc1, hcc⟩ := hc
  obtain ⟨w, rfl⟩ := hx
  refine ⟨w⁻¹ * c * w, ?_, ?_, ?_⟩
  · calc w⁻¹ * c * w * (w⁻¹ * c * w) * (w⁻¹ * c * w) = w⁻¹ * (c * c * c) * w := by group
      _ = 1 := by rw [hc3]; group
  · intro h
    apply hc1
    have : c = w * (w⁻¹ * c * w) * w⁻¹ := by group
    rw [this, h]
    group
  · calc w⁻¹ * c * w * (w⁻¹ * rep * w) = w⁻¹ * (c * rep) * w := by group
      _ = w⁻¹ * (rep * c) * w := by rw [hcc]
      _ = w⁻¹ * rep * w * (w⁻¹ * c * w) := by group

theorem exists_three_central_t0 : ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * t0 = t0 * c :=
  ⟨⟨1, c3, false⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exists_three_central_u3 : ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * u3 = u3 * c :=
  ⟨⟨1, c3, false⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem exists_three_central_s0 : ∃ c : Wc, c * c * c = 1 ∧ c ≠ 1 ∧ c * s0 = s0 * c :=
  ⟨⟨c3, c3, false⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem z0_mem_A1 : z0 ∈ A1 := by decide +kernel
theorem z0_mem_A2 : z0 ∈ A2 := by decide +kernel
theorem t0_mem_A1 : t0 ∈ A1 := by decide +kernel
theorem t0_mem_A2 : t0 ∈ A2 := by decide +kernel
theorem t0_mem_T1h : t0 ∈ T1h := by decide +kernel
theorem t0'_mem_T2h : t0' ∈ T2h := by decide +kernel
theorem z0_eq_mul : z0 = t0 * t0' := by decide +kernel
theorem t0'_eq_conj : t0' = s0⁻¹ * t0 * s0 := by decide +kernel
theorem t0_central_Jh : ∀ y ∈ Jh, y * t0 = t0 * y :=
  forall_mem_Jh fun a ha b hb => by revert a ha b hb; decide +kernel
theorem t0_sq : t0 * t0 = 1 := by decide +kernel
theorem s0_sq : s0 * s0 = 1 := by decide +kernel

theorem D4_into_B : ∀ w : Wc, D4 w = true → ∃ v : Wc, v⁻¹ * w * v ∈ A2 := by decide +kernel
theorem D5_into_B : ∀ w : Wc, D5 w = true → ∃ v : Wc, v⁻¹ * w * v ∈ A2 := by decide +kernel

theorem cls_conj_mem {rep : Wc} {D : Wc → Bool}
    (h : ∀ y, D y = true ↔ ∃ w : Wc, w⁻¹ * rep * w = y) {w : Wc} (hw : D w = true) (v : Wc) :
    D (v⁻¹ * w * v) = true := by
  obtain ⟨x, rfl⟩ := (h w).1 hw
  exact (h _).2 ⟨x * v, by group⟩

theorem D3_conj {w : Wc} (hw : D3 w = true) (v : Wc) : D3 (v⁻¹ * w * v) = true :=
  cls_conj_mem (fun y => (cls_u3 y).symm) hw v
theorem D4_conj {w : Wc} (hw : D4 w = true) (v : Wc) : D4 (v⁻¹ * w * v) = true :=
  cls_conj_mem (fun y => (cls_u4 y).symm) hw v
theorem D5_conj {w : Wc} (hw : D5 w = true) (v : Wc) : D5 (v⁻¹ * w * v) = true :=
  cls_conj_mem (fun y => (cls_u5 y).symm) hw v
theorem D6_not_mem_Jh {w : Wc} (hw : D6 w = true) : w ∉ Jh := by
  intro h
  have h1 : w.e = false := h.1
  have h2 : w.e = true := by
    simp only [D6, Bool.and_eq_true] at hw
    exact hw.1
  rw [h1] at h2
  exact Bool.noConfusion h2

theorem z0_ne_one : z0 ≠ 1 := by decide +kernel
theorem s0_ne_one : s0 ≠ 1 := by decide +kernel

def x3 : Wc := ⟨c3, 1, false⟩
theorem x3_cube : x3 ^ 3 = 1 := by decide +kernel
theorem x3_ne_one : x3 ≠ 1 := by decide +kernel

theorem card_Jh : Nat.card Jh = 64 := by
  rw [Jh, card_baseSub, card_D]

end CFSG.Quasithin.A10
