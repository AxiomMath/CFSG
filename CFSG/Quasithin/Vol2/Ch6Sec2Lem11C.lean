module

public import CFSG.Quasithin.H13.U3L14K

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section Transv

variable {E : Type*} [CommGroup E]

@[expose] def IsTransvCh611 (x : E) (a : MulAut E) : Prop :=
  ∀ u : E, a u * u⁻¹ = 1 ∨ a u * u⁻¹ = x

theorem IsTransvCh611.cases {x : E} {a : MulAut E} (ha : IsTransvCh611 x a) (u : E) :
    a u = u ∨ a u = u * x := by
  rcases ha u with h | h
  · left
    exact mul_inv_eq_one.mp h
  · right
    rw [← h, mul_comm (a u) u⁻¹, mul_inv_cancel_left]

theorem IsTransvCh611.apply_center (hE : ∀ u : E, u ^ 2 = 1) {x : E} (hx : x ≠ 1)
    {a : MulAut E} (ha : IsTransvCh611 x a) : a x = x := by
  rcases ha.cases x with h | h
  · exact h
  · exfalso
    apply hx
    have h1 : a x = 1 := by rw [h, ← pow_two, hE]
    exact a.injective (h1.trans (map_one a).symm)

theorem IsTransvCh611.mul_fix_iff (hE : ∀ u : E, u ^ 2 = 1) {x : E} (hx : x ≠ 1)
    {a : MulAut E} (ha : IsTransvCh611 x a) (u v : E) :
    a (u * v) = u * v ↔ (a u = u ↔ a v = v) := by
  have hne : ∀ w : E, w * x ≠ w := fun w h => hx (by simpa using h)
  have hxx : x * x = 1 := by rw [← pow_two, hE]
  rw [map_mul]
  rcases ha.cases u with hu | hu <;> rcases ha.cases v with hv | hv
  · simp [hu, hv]
  · rw [hu, hv]
    constructor
    · intro h
      exact absurd (by simpa [mul_assoc] using h) (hne v)
    · intro h
      exact absurd (h.mp rfl) (hne v)
  · rw [hu, hv]
    constructor
    · intro h
      have : u * x * v = u * v := h
      exact absurd (by rw [mul_right_comm] at this; simpa using this) (hne u)
    · intro h
      exact absurd (h.mpr rfl) (hne u)
  · rw [hu, hv]
    constructor
    · intro _
      exact ⟨fun h => absurd h (hne u), fun h => absurd h (hne v)⟩
    · intro _
      calc u * x * (v * x) = u * v * (x * x) := by rw [mul_mul_mul_comm]
        _ = u * v := by rw [hxx, mul_one]

theorem IsTransvCh611.eq_of_fix_iff {x : E} {a b : MulAut E} (ha : IsTransvCh611 x a)
    (hb : IsTransvCh611 x b) (hab : ∀ u, a u = u ↔ b u = u) : a = b := by
  ext u
  rcases ha.cases u with h1 | h1
  · rw [h1, (hab u).mp h1]
  · rcases hb.cases u with h2 | h2
    · rw [(hab u).mpr h2, h2]
    · rw [h1, h2]

theorem exists_conj_transv_ch611 (hE : ∀ u : E, u ^ 2 = 1) {x : E} (hx : x ≠ 1)
    {a b : MulAut E} (ha : IsTransvCh611 x a) (hb : IsTransvCh611 x b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ φ : MulAut E, φ x = x ∧ φ * a * φ⁻¹ = b := by
  classical
  by_cases hab : ∀ u, a u = u ↔ b u = u
  · exact ⟨1, rfl, by rw [one_mul, inv_one, mul_one]; exact ha.eq_of_fix_iff hb hab⟩
  push Not at hab
  obtain ⟨u₀, hu₀⟩ := hab
  have hma := ha.mul_fix_iff hE hx
  have hmb := hb.mul_fix_iff hE hx
  obtain ⟨u₁, hu₁⟩ : ∃ u, a u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact ha1 (MulEquiv.ext hcon)
  obtain ⟨u₂, hu₂⟩ : ∃ u, b u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hb1 (MulEquiv.ext hcon)
  obtain ⟨c, hca, hcb⟩ : ∃ c, a c ≠ c ∧ b c ≠ c := by
    rcases hu₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases h3 : b u₁ = u₁
      · refine ⟨u₀ * u₁, ?_, ?_⟩
        · rw [Ne, hma]; tauto
        · rw [Ne, hmb]; tauto
      · exact ⟨u₁, hu₁, h3⟩
    · by_cases h3 : a u₂ = u₂
      · refine ⟨u₀ * u₂, ?_, ?_⟩
        · rw [Ne, hma]; tauto
        · rw [Ne, hmb]; tauto
      · exact ⟨u₂, h3, hu₂⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : E → Prop, ∀ u, μ u ↔ ¬ (a u = u ↔ b u = u) := ⟨_, fun _ => Iff.rfl⟩
  have hμmul : ∀ u v, μ (u * v) ↔ ¬ (μ u ↔ μ v) := by
    intro u v
    rw [hμ, hμ, hμ, hma, hmb]
    tauto
  have hμc : ¬ μ c := by
    rw [hμ]
    tauto
  have hcc : c * c = 1 := by rw [← pow_two, hE]
  obtain ⟨f, hf1, hf0⟩ : ∃ f : E → E, (∀ u, μ u → f u = u * c) ∧ (∀ u, ¬ μ u → f u = u) :=
    ⟨fun u => if μ u then u * c else u, fun u hu => if_pos hu, fun u hu => if_neg hu⟩
  have hff : ∀ u, f (f u) = u := by
    intro u
    by_cases hu : μ u
    · have h1 : μ (u * c) := by rw [hμmul]; tauto
      rw [hf1 u hu, hf1 _ h1, mul_assoc, hcc, mul_one]
    · rw [hf0 u hu, hf0 u hu]
  have hfmul : ∀ u v, f (u * v) = f u * f v := by
    intro u v
    by_cases hu : μ u <;> by_cases hv : μ v
    · have h1 : ¬ μ (u * v) := by rw [hμmul]; tauto
      rw [hf0 _ h1, hf1 u hu, hf1 v hv]
      calc u * v = u * v * (c * c) := by rw [hcc, mul_one]
        _ = u * c * (v * c) := by rw [mul_mul_mul_comm]
    · have h1 : μ (u * v) := by rw [hμmul]; tauto
      rw [hf1 _ h1, hf1 u hu, hf0 v hv, mul_right_comm]
    · have h1 : μ (u * v) := by rw [hμmul]; tauto
      rw [hf1 _ h1, hf0 u hu, hf1 v hv, mul_assoc]
    · have h1 : ¬ μ (u * v) := by rw [hμmul]; tauto
      rw [hf0 _ h1, hf0 u hu, hf0 v hv]
  let φ : MulAut E :=
    { toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      map_mul' := hfmul }
  have hφapp : ∀ u, φ u = f u := fun _ => rfl
  have hφx : φ x = x := by
    have h1 : ¬ μ x := by
      rw [hμ, ha.apply_center hE hx, hb.apply_center hE hx]
      tauto
    rw [hφapp, hf0 x h1]
  refine ⟨φ, hφx, ?_⟩
  have hφinv : φ⁻¹ = φ := by
    ext u
    show f u = f u
    rfl
  rw [hφinv]
  ext u
  rw [MulAut.mul_apply, MulAut.mul_apply, hφapp, hφapp]
  have hfix : a (f u) = f u ↔ b u = u := by
    by_cases hu : μ u
    · rw [hf1 u hu, hma]
      rw [hμ] at hu
      tauto
    · rw [hf0 u hu]
      rw [hμ] at hu
      tauto
  rcases ha.cases (f u) with h1 | h1
  · rw [h1, hff, (hfix.mp h1)]
  · rcases hb.cases u with h2 | h2
    · exact absurd (hfix.mpr h2) (by rw [h1]; intro h3; exact hx (by simpa using h3))
    · rw [h1, hfmul, hff, h2, ← hφapp, hφx]

end Transv

end CFSG.Quasithin.H13
