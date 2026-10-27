module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerFixed
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerConfig

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

namespace TwE6Per


variable {k : Type} [Field k]

@[expose] def InSlot (μ : kˣ) (x : e6Data_valid.minGroup k) : Fin 4 → Prop :=
  ![x ∈ rankOne k vb1, x ∈ rankOne k vb2, x ∈ rankOne k vb3,
    x = torusHom k (uOne μ) ∨ x = torusHom k (uTwo μ)]

theorem commute_of_slot (μ : kˣ) {x y : e6Data_valid.minGroup k} {s t : Fin 4}
    (hx : InSlot μ x s) (hy : InSlot μ y t) (h : s ≠ t ∨ (s = 3 ∧ t = 3)) : Commute x y := by
  have tor : ∀ {z w : e6Data_valid.minGroup k} {γ : Fin (Tag.rank .E6) → ℤ},
      (γ = vb1 ∨ γ = vb2 ∨ γ = vb3) → z ∈ rankOne k γ →
        (w = torusHom k (uOne μ) ∨ w = torusHom k (uTwo μ)) → Commute z w := by
    intro z w γ hγ hz hw
    rcases hw with rfl | rfl
    · exact (commute_torus_rankOne μ (Or.inl rfl) hγ hz).symm
    · exact (commute_torus_rankOne μ (Or.inr rfl) hγ hz).symm
  fin_cases s <;> fin_cases t
  · exact absurd h (by decide)
  · exact commute_rankOne_12 hx hy
  · exact commute_rankOne_13 hx hy
  · exact tor (Or.inl rfl) hx hy
  · exact (commute_rankOne_12 hy hx).symm
  · exact absurd h (by decide)
  · exact commute_rankOne_23 hx hy
  · exact tor (Or.inr (Or.inl rfl)) hx hy
  · exact (commute_rankOne_13 hy hx).symm
  · exact (commute_rankOne_23 hy hx).symm
  · exact absurd h (by decide)
  · exact tor (Or.inr (Or.inr rfl)) hx hy
  · exact (tor (Or.inl rfl) hy hx).symm
  · exact (tor (Or.inr (Or.inl rfl)) hy hx).symm
  · exact (tor (Or.inr (Or.inr rfl)) hy hx).symm
  · change x = torusHom k (uOne μ) ∨ x = torusHom k (uTwo μ) at hx
    change y = torusHom k (uOne μ) ∨ y = torusHom k (uTwo μ) at hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      exact (Commute.all _ _).map (torusHom k)

section Config

variable [CharP k 2] {θ : k →+* k} (hθ : ∀ c, θ (θ c) = c) (μ : kˣ)
  (hθμ : Units.map (θ : k →* k) μ = μ⁻¹)

abbrev slotOf : Fin 5 → Fin 4 := ![0, 1, 2, 3, 3]

@[expose] noncomputable def bU : Fin 5 → fixedGroup k θ :=
  ![uS1 μ hθμ, uS2 μ hθμ, uS3 μ hθμ, uT1 hθ μ hθμ, uT2 hθ μ hθμ]

variable (θ) in
@[expose] noncomputable def wU : Fin 5 → fixedGroup k θ :=
  ![uW1 θ, uW2 θ, uW3 θ, uM1 θ, uM2 θ]

theorem slot_bU (i : Fin 5) :
    InSlot μ ((bU hθ μ hθμ i : fixedGroup k θ) : e6Data_valid.minGroup k) (slotOf i) := by
  fin_cases i
  · exact val_S1_mem μ hθμ
  · exact val_S2_mem μ hθμ
  · exact val_S3_mem μ hθμ
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem slot_wU (i : Fin 5) (hi : i.val < 3) :
    InSlot μ ((wU θ i : fixedGroup k θ) : e6Data_valid.minGroup k) (slotOf i) := by
  fin_cases i
  · exact val_W1_mem (θ := θ)
  · exact val_W2_mem (θ := θ)
  · exact val_W3_mem (θ := θ)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)

theorem slot_cond :
    ∀ i j : Fin 5, i ≠ j → (slotOf i ≠ slotOf j ∨ (slotOf i = 3 ∧ slotOf j = 3)) := by
  decide

theorem slot_cond' : ∀ i j : Fin 5, i.val < 3 → j ≠ i →
    (slotOf i ≠ slotOf j ∨ (slotOf i = 3 ∧ slotOf j = 3)) := by
  decide

omit [CharP k 2] in
theorem commute_U {x y : fixedGroup k θ} {s t : Fin 4}
    (hx : InSlot μ (x : e6Data_valid.minGroup k) s) (hy : InSlot μ (y : e6Data_valid.minGroup k) t)
    (h : s ≠ t ∨ (s = 3 ∧ t = 3)) : Commute x y :=
  Subtype.ext (commute_of_slot μ hx hy h).eq

theorem bU_comm (i j : Fin 5) : Commute (bU hθ μ hθμ i) (bU hθ μ hθμ j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · exact commute_U μ (slot_bU hθ μ hθμ i) (slot_bU hθ μ hθμ j) (slot_cond i j hij)

theorem wU_comm (i j : Fin 5) (hi : i.val < 3) (hj : j ≠ i) :
    wU θ i * bU hθ μ hθμ j * (wU θ i)⁻¹ = bU hθ μ hθμ j := by
  rw [(commute_U μ (slot_wU μ i hi) (slot_bU hθ μ hθμ j) (slot_cond' i j hi hj)).eq,
    mul_inv_cancel_right]

omit
  [CharP k 2] in
theorem conj_conj_inv {G : Type*} [Group G] {M a b : G} (h : a * b * a⁻¹ = b⁻¹) :
    (M * a * M⁻¹) * (M * b * M⁻¹) * (M * a * M⁻¹)⁻¹ = (M * b * M⁻¹)⁻¹ := by
  rw [show (M * a * M⁻¹) * (M * b * M⁻¹) * (M * a * M⁻¹)⁻¹ = M * (a * b * a⁻¹) * M⁻¹ by group, h]
  group

theorem wU_inv (i : Fin 5) :
    wU θ i * bU hθ μ hθμ i * (wU θ i)⁻¹ = (bU hθ μ hθμ i)⁻¹ := by
  have h3 : uW3 θ * uS3 μ hθμ * (uW3 θ)⁻¹ = (uS3 μ hθμ)⁻¹ :=
    Subtype.ext (nm_conj_sElt (nd 3) _)
  have h2 : uW2 θ * uS2 μ hθμ * (uW2 θ)⁻¹ = (uS2 μ hθμ)⁻¹ := conj_conj_inv h3
  fin_cases i
  · exact conj_conj_inv h2
  · exact h2
  · exact h3
  · exact Subtype.ext (conj_N1_t1 hθ hθμ)
  · exact Subtype.ext (conj_N2_t2 hθ hθμ)

omit [CharP k 2] in
theorem wU_34 : wU θ 3 * bU hθ μ hθμ 4 * (wU θ 3)⁻¹ = bU hθ μ hθμ 4 * bU hθ μ hθμ 3 :=
  Subtype.ext (conj_N1_t2 hθ hθμ)

omit [CharP k 2] in
theorem wU_43 : wU θ 4 * bU hθ μ hθμ 3 * (wU θ 4)⁻¹ = bU hθ μ hθμ 3 * bU hθ μ hθμ 4 :=
  Subtype.ext (conj_N2_t1 hθ hθμ)

end Config

end TwE6Per

end CFSG.StandardType
