module

public import CFSG.Quasithin.Background.C124YLH6Lin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix

variable {K : Type} [Field K] [Finite K] (Γ₀ : Subgroup (GL (Fin 3) K))

@[expose] def mat (g : ↥Γ₀) : Matrix (Fin 3) (Fin 3) K :=
  ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

variable {Γ₀}

theorem mat_mul (g h : ↥Γ₀) : mat Γ₀ (g * h) = mat Γ₀ g * mat Γ₀ h := rfl

theorem mat_one : mat Γ₀ (1 : ↥Γ₀) = 1 := rfl

theorem mat_injective : Function.Injective (mat Γ₀) := fun _ _ e =>
  Subtype.ext (Units.ext e)

@[expose] def fixS (B : Subgroup ↥Γ₀) : Submodule K (Fin 3 → K) where
  carrier := {y | ∀ g ∈ B, (mat Γ₀ g).mulVec y = y}
  add_mem' := fun {a b} ha hb g hg => by rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun _ _ => by simp
  smul_mem' := fun c _ hy g hg => by rw [Matrix.mulVec_smul, hy g hg]

theorem mem_fixS {B : Subgroup ↥Γ₀} {y : Fin 3 → K} :
    y ∈ fixS B ↔ ∀ g ∈ B, (mat Γ₀ g).mulVec y = y := Iff.rfl

@[expose] def stabS (W : Submodule K (Fin 3 → K)) : Subgroup ↥Γ₀ where
  carrier := {g | ∀ y ∈ W, (mat Γ₀ g).mulVec y = y}
  one_mem' := fun _ _ => by simp [mat_one]
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    have h := ha y hy
    have h2 : (mat Γ₀ a⁻¹).mulVec ((mat Γ₀ a).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]
    rwa [h] at h2

theorem le_stabS_fixS (B : Subgroup ↥Γ₀) : B ≤ stabS (fixS B) := fun g hg _ hy => hy g hg

theorem eq_one_of_mulVec {g : ↥Γ₀} (h : ∀ y, (mat Γ₀ g).mulVec y = y) : g = 1 := by
  apply mat_injective
  rw [mat_one]
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem card_fixS_le (hK : Nat.card K = 4) {B : Subgroup ↥Γ₀} (hB : B ≠ ⊥) :
    Nat.card (fixS B) ≤ 16 := by
  obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
  have hlt : fixS B ≠ ⊤ := by
    intro h
    apply hg1
    apply Subtype.ext
    apply eq_one_of_mulVec
    intro y
    have : y ∈ fixS B := by rw [h]; trivial
    exact this g g.2
  have h1 : Module.finrank K (fixS B) < 3 := by
    have := Submodule.finrank_lt hlt
    rwa [Module.finrank_fin_fun] at this
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := fixS B)
  rw [hK] at h2
  rw [h2]
  have : Module.finrank K (fixS B) ≤ 2 := by omega
  calc 4 ^ Module.finrank K (fixS B) ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    _ = 16 := by norm_num

theorem submodule_eq_of_card {W W' : Submodule K (Fin 3 → K)} (hK : Nat.card K = 4) (h : W ≤ W')
    (hc : Nat.card W' ≤ Nat.card W) : W = W' := by
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := W)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := W')
  rw [hK] at h1 h2
  rw [h1, h2] at hc
  exact Submodule.eq_of_le_of_finrank_le h
    ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 4)).1 hc)

section Elem

variable (hK : Nat.card K = 4) (h2 : (2 : K) = 0)
  (hdet : ∀ g ∈ Γ₀, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)

include hK h2 hdet in
theorem stabS_isElem {W : Submodule K (Fin 3 → K)} (hW : Nat.card W = 16) :
    ∀ g ∈ stabS (Γ₀ := Γ₀) W, ∀ h ∈ stabS (Γ₀ := Γ₀) W, g * h = h * g ∧ g * g = 1 := by
  obtain ⟨v, hv, hWv⟩ := exists_hyperplane hK W hW
  have key : ∀ g ∈ stabS (Γ₀ := Γ₀) W,
      ∃ u : Fin 3 → K, mat Γ₀ g = 1 + vecMulVec u v ∧ v ⬝ᵥ u = 0 := by
    intro g hg
    obtain ⟨u, hu⟩ := eq_one_add_vecMulVec hv (fun y hy => hg y ((hWv y).2 hy))
    exact ⟨u, hu, dot_eq_zero_of_det hu (hdet g.1 g.2)⟩
  intro g hg h hh
  obtain ⟨u, hu, hvu⟩ := key g hg
  obtain ⟨u', hu', hvu'⟩ := key h hh
  refine ⟨mat_injective ?_, mat_injective ?_⟩
  · rw [mat_mul, mat_mul, hu, hu']
    exact comm_of_same hvu hvu'
  · rw [mat_mul, mat_one, hu]
    exact sq_eq_one h2 hvu

variable (h4 : ∀ B : Subgroup ↥Γ₀, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
  Nat.card B ≤ 4)

include hK h2 hdet h4 in
theorem offender_facts {B : Subgroup ↥Γ₀} (hB : B ≠ ⊥)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1)
    (hoff : 64 ≤ Nat.card B * Nat.card (fixS B)) :
    Nat.card B = 4 ∧ Nat.card (fixS B) = 16 ∧ B = stabS (fixS B) := by
  have h16 := card_fixS_le hK hB
  have hB4 : Nat.card B ≤ 4 := h4 B hcomm hsq
  have hB4' : 4 ≤ Nat.card B := by nlinarith
  have hBe : Nat.card B = 4 := le_antisymm hB4 hB4'
  have hfix : Nat.card (fixS B) = 16 := by rw [hBe] at hoff; omega
  refine ⟨hBe, hfix, ?_⟩
  have hel := stabS_isElem hK h2 hdet (W := fixS B) hfix
  have hcard : Nat.card (stabS (fixS B)) ≤ 4 :=
    h4 _ (fun a ha b hb => (hel a ha b hb).1) (fun a ha => (hel a ha a ha).2)
  exact Subgroup.eq_of_le_of_card_ge (le_stabS_fixS B) (by rw [hBe]; exact hcard)

include hK h2 hdet h4 in
theorem offender_unique {B B' : Subgroup ↥Γ₀} (hB : B ≠ ⊥)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1)
    (hoff : 64 ≤ Nat.card B * Nat.card (fixS B)) (hB' : B' ≠ ⊥)
    (hcomm' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a) (hsq' : ∀ a ∈ B', a * a = 1)
    (hoff' : 64 ≤ Nat.card B' * Nat.card (fixS B')) (hint : B ⊓ B' ≠ ⊥) : B = B' := by
  obtain ⟨_, hfix, hBs⟩ := offender_facts hK h2 hdet h4 hB hcomm hsq hoff
  obtain ⟨_, hfix', hBs'⟩ := offender_facts hK h2 hdet h4 hB' hcomm' hsq' hoff'
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hint
  have htB : (t : ↥Γ₀) ∈ B := t.2.1
  have htB' : (t : ↥Γ₀) ∈ B' := t.2.2
  have ht1' : (t : ↥Γ₀) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hz : Subgroup.zpowers (t : ↥Γ₀) ≠ ⊥ := by
    intro h
    apply ht1'
    have := Subgroup.mem_zpowers (t : ↥Γ₀)
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hle : ∀ {C : Subgroup ↥Γ₀}, (t : ↥Γ₀) ∈ C → fixS C ≤ fixS (Subgroup.zpowers (t : ↥Γ₀)) := by
    intro C hC y hy g hg
    exact hy g ((Subgroup.zpowers_le.2 hC) hg)
  have hz16 := card_fixS_le hK hz
  have e1 : fixS B = fixS (Subgroup.zpowers (t : ↥Γ₀)) :=
    submodule_eq_of_card hK (hle htB) (by rw [hfix]; exact hz16)
  have e2 : fixS B' = fixS (Subgroup.zpowers (t : ↥Γ₀)) :=
    submodule_eq_of_card hK (hle htB') (by rw [hfix']; exact hz16)
  rw [hBs, hBs', e1, e2]

end Elem

theorem inf_ne_bot_of_card {P B B' : Subgroup ↥Γ₀} (hP : Nat.card P = 8) (hB : B ≤ P)
    (hB' : B' ≤ P) (h4 : Nat.card B = 4) (h4' : Nat.card B' = 4) : B ⊓ B' ≠ ⊥ := by
  intro hbot
  let f : ↥B × ↥B' → ↥P := fun p => ⟨p.1 * p.2, P.mul_mem (hB p.1.2) (hB' p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : ↥Γ₀) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : ↥Γ₀)⁻¹ * a = b' * (b : ↥Γ₀)⁻¹ := by
      calc (a' : ↥Γ₀)⁻¹ * a = (a' : ↥Γ₀)⁻¹ * (a * b) * (b : ↥Γ₀)⁻¹ := by group
        _ = b' * (b : ↥Γ₀)⁻¹ := by rw [h1]; group
    have hmem : (a' : ↥Γ₀)⁻¹ * a ∈ B ⊓ B' :=
      ⟨B.mul_mem (B.inv_mem a'.2) a.2, h2 ▸ B'.mul_mem b'.2 (B'.inv_mem b.2)⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have ha : a = a' := Subtype.ext hmem.symm
    subst ha
    have : (b : ↥Γ₀) = b' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, h4, h4', hP] at this
  omega

end CFSG.Quasithin.C124.YL.H6
