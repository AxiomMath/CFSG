module

public import CFSG.Timmesfeld.Transvection.ModelSULowSpan
import CFSG.Timmesfeld.Transvection.AssembleModelSU

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

private def truncLow (j : ℕ) (v : Fin m → F) : Fin m → F :=
  v - ∑ i : Fin (m / 2), if i.val < j then v (lowIdx i) • Pi.single (lowIdx i) 1 else 0

private theorem truncLow_apply_lowIdx {j : ℕ} {v : Fin m → F} {i : Fin (m / 2)}
    (hi : i.val < j) : truncLow j v (lowIdx i) = 0 := by
  rw [truncLow, Pi.sub_apply, Fintype.sum_apply, Fintype.sum_eq_single i]
  · simp [hi]
  · intro b hb
    by_cases hbj : b.val < j
    · rw [if_pos hbj, Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
      intro h
      exact hb (Fin.ext (by simpa [val_lowIdx] using congrArg Fin.val h)).symm
    · rw [if_neg hbj]
      rfl

private theorem truncLow_apply_rev (j : ℕ) (v : Fin m → F) (i : Fin (m / 2)) :
    truncLow j v (Fin.rev (lowIdx i)) = v (Fin.rev (lowIdx i)) := by
  rw [truncLow, Pi.sub_apply, Fintype.sum_apply,
    Finset.sum_eq_zero (fun b _ => ?_), sub_zero]
  by_cases hbj : b.val < j
  · rw [if_pos hbj, Pi.smul_apply, Pi.single_eq_of_ne (lowIdx_ne_rev b i).symm, smul_zero]
  · rw [if_neg hbj]
    rfl

private theorem uForm_truncLow {j : ℕ} {v y : Fin m → F}
    (hy : ∀ i : Fin (m / 2), i.val < j → y (Fin.rev (lowIdx i)) = 0) :
    uForm σ (truncLow j v) y = uForm σ v y := by
  have hsum : uForm σ (∑ i : Fin (m / 2),
      if i.val < j then v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) y = 0 := by
    calc uForm σ (∑ i : Fin (m / 2),
          if i.val < j then v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) y
        = ∑ x : Fin m, σ ((∑ i : Fin (m / 2),
            if i.val < j then v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) x) *
              y (Fin.rev x) := by rw [uForm_eq]
      _ = ∑ x : Fin m, ∑ i : Fin (m / 2), σ ((if i.val < j then
            v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) x) * y (Fin.rev x) := by
            simp only [Finset.sum_apply, map_sum, Finset.sum_mul]
      _ = ∑ i : Fin (m / 2), ∑ x : Fin m, σ ((if i.val < j then
            v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) x) * y (Fin.rev x) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin (m / 2), uForm σ (if i.val < j then
            v (lowIdx i) • Pi.single (lowIdx i) 1 else 0) y := by
            simp only [uForm_eq]
      _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hi : i.val < j
            · rw [if_pos hi, uForm_smul_left, uForm_single_left, hy i hi, mul_zero]
            · rw [if_neg hi]
              simp [uForm_eq]
  rw [truncLow, uForm_sub_left, hsum, sub_zero]

private theorem truncLow_perpUU {j : ℕ} {v : Fin m → F}
    (hv : ∀ i : Fin (m / 2), i.val < j → v (Fin.rev (lowIdx i)) = 0) :
    PerpUU j (truncLow j v) := by
  intro i hi
  exact ⟨truncLow_apply_lowIdx hi, by rw [truncLow_apply_rev]; exact hv i hi⟩

private theorem truncLow_ne_zero {j : ℕ} {v : Fin m → F} {i : Fin (m / 2)}
    (hi : v (Fin.rev (lowIdx i)) ≠ 0) : truncLow j v ≠ 0 := by
  intro h
  exact hi (by rw [← truncLow_apply_rev j v i, h]; rfl)

private theorem exists_suMat_apply_rev_eq_zero_of_exists [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {S : Set (Fin m → F)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, uForm σ x y = 0) {j : ℕ} (hj : j < m / 2) {g : SU σ m}
    (hg : ∀ x ∈ S, ∀ i : Fin (m / 2), i.val < j →
      (suMat σ m g *ᵥ x) (Fin.rev (lowIdx i)) = 0)
    (hex : ∃ x ∈ S, (suMat σ m g *ᵥ x) (Fin.rev (lowIdx ⟨j, hj⟩)) ≠ 0) :
    ∃ g' : SU σ m, ∀ x ∈ S, ∀ i : Fin (m / 2), i.val < j + 1 →
      (suMat σ m g' *ᵥ x) (Fin.rev (lowIdx i)) = 0 := by
  obtain ⟨x₀, hx₀S, hx₀⟩ := hex
  set v : Fin m → F := suMat σ m g *ᵥ x₀ with hv
  set w : Fin m → F := truncLow j v with hwdef
  set e : Fin m → F := Pi.single (lowIdx ⟨j, hj⟩) 1 with he
  have hvp : ∀ i : Fin (m / 2), i.val < j → v (Fin.rev (lowIdx i)) = 0 :=
    fun i hi => hg x₀ hx₀S i hi
  have hwU : PerpUU j w := truncLow_perpUU hvp
  have heU : PerpUU j e := by
    intro i hi
    constructor
    · rw [he, Pi.single_eq_of_ne]
      intro h
      have hval : i.val = j := by
        have h' := congrArg Fin.val h
        rw [val_lowIdx, val_lowIdx] at h'
        simpa using h'
      omega
    · rw [he, Pi.single_eq_of_ne (lowIdx_ne_rev ⟨j, hj⟩ i).symm]
  have hw0 : w ≠ 0 := by
    refine truncLow_ne_zero (i := ⟨j, hj⟩) ?_
    rwa [hv]
  have he0 : e ≠ 0 := by
    rw [he]
    exact single_one_ne_zero _
  have hvv : uForm σ v v = 0 := by
    rw [hv]
    exact (uForm_mulVec σ g x₀ x₀).trans (hS x₀ hx₀S x₀ hx₀S)
  have hwv : uForm σ w v = 0 := by
    rw [hwdef, uForm_truncLow (fun i hi => hvp i hi), hvv]
  have hvw : uForm σ v w = 0 := uForm_eq_zero_comm hσ hwv
  have hww : uForm σ w w = 0 := by
    rw [hwdef, uForm_truncLow (fun i hi => (hwU i hi).2), hvw]
  have hee : uForm σ e e = 0 := by
    rw [he]
    exact uForm_single_self (lowIdx_ne_rev ⟨j, hj⟩ ⟨j, hj⟩)
  obtain ⟨g', l, hl, hgw, hfix⟩ :=
    exists_suMat_mulVec_eq_smul_of_perp hσ htr (ζ := 1) one_ne_zero
      (by rw [map_one, CharTwo.add_self_eq_zero]) hwU heU hw0 he0 hww hee
  refine ⟨g' * g, fun x hxS i hi => ?_⟩
  rw [map_mul, ← Matrix.mulVec_mulVec]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hij | hij
  · calc (suMat σ m g' *ᵥ (suMat σ m g *ᵥ x)) (Fin.rev (lowIdx i))
        = uForm σ (Pi.single (lowIdx i) 1)
            (suMat σ m g' *ᵥ (suMat σ m g *ᵥ x)) := by rw [uForm_single_left]
      _ = uForm σ (suMat σ m g' *ᵥ Pi.single (lowIdx i) 1)
            (suMat σ m g' *ᵥ (suMat σ m g *ᵥ x)) := by rw [(hfix i hij).1]
      _ = uForm σ (Pi.single (lowIdx i) 1) (suMat σ m g *ᵥ x) :=
            uForm_mulVec σ g' _ _
      _ = (suMat σ m g *ᵥ x) (Fin.rev (lowIdx i)) := by rw [uForm_single_left]
      _ = 0 := hg x hxS i hij
  · have hii : i = ⟨j, hj⟩ := Fin.ext hij
    subst hii
    have hej : e = suMat σ m g' *ᵥ (l⁻¹ • w) := by
      rw [mulVec_smul, hgw, smul_smul, inv_mul_cancel₀ hl, one_smul]
    rw [← uForm_single_left (lowIdx ⟨j, hj⟩)
      (suMat σ m g' *ᵥ (suMat σ m g *ᵥ x))]
    calc uForm σ e (suMat σ m g' *ᵥ (suMat σ m g *ᵥ x))
        = uForm σ (l⁻¹ • w) (suMat σ m g *ᵥ x) := by rw [hej, uForm_mulVec]
      _ = σ l⁻¹ * uForm σ w (suMat σ m g *ᵥ x) := uForm_smul_left σ (l⁻¹) w (suMat σ m g *ᵥ x)
      _ = 0 := by
            rw [show uForm σ w (suMat σ m g *ᵥ x) = 0 by
              rw [hwdef, uForm_truncLow (fun k hk => hg x hxS k hk), hv]
              exact (uForm_mulVec σ g x₀ x).trans (hS x₀ hx₀S x hxS), mul_zero]

private theorem exists_suMat_apply_rev_eq_zero_succ [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {S : Set (Fin m → F)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, uForm σ x y = 0) {j : ℕ} (hj : j < m / 2) {g : SU σ m}
    (hg : ∀ x ∈ S, ∀ i : Fin (m / 2), i.val < j →
      (suMat σ m g *ᵥ x) (Fin.rev (lowIdx i)) = 0) :
    ∃ g' : SU σ m, ∀ x ∈ S, ∀ i : Fin (m / 2), i.val < j + 1 →
      (suMat σ m g' *ᵥ x) (Fin.rev (lowIdx i)) = 0 := by
  classical
  by_cases hex : ∃ x ∈ S, (suMat σ m g *ᵥ x) (Fin.rev (lowIdx ⟨j, hj⟩)) ≠ 0
  · exact exists_suMat_apply_rev_eq_zero_of_exists hσ htr hS hj hg hex
  · refine ⟨g, fun x hxS i hi => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hij | hij
    · exact hg x hxS i hij
    · have hii : i = ⟨j, hj⟩ := Fin.ext hij
      subst hii
      by_contra h
      exact hex ⟨x, hxS, h⟩

theorem exists_suMat_mulVec_mem_lowSpan [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {S : Set (Fin m → F)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, uForm σ x y = 0) :
    ∃ g : SU σ m, ∀ x ∈ S, suMat σ m g *ᵥ x ∈ lowSpan F m := by
  classical
  have hP : ∀ j ≤ m / 2, ∃ g : SU σ m, ∀ x ∈ S, ∀ i : Fin (m / 2), i.val < j →
      (suMat σ m g *ᵥ x) (Fin.rev (lowIdx i)) = 0 := by
    intro j hj
    induction j with
    | zero =>
        refine ⟨1, fun x _ i hi => ?_⟩
        exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
        obtain ⟨g, hg⟩ := ih (by omega)
        exact exists_suMat_apply_rev_eq_zero_succ hσ htr hS (by omega) hg
  obtain ⟨g, hg⟩ := hP (m / 2) le_rfl
  refine ⟨g, ?_⟩
  intro x hx
  exact mem_lowSpan_of_apply_rev_eq_zero
    ((uForm_mulVec σ g x x).trans (hS x hx x hx)) (fun i => hg x hx i i.isLt)

end ModelRank

end CFSG.Timmesfeld.Transvection
