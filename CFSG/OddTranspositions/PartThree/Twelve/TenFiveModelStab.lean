module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelCenter
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelWalk
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

variable {k : ℕ} {ε π : Bool} {c : Fin (k + 1) → ZMod 5}

private theorem zmod5_binary_square (a b c : ZMod 5) (hb : b ≠ 0) (hd : a * c - b * b ≠ 0) :
    ∃ x z : ZMod 5, a * x + b * z ≠ 0 ∧
      a * x * x + 2 * b * x * z + c * z * z ≠ 0 ∧
      (a * x * x + 2 * b * x * z + c * z * z = 1 ∨
        a * x * x + 2 * b * x * z + c * z * z = 4) := by
  revert a b c
  decide

private theorem zmod5_binary_nonsquare (a b c : ZMod 5) (hb : b ≠ 0) (hd : a * c - b * b ≠ 0) :
    ∃ x z : ZMod 5, a * x + b * z ≠ 0 ∧
      a * x * x + 2 * b * x * z + c * z * z ≠ 0 ∧
      (a * x * x + 2 * b * x * z + c * z * z = 2 ∨
        a * x * x + 2 * b * x * z + c * z * z = 3) := by
  revert a b c
  decide

private theorem zmod5_isSquare_iff (q : ZMod 5) (hq : q ≠ 0) :
    (IsSquare q ↔ q = 1 ∨ q = 4) := by
  revert q
  decide

private theorem zmod5_not_isSquare_iff (q : ZMod 5) :
    (¬ IsSquare q ↔ q = 2 ∨ q = 3) := by
  revert q
  decide

private theorem zmod5_units_sq_eq_one (u : (ZMod 5)ˣ) (h : u * u = 1) : u = 1 ∨ u = -1 := by
  revert u
  decide

private theorem zmod5_units_sq_of_not_isSquare (u : (ZMod 5)ˣ)
    (h : ¬ IsSquare (u : ZMod 5)) : u ^ 2 = -1 := by
  revert u
  decide

theorem orderOf_eq_four_of_not_isSquare (u : (ZMod 5)ˣ) (h : ¬ IsSquare (u : ZMod 5)) :
    orderOf u = 4 := by
  have h2 : u ^ 2 = -1 := zmod5_units_sq_of_not_isSquare u h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · rw [pow_one, h2]
    intro hc
    exact absurd (congrArg (fun w : (ZMod 5)ˣ => (w : ZMod 5)) hc) (by decide)
  · rw [show 2 ^ (1 + 1) = 4 by norm_num, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2]
    decide

theorem natCard_units_five : Nat.card (ZMod 5)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem orderOf_neg_one_units : orderOf (-1 : (ZMod 5)ˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · ext; decide
  · intro h
    exact absurd (congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) h) (by decide)

private theorem neg_one_units_smul (k : ℕ) (x : Fin (k + 1) → ZMod 5) :
    (((-1 : (ZMod 5)ˣ) : ZMod 5)) • x = -x := by
  funext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Units.val_neg, Units.val_one]
  exact neg_one_mul (x i)

private theorem zmod5_coeff_one (α : ZMod 5) (hα : α ≠ 0) :
    2 * (-α) * (-2 * α)⁻¹ = 1 := by
  have hB : (-2 * α) ≠ 0 := mul_ne_zero (by decide) hα
  field_simp
  rw [div_self (by decide : (2 : ZMod 5) ≠ 0)]

private theorem zmod5_coeff_inv (α : ZMod 5) (hα : α ≠ 0) :
    2 * 1 * (-2 * α)⁻¹ = -α⁻¹ := by
  have hB : (-2 * α) ≠ 0 := mul_ne_zero (by decide) hα
  field_simp
  rw [div_self (by decide : (2 : ZMod 5) ≠ 0)]

private theorem zmod5_two_div (a : ZMod 5) : 2 * (a / 2) = a := by
  rw [mul_comm 2 (a / 2), div_eq_mul_inv, mul_assoc,
    inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), mul_one]

private theorem zmod5_hBc_id (α : ZMod 5) : (0 : ZMod 5) - α * 1 = -α := by
  revert α; decide

private theorem zmod5_hQv_id (α : ZMod 5) :
    (0 : ZMod 5) + α * α * 0 - 2 * (α * 1) = -2 * α := by
  revert α; decide

private theorem zmod5_inv_three : (3 : ZMod 5)⁻¹ = 2 :=
  inv_eq_of_mul_eq_one_right (by decide : (3 : ZMod 5) * 2 = 1)

private theorem zmod5_vec_reflect (k : ℕ) (c d : Fin (k + 1) → ZMod 5) (α : ZMod 5)
    (hα : α ≠ 0) : d - (-α⁻¹) • (c - α • d) = α⁻¹ • c := by
  rw [smul_sub, smul_smul]
  have hneg : (-α⁻¹) * α = -(1 : ZMod 5) := by
    calc (-α⁻¹) * α = -(α⁻¹ * α) := neg_mul α⁻¹ α
      _ = -(1 : ZMod 5) := by rw [inv_mul_cancel₀ hα]
  have hneg1 : (-1 : ZMod 5) • d = -d := by
    funext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact neg_one_mul (d i)
  have hneg2 : (-α⁻¹) • c = -(α⁻¹ • c) := by
    funext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact neg_mul α⁻¹ (c i)
  rw [hneg, hneg1, hneg2]
  abel

@[expose] def fiveLineStab (k : ℕ) (ε π : Bool) (c : Fin (k + 1) → ZMod 5) :
    Subgroup (GL (Fin (k + 1)) (ZMod 5)) where
  carrier := {g | ∃ lam : (ZMod 5)ˣ,
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (lam : ZMod 5) • c}
  mul_mem' := by
    rintro g h ⟨lam, hlam⟩ ⟨mu, hmu⟩
    refine ⟨mu * lam, ?_⟩
    show (((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *
        (h : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) =
      ((mu * lam : (ZMod 5)ˣ) : ZMod 5) • c
    rw [← Matrix.mulVec_mulVec, hmu, Matrix.mulVec_smul, hlam, smul_smul, Units.val_mul]
  one_mem' := ⟨1, by
    show ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c) =
      ((1 : (ZMod 5)ˣ) : ZMod 5) • c
    rw [Matrix.one_mulVec, Units.val_one, one_smul]⟩
  inv_mem' := by
    rintro g ⟨lam, hlam⟩
    refine ⟨lam⁻¹, ?_⟩
    show ((((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) =
      ((lam⁻¹ : (ZMod 5)ˣ) : ZMod 5) • c
    have h : (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ
        (((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) =
        (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ ((lam : ZMod 5) • c) := by
      rw [hlam]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hleft : ((((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c = c := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
        Matrix.one_mulVec]
    rw [hleft] at h
    have h2 : (((lam⁻¹ : (ZMod 5)ˣ) : ZMod 5)) • c =
        (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c := by
      nth_rewrite 1 [h]
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    exact h2.symm

theorem mem_fiveLineStab {g : GL (Fin (k + 1)) (ZMod 5)} :
    g ∈ fiveLineStab k ε π c ↔ ∃ lam : (ZMod 5)ˣ,
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (lam : ZMod 5) • c :=
  Iff.rfl

theorem fiveLineStab_smul_unique {lam mu : (ZMod 5)ˣ} {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    (h : (lam : ZMod 5) • c = (mu : ZMod 5) • c) : lam = mu := by
  apply Units.ext
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  have h1 := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : ((lam : ZMod 5) - (mu : ZMod 5)) * c i = 0 := by
    rw [sub_mul, h1, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hi)

noncomputable def fiveLineStabHom (k : ℕ) (ε π : Bool) (c : Fin (k + 1) → ZMod 5)
    (hc : c ≠ 0) :
    ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c) →* (ZMod 5)ˣ where
  toFun g := Classical.choose (mem_fiveLineStab.mp g.2.2)
  map_one' := by
    apply fiveLineStab_smul_unique hc
    have hspec := Classical.choose_spec
      (mem_fiveLineStab.mp ((1 : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)).2.2))
    rw [← hspec]
    show (((1 : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)) :
        GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c =
      ((1 : (ZMod 5)ˣ) : ZMod 5) • c
    rw [Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, Units.val_one,
      one_smul]
  map_mul' := by
    intro g h
    apply fiveLineStab_smul_unique hc
    have hspec_gh := Classical.choose_spec
      (mem_fiveLineStab.mp ((g * h : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)).2.2))
    have hspec_g := Classical.choose_spec (mem_fiveLineStab.mp g.2.2)
    have hspec_h := Classical.choose_spec (mem_fiveLineStab.mp h.2.2)
    rw [← hspec_gh]
    show ((((g : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)) :
        GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *
        (((h : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)) :
        GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c =
      ((Classical.choose (mem_fiveLineStab.mp g.2.2) *
        Classical.choose (mem_fiveLineStab.mp h.2.2) : (ZMod 5)ˣ) : ZMod 5) • c
    conv_lhs =>
      rw [← Matrix.mulVec_mulVec, hspec_h, Matrix.mulVec_smul, hspec_g, smul_smul]
    rw [Units.val_mul]
    congr 1
    ring_nf

theorem fiveLineStabHom_spec (k : ℕ) (ε π : Bool) (c : Fin (k + 1) → ZMod 5)
    (hc : c ≠ 0) (g : ↥(fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c)) :
    (g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c =
      ((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5) • c :=
  Classical.choose_spec (mem_fiveLineStab.mp g.2.2)

theorem fiveReflOf_mulVec_eq_self_iff {ε : Bool} {w v : Fin (k + 1) → ZMod 5}
    (hw : fiveForm k ε w w ≠ 0) :
    (fiveReflOf k ε w : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v = v ↔
      fiveForm k ε v w = 0 := by
  rw [fiveReflOf_mulVec]
  constructor
  · intro h
    have h2 : (2 * fiveForm k ε v w * (fiveForm k ε w w)⁻¹) • w = 0 := sub_eq_self.mp h
    have hcoeff : 2 * fiveForm k ε v w * (fiveForm k ε w w)⁻¹ = 0 := by
      rcases smul_eq_zero.mp h2 with hc | hw0
      · exact hc
      · exact absurd hw0 (fun hw' => hw (by rw [hw']; simp [fiveForm]))
    rcases mul_eq_zero.mp hcoeff with h4 | h5
    · rcases mul_eq_zero.mp h4 with h6 | h7
      · exact absurd h6 (by decide)
      · exact h7
    · exact absurd h5 (inv_ne_zero hw)
  · intro h
    rw [h]
    simp

theorem fiveForm_sub_sub (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x - y) (x - y) =
      fiveForm k ε x x + fiveForm k ε y y - 2 * fiveForm k ε x y := by
  rw [show x - y = x + (-1 : ZMod 5) • y by
    rw [sub_eq_add_neg]
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact (neg_one_mul (y i)).symm]
  rw [fiveForm_self_add k ε x ((-1 : ZMod 5) • y),
    fiveForm_smul_smul k ε (-1) (-1) y y, fiveForm_smul_right k ε (-1) x y]
  generalize fiveForm k ε x x = a
  generalize fiveForm k ε x y = b
  generalize fiveForm k ε y y = cc
  revert a b cc
  decide

theorem mem_fiveReflectionsFixing {g : GL (Fin (k + 1)) (ZMod 5)} :
    g ∈ fiveReflectionsFixing k ε π c ↔ g ∈ fiveReflections k ε π ∧
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c :=
  Iff.rfl

theorem fiveReflOf_mem_fiveReflectionsFixing_iff {ε π : Bool} {w : Fin (k + 1) → ZMod 5}
    (hw : fiveForm k ε w w ≠ 0) (hπ : IsSquare (fiveForm k ε w w) ↔ π = true) :
    fiveReflOf k ε w ∈ fiveReflectionsFixing k ε π c ↔ fiveForm k ε w c = 0 := by
  rw [mem_fiveReflectionsFixing, iff_true_intro (fiveReflOf_mem hw hπ), true_and,
    fiveReflOf_mulVec_eq_self_iff hw, fiveForm_comm k ε w c]

theorem exists_fiveForm_aniso_ne_zero {ε : Bool} {u y : Fin (k + 1) → ZMod 5}
    (huy : fiveForm k ε u y ≠ 0)
    (hdet : fiveForm k ε u u * fiveForm k ε y y -
      fiveForm k ε u y * fiveForm k ε u y ≠ 0) (σ : Bool) :
    ∃ w ∈ Submodule.span (ZMod 5) ({u, y} : Set (Fin (k + 1) → ZMod 5)),
      fiveForm k ε w w ≠ 0 ∧ (IsSquare (fiveForm k ε w w) ↔ σ = true) ∧
        fiveForm k ε u w ≠ 0 := by
  have hspan : ∀ x z : ZMod 5, x • u + z • y ∈
      Submodule.span (ZMod 5) ({u, y} : Set (Fin (k + 1) → ZMod 5)) := by
    intro x z
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hQ : ∀ x z : ZMod 5, fiveForm k ε (x • u + z • y) (x • u + z • y) =
      fiveForm k ε u u * x * x + 2 * fiveForm k ε u y * x * z +
        fiveForm k ε y y * z * z := by
    intro x z
    rw [fiveForm_self_add, fiveForm_smul_smul, fiveForm_smul_smul, fiveForm_smul_smul]
    ring_nf
  have hB : ∀ x z : ZMod 5, fiveForm k ε u (x • u + z • y) =
      fiveForm k ε u u * x + fiveForm k ε u y * z := by
    intro x z
    rw [fiveForm_add_right, fiveForm_smul_right, fiveForm_smul_right]
    ring_nf
  cases σ
  · obtain ⟨x, z, hxz, hq⟩ := zmod5_binary_nonsquare (fiveForm k ε u u)
      (fiveForm k ε u y) (fiveForm k ε y y) huy hdet
    refine ⟨x • u + z • y, hspan x z, ?_, ?_, ?_⟩
    · rw [hQ]; exact hq.1
    · rw [hQ]
      have hnot : ¬ IsSquare (fiveForm k ε u u * x * x + 2 * fiveForm k ε u y * x * z +
          fiveForm k ε y y * z * z) := (zmod5_not_isSquare_iff _).mpr hq.2
      simpa using hnot
    · rw [hB]; exact hxz
  · obtain ⟨x, z, hxz, hq⟩ := zmod5_binary_square (fiveForm k ε u u)
      (fiveForm k ε u y) (fiveForm k ε y y) huy hdet
    refine ⟨x • u + z • y, hspan x z, ?_, ?_, ?_⟩
    · rw [hQ]; exact hq.1
    · rw [hQ]
      have hsq : IsSquare (fiveForm k ε u u * x * x + 2 * fiveForm k ε u y * x * z +
          fiveForm k ε y y * z * z) := (zmod5_isSquare_iff _ hq.1).mpr hq.2
      simpa using hsq
    · rw [hB]; exact hxz

theorem exists_fiveForm_det_ne {ε : Bool} (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5))
    {u : Fin (k + 1) → ZMod 5}
    (hW : ∀ x ∈ W, (∀ y ∈ W, fiveForm k ε x y = 0) → x = 0)
    (hroom : ∃ z ∈ W, fiveForm k ε u z = 0 ∧ z ≠ 0)
    (huW : u ∈ W) (hu : u ≠ 0) :
    ∃ y ∈ W, fiveForm k ε u y ≠ 0 ∧
      fiveForm k ε u u * fiveForm k ε y y - fiveForm k ε u y * fiveForm k ε u y ≠ 0 := by
  have hy0 : ∃ y ∈ W, fiveForm k ε u y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hW u huW h)
  obtain ⟨y0, hy0W, huy0⟩ := hy0
  by_cases hdet : fiveForm k ε u u * fiveForm k ε y0 y0 -
      fiveForm k ε u y0 * fiveForm k ε u y0 = 0
  swap
  · exact ⟨y0, hy0W, huy0, hdet⟩
  have ha : fiveForm k ε u u ≠ 0 := by
    intro ha0
    have h := hdet
    rw [ha0] at h
    simp only [zero_mul, zero_sub] at h
    exact huy0 (mul_self_eq_zero.mp (neg_eq_zero.mp h))
  have hz : ∃ z ∈ W, fiveForm k ε u z = 0 ∧
      fiveForm k ε (y0 + z) (y0 + z) ≠ fiveForm k ε y0 y0 := by
    by_contra h
    push_neg at h
    obtain ⟨z, hzW, hzu, hz0⟩ := hroom
    have hbil : ∀ z1 ∈ W, fiveForm k ε u z1 = 0 → ∀ z2 ∈ W, fiveForm k ε u z2 = 0 →
        fiveForm k ε z1 z2 = 0 := by
      intro z1 hz1W hz1u z2 hz2W hz2u
      have e1 : fiveForm k ε (y0 + z1) (y0 + z1) = fiveForm k ε y0 y0 := h z1 hz1W hz1u
      have e2 : fiveForm k ε (y0 + z2) (y0 + z2) = fiveForm k ε y0 y0 := h z2 hz2W hz2u
      have e12 : fiveForm k ε (y0 + (z1 + z2)) (y0 + (z1 + z2)) = fiveForm k ε y0 y0 :=
        h (z1 + z2) (W.add_mem hz1W hz2W) (by
          rw [fiveForm_add_right, hz1u, hz2u, add_zero])
      have e1' : fiveForm k ε y0 y0 + fiveForm k ε z1 z1 + 2 * fiveForm k ε y0 z1 =
          fiveForm k ε y0 y0 := by
        rw [← fiveForm_self_add]; exact e1
      have e2' : fiveForm k ε y0 y0 + fiveForm k ε z2 z2 + 2 * fiveForm k ε y0 z2 =
          fiveForm k ε y0 y0 := by
        rw [← fiveForm_self_add]; exact e2
      have e12' : fiveForm k ε y0 y0 +
          (fiveForm k ε z1 z1 + fiveForm k ε z2 z2 + 2 * fiveForm k ε z1 z2) +
          2 * (fiveForm k ε y0 z1 + fiveForm k ε y0 z2) = fiveForm k ε y0 y0 := by
        rw [← fiveForm_self_add (k := k) (ε := ε) z1 z2,
          ← fiveForm_add_right (n := k) (ε := ε) y0 z1 z2,
          ← fiveForm_self_add (k := k) (ε := ε) y0 (z1 + z2)]
        exact e12
      have h2 : (2 : ZMod 5) * fiveForm k ε z1 z2 = 0 := by
        linear_combination e12' - e1' - e2'
      exact (mul_eq_zero.mp h2).resolve_left (by decide)
    have hrad : ∀ w ∈ W, fiveForm k ε z w = 0 := by
      intro w hwW
      have hpW : w - (fiveForm k ε w u * (fiveForm k ε u u)⁻¹) • u ∈ W :=
        W.sub_mem hwW (W.smul_mem _ huW)
      have hpu : fiveForm k ε u (w - (fiveForm k ε w u * (fiveForm k ε u u)⁻¹) • u) = 0 := by
        rw [fiveForm_sub_right, fiveForm_smul_right, fiveForm_comm k ε w u]
        field_simp
        ring_nf
      have hsplit : w = (w - (fiveForm k ε w u * (fiveForm k ε u u)⁻¹) • u) +
          (fiveForm k ε w u * (fiveForm k ε u u)⁻¹) • u := by abel
      rw [hsplit, fiveForm_add_right, fiveForm_smul_right,
        hbil z hzW hzu _ hpW hpu, fiveForm_comm k ε z u, hzu, mul_zero, add_zero]
    exact hz0 (hW z hzW hrad)
  obtain ⟨z, hzW, hzu, hQz⟩ := hz
  refine ⟨y0 + z, W.add_mem hy0W hzW, ?_, ?_⟩
  · rw [fiveForm_add_right k ε u y0 z, hzu, add_zero]; exact huy0
  · intro hzero
    have hBu : fiveForm k ε u (y0 + z) = fiveForm k ε u y0 := by
      rw [fiveForm_add_right k ε u y0 z, hzu, add_zero]
    rw [hBu] at hzero
    have hsub : fiveForm k ε u u *
        (fiveForm k ε (y0 + z) (y0 + z) - fiveForm k ε y0 y0) = 0 := by
      linear_combination hzero - hdet
    exact (mul_ne_zero ha (sub_ne_zero.mpr hQz)) hsub

theorem exists_fiveForm_aniso_ne_zero_of_nondegenerate {ε : Bool}
    (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5))
    (hW : ∀ x ∈ W, (∀ y ∈ W, fiveForm k ε x y = 0) → x = 0)
    {u : Fin (k + 1) → ZMod 5}
    (hroom : ∃ z ∈ W, fiveForm k ε u z = 0 ∧ z ≠ 0)
    (huW : u ∈ W) (hu : u ≠ 0) (σ : Bool) :
    ∃ w ∈ W, fiveForm k ε w w ≠ 0 ∧ (IsSquare (fiveForm k ε w w) ↔ σ = true) ∧
      fiveForm k ε u w ≠ 0 := by
  obtain ⟨y, hyW, huy, hdet⟩ := exists_fiveForm_det_ne W hW hroom huW hu
  obtain ⟨w, hwspan, hwQ, hwsign, huw⟩ := exists_fiveForm_aniso_ne_zero huy hdet σ
  refine ⟨w, ?_, hwQ, hwsign, huw⟩
  refine Submodule.span_le.mpr ?_ hwspan
  rintro x (rfl | rfl)
  · exact huW
  · exact hyW

private def fivePerpSubmodule (k : ℕ) (ε : Bool) (c : Fin (k + 1) → ZMod 5) :
    Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) where
  carrier := {x | fiveForm k ε x c = 0}
  zero_mem' := by simp [fiveForm]
  add_mem' := by
    intro x y hx hy
    show fiveForm k ε (x + y) c = 0
    exact (fiveForm_add_left k ε x y c).trans (by rw [hx, hy, add_zero])
  smul_mem' := by
    intro a x hx
    show fiveForm k ε (a • x) c = 0
    exact (fiveForm_smul_left k ε a x c).trans (by rw [hx, mul_zero])

private def fiveW0 (k : ℕ) (ε : Bool) (c d : Fin (k + 1) → ZMod 5) :
    Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) where
  carrier := {x | fiveForm k ε x c = 0 ∧ fiveForm k ε x d = 0}
  zero_mem' := by simp [fiveForm]
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · exact (fiveForm_add_left k ε x y c).trans (by rw [hx.1, hy.1, add_zero])
    · exact (fiveForm_add_left k ε x y d).trans (by rw [hx.2, hy.2, add_zero])
  smul_mem' := by
    intro a x hx
    refine ⟨?_, ?_⟩
    · exact (fiveForm_smul_left k ε a x c).trans (by rw [hx.1, mul_zero])
    · exact (fiveForm_smul_left k ε a x d).trans (by rw [hx.2, mul_zero])

private theorem exists_ne_zero_perp_fiveForm (k : ℕ) (ε π : Bool) {m : ℕ}
    (hm : m < k + 1) (us : Fin m → Fin (k + 1) → ZMod 5) :
    ∃ y, y ≠ 0 ∧ ∀ i, fiveForm k ε y (us i) = 0 := by
  obtain ⟨y, hy0, hy⟩ :=
    CFSG.OddTranspositions.PartFour.TableE1Five.exists_ne_zero_perp
      (b := fiveBilin k ε π) (hk := hm) us
  refine ⟨y, hy0, fun i => ?_⟩
  have h := hy i
  rw [fiveBilin_apply] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (fiveSignRep_ne_zero π))

theorem fiveSignPerp_span_orthogonal (hk : 4 ≤ k) (ε π : Bool) {c v : Fin (k + 1) → ZMod 5}
    (hc : c ≠ 0)
    (hv : ∀ w, fiveForm k ε w w ≠ 0 → (IsSquare (fiveForm k ε w w) ↔ π = true) →
      fiveForm k ε w c = 0 → fiveForm k ε v w = 0) :
    ∃ a : ZMod 5, a • c = v := by
  by_cases hQc : fiveForm k ε c c = 0
  ·
    have hy : ∃ y, fiveForm k ε c y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (FiveWalk.fiveForm_nondegenerate k ε _ h)
    obtain ⟨y, hy⟩ := hy
    let y1 : Fin (k + 1) → ZMod 5 := (fiveForm k ε c y)⁻¹ • y
    have hy1 : fiveForm k ε c y1 = 1 := by
      change fiveForm k ε c ((fiveForm k ε c y)⁻¹ • y) = 1
      rw [fiveForm_smul_right k ε ((fiveForm k ε c y)⁻¹) c y]
      exact inv_mul_cancel₀ hy
    let d : Fin (k + 1) → ZMod 5 := y1 - (fiveForm k ε y1 y1 / 2) • c
    have hd1 : fiveForm k ε c d = 1 := by
      change fiveForm k ε c (y1 - (fiveForm k ε y1 y1 / 2) • c) = 1
      rw [fiveForm_sub_right k ε c y1 ((fiveForm k ε y1 y1 / 2) • c),
        fiveForm_smul_right k ε (fiveForm k ε y1 y1 / 2) c c, hQc, mul_zero]
      exact (sub_zero (fiveForm k ε c y1)).trans hy1
    have hd0 : fiveForm k ε d d = 0 := by
      have hB : fiveForm k ε y1 c = 1 := by rw [fiveForm_comm k ε y1 c]; exact hy1
      change fiveForm k ε (y1 - (fiveForm k ε y1 y1 / 2) • c)
        (y1 - (fiveForm k ε y1 y1 / 2) • c) = 0
      rw [fiveForm_sub_sub k ε y1 ((fiveForm k ε y1 y1 / 2) • c),
        fiveForm_smul_smul k ε (fiveForm k ε y1 y1 / 2) (fiveForm k ε y1 y1 / 2) c c,
        fiveForm_smul_right k ε (fiveForm k ε y1 y1 / 2) y1 c, hQc, hB]
      simp only [mul_zero, mul_one, add_zero]
      exact sub_eq_zero.mpr (zmod5_two_div _).symm
    let W := fiveW0 k ε c d
    let u : Fin (k + 1) → ZMod 5 :=
      v - fiveForm k ε v d • c - fiveForm k ε v c • d
    have hW : ∀ x ∈ W, (∀ y ∈ W, fiveForm k ε x y = 0) → x = 0 := by
      intro x hxW hxperp
      apply FiveWalk.fiveForm_nondegenerate k ε
      intro y
      have hyW : y - fiveForm k ε y d • c - fiveForm k ε y c • d ∈ W := by
        change fiveForm k ε (y - fiveForm k ε y d • c - fiveForm k ε y c • d) c = 0 ∧
          fiveForm k ε (y - fiveForm k ε y d • c - fiveForm k ε y c • d) d = 0
        constructor
        · rw [fiveForm_sub_left, fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left,
            fiveForm_comm k ε d c, hd1, hQc]
          ring_nf
        · rw [fiveForm_sub_left, fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left,
            hd1, hd0]
          ring_nf
      have hsplit : y = (y - fiveForm k ε y d • c - fiveForm k ε y c • d) +
          fiveForm k ε y d • c + fiveForm k ε y c • d := by abel
      rw [hsplit, fiveForm_add_right, fiveForm_add_right, fiveForm_smul_right,
        fiveForm_smul_right, hxperp _ hyW, hxW.2, hxW.1, mul_zero, mul_zero, add_zero, add_zero]
    have hroom : ∃ z ∈ W, fiveForm k ε u z = 0 ∧ z ≠ 0 := by
      obtain ⟨z, hz0, hz⟩ := exists_ne_zero_perp_fiveForm k ε π (m := 3)
        (by omega) ![c, d, u]
      refine ⟨z, ?_, ?_, hz0⟩
      · constructor
        · simpa using hz 0
        · simpa using hz 1
      · rw [fiveForm_comm k ε u z]; simpa using hz 2
    have huW : u ∈ W := by
      change fiveForm k ε u c = 0 ∧ fiveForm k ε u d = 0
      constructor
      · rw [show u = v - fiveForm k ε v d • c - fiveForm k ε v c • d from rfl,
          fiveForm_sub_left, fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left,
          fiveForm_comm k ε d c, hQc, hd1]
        ring_nf
      · rw [show u = v - fiveForm k ε v d • c - fiveForm k ε v c • d from rfl,
          fiveForm_sub_left, fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left,
          hd1, hd0]
        ring_nf
    have hu0 : u = 0 := by
      by_contra hu
      obtain ⟨w, hwW, hwQ, hwsign, huw⟩ :=
        exists_fiveForm_aniso_ne_zero_of_nondegenerate W hW hroom huW hu π
      have hw := hv w hwQ hwsign hwW.1
      refine huw ?_
      have h_expand : fiveForm k ε u w = fiveForm k ε v w := by
        rw [show u = v - fiveForm k ε v d • c - fiveForm k ε v c • d from rfl,
          fiveForm_sub_left, fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left,
          fiveForm_comm k ε c w, fiveForm_comm k ε d w, hwW.1, hwW.2]
        ring_nf
      rw [h_expand]; exact hw
    have hcdQ : fiveForm k ε (c + d) (c + d) ≠ 0 := by
      rw [fiveForm_self_add k ε c d, hQc, hd0, hd1]
      decide
    obtain ⟨e, he1, hed, heQ⟩ := exists_fiveForm_orth_eq (k := k) hk ε (a := c + d) hcdQ d
      (d := fiveSignRep π) (fiveSignRep_ne_zero _)
    have hec : fiveForm k ε e c = 0 := by
      have h := he1
      rw [fiveForm_add_right k ε e c d, hed, add_zero] at h
      exact h
    have heQ' : fiveForm k ε e e ≠ 0 := by rw [heQ]; exact fiveSignRep_ne_zero _
    have hesq : IsSquare (fiveForm k ε e e) ↔ π = true := by
      rw [heQ]; exact isSquare_fiveSignRep_iff π
    have heW : e ∈ W := ⟨hec, hed⟩
    have hwc : fiveForm k ε (e + c) c = 0 := by
      rw [fiveForm_add_left k ε e c c, hec, hQc, add_zero]
    have hwQ : fiveForm k ε (e + c) (e + c) ≠ 0 := by
      rw [fiveForm_self_add k ε e c, hQc, hec]
      ring_nf
      exact heQ'
    have hwsq : IsSquare (fiveForm k ε (e + c) (e + c)) ↔ π = true := by
      rw [fiveForm_self_add k ε e c, hQc, hec]
      ring_nf
      exact hesq
    have hvc : fiveForm k ε v c = 0 := by
      have h := hv (e + c) hwQ hwsq hwc
      have hve : fiveForm k ε v e = 0 := by
        rw [show v = u + fiveForm k ε v d • c + fiveForm k ε v c • d by
              rw [show u = v - fiveForm k ε v d • c - fiveForm k ε v c • d from rfl]; abel,
          fiveForm_add_left, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left,
          hu0, FiveWalk.fiveForm_zero_left k ε e, zero_add, fiveForm_comm k ε c e,
          fiveForm_comm k ε d e, hec, hed, mul_zero, mul_zero, add_zero]
      have hexp : fiveForm k ε v (e + c) = fiveForm k ε v c := by
        rw [fiveForm_add_right k ε v e c, hve, zero_add]
      rwa [hexp] at h
    refine ⟨fiveForm k ε v d, ?_⟩
    conv_rhs =>
      rw [show v = u + fiveForm k ε v d • c + fiveForm k ε v c • d by
            rw [show u = v - fiveForm k ε v d • c - fiveForm k ε v c • d from rfl]; abel,
        hu0, hvc]
    try simp
  ·
    let W := fivePerpSubmodule k ε c
    let u : Fin (k + 1) → ZMod 5 := v - (fiveForm k ε v c * (fiveForm k ε c c)⁻¹) • c
    have hW : ∀ x ∈ W, (∀ y ∈ W, fiveForm k ε x y = 0) → x = 0 := by
      intro x hxW hxperp
      apply FiveWalk.fiveForm_nondegenerate k ε
      intro y
      have hyW : y - (fiveForm k ε y c * (fiveForm k ε c c)⁻¹) • c ∈ W := by
        change fiveForm k ε (y - (fiveForm k ε y c * (fiveForm k ε c c)⁻¹) • c) c = 0
        rw [fiveForm_sub_left, fiveForm_smul_left, mul_assoc, inv_mul_cancel₀ hQc, mul_one,
          sub_self]
      have hsplit : y = (y - (fiveForm k ε y c * (fiveForm k ε c c)⁻¹) • c) +
          (fiveForm k ε y c * (fiveForm k ε c c)⁻¹) • c := by abel
      rw [hsplit, fiveForm_add_right, fiveForm_smul_right, hxperp _ hyW, hxW, mul_zero, add_zero]
    have hroom : ∃ z ∈ W, fiveForm k ε u z = 0 ∧ z ≠ 0 := by
      obtain ⟨z, hz0, hz⟩ := exists_ne_zero_perp_fiveForm k ε π (m := 2) (by omega) ![c, u]
      refine ⟨z, ?_, ?_, hz0⟩
      · change fiveForm k ε z c = 0
        exact hz 0
      · rw [fiveForm_comm k ε u z]; exact hz 1
    have huW : u ∈ W := by
      change fiveForm k ε u c = 0
      rw [show u = v - (fiveForm k ε v c * (fiveForm k ε c c)⁻¹) • c from rfl,
        fiveForm_sub_left, fiveForm_smul_left, mul_assoc, inv_mul_cancel₀ hQc, mul_one,
        sub_self]
    have hu0 : u = 0 := by
      by_contra hu
      obtain ⟨w, hwW, hwQ, hwsign, huw⟩ :=
        exists_fiveForm_aniso_ne_zero_of_nondegenerate W hW hroom huW hu π
      have hw := hv w hwQ hwsign hwW
      refine huw ?_
      have h_expand : fiveForm k ε u w = fiveForm k ε v w := by
        rw [show u = v - (fiveForm k ε v c * (fiveForm k ε c c)⁻¹) • c from rfl,
          fiveForm_sub_left, fiveForm_smul_left, fiveForm_comm k ε c w, hwW]
        ring_nf
      rw [h_expand]; exact hw
    refine ⟨fiveForm k ε v c * (fiveForm k ε c c)⁻¹, ?_⟩
    conv_rhs =>
      rw [show v = u + (fiveForm k ε v c * (fiveForm k ε c c)⁻¹) • c by
            rw [show u = v - (fiveForm k ε v c * (fiveForm k ε c c)⁻¹) • c from rfl]; abel,
        hu0, zero_add]
    try simp

theorem fiveLineStab_inv_apply (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5}
    {g : GL (Fin (k + 1)) (ZMod 5)} {lam : (ZMod 5)ˣ}
    (hlam : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (lam : ZMod 5) • c) :
    (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c =
      (((lam⁻¹ : (ZMod 5)ˣ) : ZMod 5)) • c := by
  have h : (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ
        ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c) =
        (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ ((lam : ZMod 5) • c) := by
    rw [hlam]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
  have hleft : ((((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c = c := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec]
  rw [hleft] at h
  conv_rhs => rw [h]
  rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem closure_fiveReflectionsFixing_fixes (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5}
    {g : GL (Fin (k + 1)) (ZMod 5)}
    (hg : g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c)) :
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c := by
  refine Subgroup.closure_induction (k := fiveReflectionsFixing k ε π c)
    (p := fun g _ => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c)
    ?_ ?_ ?_ ?_ hg
  · intro x hx; exact hx.2
  · simp
  · intro x y hx hy ihx ihy
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ihy, ihx]
  · intro x hx ihx
    have h := congrArg (fun v => (((x⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ v) ihx
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
    exact h.symm

private theorem map_conj_le_of_mem_lineStab (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5}
    (hc : c ≠ 0) {g : GL (Fin (k + 1)) (ZMod 5)}
    (hgR : g ∈ fiveReflectionGroup k ε π) (hgline : g ∈ fiveLineStab k ε π c) :
    (Subgroup.closure (fiveReflectionsFixing k ε π c)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (fiveReflectionsFixing k ε π c) := by
  obtain ⟨lam, hlam⟩ := hgline
  have hginv := fiveLineStab_inv_apply k ε π hlam
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨r, hr, rfl⟩
  rw [mem_fiveReflectionsFixing] at hr
  obtain ⟨v, hv, hπv, rfl⟩ := exists_eq_fiveReflOf hr.1
  have hvc : fiveForm k ε v c = 0 := by
    rw [fiveForm_comm k ε v c]
    exact (fiveReflOf_mulVec_eq_self_iff hv).mp hr.2
  have hgv : fiveForm k ε (((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ v) c = 0 := by
    calc fiveForm k ε ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) c
        = fiveForm k ε ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)
            ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ
              (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) := by
          rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      _ = fiveForm k ε v ((((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) :=
          fiveForm_mulVec_of_mem hgR v _
      _ = fiveForm k ε v ((((lam⁻¹ : (ZMod 5)ˣ) : ZMod 5)) • c) := by rw [hginv]
      _ = (((lam⁻¹ : (ZMod 5)ˣ) : ZMod 5)) * fiveForm k ε v c :=
          fiveForm_smul_right k ε _ v c
      _ = 0 := by rw [hvc, mul_zero]
  change g * fiveReflOf k ε v * g⁻¹ ∈ Subgroup.closure (fiveReflectionsFixing k ε π c)
  rw [conj_fiveReflOf (fiveForm_mulVec_of_mem hgR) v]
  refine Subgroup.subset_closure ?_
  rw [mem_fiveReflectionsFixing]
  exact ⟨fiveReflOf_mem (by rw [fiveForm_mulVec_of_mem hgR v v]; exact hv)
      (by rw [fiveForm_mulVec_of_mem hgR v v]; exact hπv),
    (fiveReflOf_mulVec_eq_self_iff (by rw [fiveForm_mulVec_of_mem hgR v v]; exact hv)).mpr
      (by rw [fiveForm_comm k ε c]; exact hgv)⟩

theorem inf_lineStab_le_normalizer (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5}
    (hc : c ≠ 0) :
    fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c ≤
      fiveReflectionGroup k ε π ⊓
        Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c) : Set _) := by
  rintro g ⟨hgR, hgline⟩
  refine ⟨hgR, ?_⟩
  change g ∈ Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm (map_conj_le_of_mem_lineStab k ε π hc hgR hgline)
  intro y hy
  have h2 := map_conj_le_of_mem_lineStab k ε π hc (Subgroup.inv_mem _ hgR)
    ((fiveLineStab k ε π c).inv_mem hgline)
  have hy' : (MulAut.conj g) ((MulAut.conj g⁻¹) y) = y := by
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group
  rw [← hy']
  exact ⟨(MulAut.conj g⁻¹) y, h2 ⟨y, hy, rfl⟩, rfl⟩

theorem inf_normalizer_le_lineStab (hk : 4 ≤ k) (ε π : Bool) {c : Fin (k + 1) → ZMod 5}
    (hc : c ≠ 0) :
    fiveReflectionGroup k ε π ⊓
        Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c) : Set _) ≤
      fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c := by
  rintro g ⟨hgR, hgN⟩
  refine ⟨hgR, ?_⟩
  have hconj : ∀ x ∈ Subgroup.closure (fiveReflectionsFixing k ε π c),
      g⁻¹ * x * g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) := by
    intro x hx
    have hmap : (Subgroup.closure (fiveReflectionsFixing k ε π c)).map
        (MulAut.conj g⁻¹).toMonoidHom = Subgroup.closure (fiveReflectionsFixing k ε π c) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hgN)
    have : (MulAut.conj g⁻¹) x ∈ (Subgroup.closure (fiveReflectionsFixing k ε π c)).map
        (MulAut.conj g⁻¹).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap] at this
  have horth : ∀ w, fiveForm k ε w w ≠ 0 → (IsSquare (fiveForm k ε w w) ↔ π = true) →
      fiveForm k ε w c = 0 → fiveForm k ε (((g : Matrix (Fin (k + 1)) (Fin (k + 1))
        (ZMod 5))) *ᵥ c) w = 0 := by
    intro w hw hπ hwc
    have hgen : fiveReflOf k ε w ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) :=
      Subgroup.subset_closure
        ((fiveReflOf_mem_fiveReflectionsFixing_iff hw hπ).mpr hwc)
    have hfix : (((fiveReflOf k ε w : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ
        (((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) =
        ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c := by
      have h1 : (((g⁻¹ * fiveReflOf k ε w * g : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c = c :=
        closure_fiveReflectionsFixing_fixes k ε π (hconj _ hgen)
      calc (((fiveReflOf k ε w : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ
            (((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c)
          = ((((fiveReflOf k ε w) * g : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c := by
            rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul]
        _ = (((g * (g⁻¹ * fiveReflOf k ε w * g) : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c := by
            rw [show (fiveReflOf k ε w) * g = g * (g⁻¹ * fiveReflOf k ε w * g) by group]
        _ = (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ
              ((((g⁻¹ * fiveReflOf k ε w * g : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c) := by
            rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]
        _ = (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c := by rw [h1]
    exact (fiveReflOf_mulVec_eq_self_iff hw).mp hfix
  obtain ⟨a, ha⟩ := fiveSignPerp_span_orthogonal hk ε π hc horth
  have ha0 : a ≠ 0 := by
    intro ha0
    have hzero : ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ c = 0 := by
      rw [← ha, ha0, zero_smul]
    have h := congrArg (fun v => (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) *ᵥ v) hzero
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact hc h
  exact ⟨Units.mk0 a ha0, by rw [Units.val_mk0]; exact ha.symm⟩

theorem inf_normalizer_fiveReflectionsFixing_eq_lineStab (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) :
    fiveReflectionGroup k ε π ⊓
        Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c) : Set _) =
      fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c :=
  le_antisymm (inf_normalizer_le_lineStab hk ε π hc) (inf_lineStab_le_normalizer k ε π hc)

theorem fiveLineStabHom_ker (k : ℕ) (ε π : Bool) {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    (hS5 : ∀ g : GL (Fin (k + 1)) (ZMod 5),
      g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) ↔
        g ∈ fiveReflectionGroup k ε π ∧
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c) :
    (fiveLineStabHom k ε π c hc).ker =
      (Subgroup.closure (fiveReflectionsFixing k ε π c)).subgroupOf
        (fiveReflectionGroup k ε π ⊓ fiveLineStab k ε π c) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine (hS5 g.1).mpr ⟨g.2.1, ?_⟩
    have hspec := fiveLineStabHom_spec k ε π c hc g
    rw [h] at hspec
    simpa using hspec
  · intro h
    apply fiveLineStab_smul_unique hc
    rw [← fiveLineStabHom_spec k ε π c hc g, closure_fiveReflectionsFixing_fixes k ε π h,
      Units.val_one, one_smul]

theorem fiveLineStabHom_range_card_of_ne (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) (hQ : fiveForm k ε c c ≠ 0) :
    Nat.card (fiveLineStabHom k ε π c hc).range = 2 := by
  have hmem : ∀ x ∈ (fiveLineStabHom k ε π c hc).range, x = 1 ∨ x = -1 := by
    rintro x ⟨g, -, rfl⟩
    have hspec := fiveLineStabHom_spec k ε π c hc g
    have hthis : fiveForm k ε c c =
        (((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5) *
          ((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) * fiveForm k ε c c := by
      calc fiveForm k ε c c
          = fiveForm k ε ((g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c)
              ((g.1 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c) :=
            (fiveForm_mulVec_of_mem g.2.1 c c).symm
        _ = fiveForm k ε ((((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) • c)
              ((((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) • c) := by rw [hspec]
        _ = (((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5) *
              ((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) * fiveForm k ε c c :=
            fiveForm_smul_smul k ε _ _ c c
    have hsq : (((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5) *
        ((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) = 1 := by
      have h' : (((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5) *
          ((fiveLineStabHom k ε π c hc g : (ZMod 5)ˣ) : ZMod 5)) * fiveForm k ε c c =
          1 * fiveForm k ε c c := by rw [one_mul]; exact hthis.symm
      exact mul_right_cancel₀ hQ h'
    have hsq_units : (fiveLineStabHom k ε π c hc g) *
        (fiveLineStabHom k ε π c hc g) = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      exact hsq
    exact zmod5_units_sq_eq_one _ hsq_units
  have hneg : (-1 : (ZMod 5)ˣ) ∈ (fiveLineStabHom k ε π c hc).range := by
    have hrc : (fiveReflOf k ε c : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = -c := by
      rw [fiveReflOf_mulVec]
      have h2 : 2 * fiveForm k ε c c * (fiveForm k ε c c)⁻¹ = 2 := by
        rw [mul_assoc, mul_inv_cancel₀ hQ, mul_one]
      rw [h2, two_smul]
      abel
    by_cases hsign : IsSquare (fiveForm k ε c c) ↔ π = true
    · have hrefl : fiveReflOf k ε c ∈ fiveReflectionGroup k ε π :=
        Subgroup.subset_closure (fiveReflOf_mem hQ hsign)
      have hline : fiveReflOf k ε c ∈ fiveLineStab k ε π c :=
        ⟨-1, by rw [neg_one_units_smul]; exact hrc⟩
      refine ⟨⟨fiveReflOf k ε c, Subgroup.mem_inf.mpr ⟨hrefl, hline⟩⟩, ?_⟩
      apply fiveLineStab_smul_unique hc
      rw [← fiveLineStabHom_spec k ε π c hc, hrc, neg_one_units_smul]
    · have hsign' : IsSquare (fiveForm k ε c c) ↔ (!π) = true := by
        by_cases hs : IsSquare (fiveForm k ε c c) <;> cases π <;> simp_all
      obtain ⟨u0, hu0c, -, hu0Q⟩ := exists_fiveForm_orth_eq (k := k) hk ε (a := c) hQ c
        (d := fiveSignRep (!π)) (fiveSignRep_ne_zero _)
      have hu0Q' : fiveForm k ε u0 u0 ≠ 0 := by rw [hu0Q]; exact fiveSignRep_ne_zero _
      have hu0sq : IsSquare (fiveForm k ε u0 u0) ↔ (!π) = true := by
        rw [hu0Q]; exact isSquare_fiveSignRep_iff (!π)
      have hrc_mem : fiveReflOf k ε c ∈ fiveReflections k ε (!π) := fiveReflOf_mem hQ hsign'
      have hu0_mem : fiveReflOf k ε u0 ∈ fiveReflections k ε (!π) := fiveReflOf_mem hu0Q' hu0sq
      have hgR : fiveReflOf k ε c * fiveReflOf k ε u0 ∈ fiveReflectionGroup k ε π :=
        mul_mem_fiveReflectionGroup_of_mem_fiveReflections_not hk ε π hrc_mem hu0_mem
      have hu0fix : (fiveReflOf k ε u0 : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c :=
        (fiveReflOf_mulVec_eq_self_iff hu0Q').mpr (by rw [fiveForm_comm k ε c]; exact hu0c)
      have hgv : ((fiveReflOf k ε c * fiveReflOf k ε u0 : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = -c := by
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hu0fix, hrc]
      have hgline : fiveReflOf k ε c * fiveReflOf k ε u0 ∈ fiveLineStab k ε π c :=
        ⟨-1, by rw [neg_one_units_smul]; exact hgv⟩
      refine ⟨⟨fiveReflOf k ε c * fiveReflOf k ε u0, Subgroup.mem_inf.mpr ⟨hgR, hgline⟩⟩, ?_⟩
      apply fiveLineStab_smul_unique hc
      rw [← fiveLineStabHom_spec k ε π c hc, hgv, neg_one_units_smul]
  have hrange : (fiveLineStabHom k ε π c hc).range =
      Subgroup.closure ({(-1 : (ZMod 5)ˣ)} : Set (ZMod 5)ˣ) := by
    apply le_antisymm
    · intro x hx
      rcases hmem x hx with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro x rfl
      exact hneg
  have hcard : Nat.card (Subgroup.zpowers (-1 : (ZMod 5)ˣ)) = 2 := by
    rw [Nat.card_zpowers, orderOf_neg_one_units]
  rw [Subgroup.zpowers_eq_closure] at hcard
  rw [hrange]
  exact hcard

set_option maxHeartbeats 400000 in
theorem fiveLineStabHom_range_card_of_eq (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) (hQ : fiveForm k ε c c = 0) :
    Nat.card (fiveLineStabHom k ε π c hc).range = 4 := by
  have hy : ∃ y, fiveForm k ε c y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (FiveWalk.fiveForm_nondegenerate k ε _ h)
  obtain ⟨y, hy⟩ := hy
  let y1 : Fin (k + 1) → ZMod 5 := (fiveForm k ε c y)⁻¹ • y
  have hy1 : fiveForm k ε c y1 = 1 := by
    change fiveForm k ε c ((fiveForm k ε c y)⁻¹ • y) = 1
    rw [fiveForm_smul_right k ε ((fiveForm k ε c y)⁻¹) c y]
    exact inv_mul_cancel₀ hy
  let t : ZMod 5 := fiveForm k ε y1 y1 / 2
  let d : Fin (k + 1) → ZMod 5 := y1 - t • c
  have hd1 : fiveForm k ε c d = 1 := by
    change fiveForm k ε c (y1 - (fiveForm k ε y1 y1 / 2) • c) = 1
    rw [fiveForm_sub_right k ε c y1 ((fiveForm k ε y1 y1 / 2) • c),
      fiveForm_smul_right k ε (fiveForm k ε y1 y1 / 2) c c, hQ, mul_zero]
    exact (sub_zero (fiveForm k ε c y1)).trans hy1
  have hd0 : fiveForm k ε d d = 0 := by
    have hB : fiveForm k ε y1 c = 1 := by rw [fiveForm_comm k ε y1 c]; exact hy1
    change fiveForm k ε (y1 - (fiveForm k ε y1 y1 / 2) • c)
      (y1 - (fiveForm k ε y1 y1 / 2) • c) = 0
    rw [fiveForm_sub_sub k ε y1 ((fiveForm k ε y1 y1 / 2) • c),
      fiveForm_smul_smul k ε (fiveForm k ε y1 y1 / 2) (fiveForm k ε y1 y1 / 2) c c,
      fiveForm_smul_right k ε (fiveForm k ε y1 y1 / 2) y1 c, hQ, hB]
    simp only [mul_zero, mul_one, add_zero]
    exact sub_eq_zero.mpr (zmod5_two_div _).symm
  have hrefl_c : ∀ α : ZMod 5, α ≠ 0 →
      (fiveReflOf k ε (c - α • d) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c =
        α • d := by
    intro α hα
    rw [fiveReflOf_mulVec]
    have hBc : fiveForm k ε c (c - α • d) = -α := by
      rw [fiveForm_sub_right k ε c c (α • d), fiveForm_smul_right k ε α c d, hQ, hd1]
      exact zmod5_hBc_id α
    have hQv : fiveForm k ε (c - α • d) (c - α • d) = -2 * α := by
      rw [fiveForm_sub_sub k ε c (α • d), fiveForm_smul_smul k ε α α d d,
        fiveForm_smul_right k ε α c d, hQ, hd0, hd1]
      exact zmod5_hQv_id α
    rw [show c - (2 * fiveForm k ε c (c - α • d) * (fiveForm k ε (c - α • d) (c - α • d))⁻¹) •
        (c - α • d) = c - (2 * (-α) * (-2 * α)⁻¹) • (c - α • d) by rw [hBc, hQv]]
    have hcoef : 2 * (-α) * (-2 * α)⁻¹ = 1 := zmod5_coeff_one α hα
    rw [hcoef, one_smul]
    abel
  have hrefl_d : ∀ α : ZMod 5, α ≠ 0 →
      (fiveReflOf k ε (c - α • d) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ d =
        α⁻¹ • c := by
    intro α hα
    rw [fiveReflOf_mulVec]
    have hBd : fiveForm k ε d (c - α • d) = 1 := by
      rw [fiveForm_sub_right k ε d c (α • d), fiveForm_smul_right k ε α d d, hd0, mul_zero,
        fiveForm_comm k ε d c, hd1]
      decide
    have hQv : fiveForm k ε (c - α • d) (c - α • d) = -2 * α := by
      rw [fiveForm_sub_sub k ε c (α • d), fiveForm_smul_smul k ε α α d d,
        fiveForm_smul_right k ε α c d, hQ, hd0, hd1]
      exact zmod5_hQv_id α
    rw [show d - (2 * fiveForm k ε d (c - α • d) * (fiveForm k ε (c - α • d) (c - α • d))⁻¹) •
        (c - α • d) = d - (2 * 1 * (-2 * α)⁻¹) • (c - α • d) by rw [hBd, hQv]]
    have hcoef : 2 * 1 * (-2 * α)⁻¹ = -α⁻¹ := zmod5_coeff_inv α hα
    rw [hcoef]
    exact zmod5_vec_reflect k c d α hα
  have hcdQ : fiveForm k ε (c + d) (c + d) ≠ 0 := by
    rw [fiveForm_self_add k ε c d, hQ, hd0, hd1]
    decide
  obtain ⟨e, he1, hed, heQ⟩ := exists_fiveForm_orth_eq (k := k) hk ε (a := c + d) hcdQ d
    (d := fiveSignRep (!π)) (fiveSignRep_ne_zero _)
  have hec : fiveForm k ε e c = 0 := by
    have h := he1
    rw [fiveForm_add_right k ε e c d, hed, add_zero] at h
    exact h
  have heQ' : fiveForm k ε e e ≠ 0 := by rw [heQ]; exact fiveSignRep_ne_zero _
  have hesq : IsSquare (fiveForm k ε e e) ↔ (!π) = true := by
    rw [heQ]; exact isSquare_fiveSignRep_iff (!π)
  have hemem : fiveReflOf k ε e ∈ fiveReflections k ε (!π) := fiveReflOf_mem heQ' hesq
  have hefix : (fiveReflOf k ε e : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c :=
    (fiveReflOf_mulVec_eq_self_iff heQ').mpr (by rw [fiveForm_comm k ε c e]; exact hec)
  have hQt : ∀ α : ZMod 5, fiveForm k ε (c - α • d) (c - α • d) = -2 * α := by
    intro α
    rw [fiveForm_sub_sub k ε c (α • d), fiveForm_smul_smul k ε α α d d,
      fiveForm_smul_right k ε α c d, hQ, hd0, hd1]
    exact zmod5_hQv_id α
  have hx_c : (fiveReflOf k ε (c - d) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c =
      d := by
    have := hrefl_c 1 (by decide)
    simpa using this
  have hx_d : (fiveReflOf k ε (c - d) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ d =
      c := by
    have := hrefl_d 1 (by decide)
    simpa using this
  have hy_c : (fiveReflOf k ε (c - (3 : ZMod 5) • d) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (3 : ZMod 5) • d :=
    hrefl_c (3 : ZMod 5) (by decide)
  have hy_d : (fiveReflOf k ε (c - (3 : ZMod 5) • d) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ d = (2 : ZMod 5) • c :=
    (hrefl_d (3 : ZMod 5) (by decide)).trans (by rw [zmod5_inv_three])
  have hxQt' : fiveForm k ε (c - d) (c - d) = -2 := by
    have := hQt (1 : ZMod 5); simpa using this
  have hxQt : fiveForm k ε (c - d) (c - d) = 3 := hxQt'.trans (by decide)
  have hyQt' : fiveForm k ε (c - (3 : ZMod 5) • d) (c - (3 : ZMod 5) • d) = -2 * 3 := by
    have := hQt (3 : ZMod 5); simpa using this
  have hyQt : fiveForm k ε (c - (3 : ZMod 5) • d) (c - (3 : ZMod 5) • d) = 4 :=
    hyQt'.trans (by decide)
  have huns : ∃ u ∈ (fiveLineStabHom k ε π c hc).range, ¬ IsSquare (u : ZMod 5) := by
    by_cases hπ : π = true
    · have hxmem : fiveReflOf k ε (c - d) ∈ fiveReflections k ε (!π) := by
        refine fiveReflOf_mem (by rw [hxQt]; decide) ?_
        rw [hxQt, hπ]; decide
      have hymem : fiveReflOf k ε (c - (3 : ZMod 5) • d) ∈ fiveReflections k ε π := by
        refine fiveReflOf_mem (by rw [hyQt]; decide) ?_
        rw [hyQt, hπ]; decide
      have hprod : fiveReflOf k ε e * fiveReflOf k ε (c - d) ∈ fiveReflectionGroup k ε π :=
        mul_mem_fiveReflectionGroup_of_mem_fiveReflections_not hk ε π hemem hxmem
      have hgR : (fiveReflOf k ε e * fiveReflOf k ε (c - d)) *
          fiveReflOf k ε (c - (3 : ZMod 5) • d) ∈ fiveReflectionGroup k ε π :=
        Subgroup.mul_mem _ hprod (Subgroup.subset_closure hymem)
      have hgc : (((fiveReflOf k ε e * fiveReflOf k ε (c - d)) *
          fiveReflOf k ε (c - (3 : ZMod 5) • d) : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (3 : ZMod 5) • c := by
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy_c, Matrix.mulVec_smul, hx_d,
          Matrix.mulVec_smul, hefix]
      have hline : (fiveReflOf k ε e * fiveReflOf k ε (c - d)) *
          fiveReflOf k ε (c - (3 : ZMod 5) • d) ∈ fiveLineStab k ε π c :=
        ⟨Units.mk0 (3 : ZMod 5) (by decide), by rw [Units.val_mk0]; exact hgc⟩
      refine ⟨Units.mk0 (3 : ZMod 5) (by decide),
        ⟨⟨(fiveReflOf k ε e * fiveReflOf k ε (c - d)) *
          fiveReflOf k ε (c - (3 : ZMod 5) • d), hgR, hline⟩, ?_⟩, by decide⟩
      apply fiveLineStab_smul_unique hc
      rw [← fiveLineStabHom_spec k ε π c hc, hgc, Units.val_mk0]
    · have hπf : π = false := by cases π <;> simp_all
      have hxmem : fiveReflOf k ε (c - d) ∈ fiveReflections k ε π := by
        refine fiveReflOf_mem (by rw [hxQt]; decide) ?_
        rw [hxQt, hπf]; decide
      have hymem : fiveReflOf k ε (c - (3 : ZMod 5) • d) ∈ fiveReflections k ε (!π) := by
        refine fiveReflOf_mem (by rw [hyQt]; decide) ?_
        rw [hyQt, hπf]; decide
      have hprod : fiveReflOf k ε e * fiveReflOf k ε (c - (3 : ZMod 5) • d) ∈
          fiveReflectionGroup k ε π :=
        mul_mem_fiveReflectionGroup_of_mem_fiveReflections_not hk ε π hemem hymem
      have hgR : (fiveReflOf k ε e * fiveReflOf k ε (c - (3 : ZMod 5) • d)) *
          fiveReflOf k ε (c - d) ∈ fiveReflectionGroup k ε π :=
        Subgroup.mul_mem _ hprod (Subgroup.subset_closure hxmem)
      have hgc : (((fiveReflOf k ε e * fiveReflOf k ε (c - (3 : ZMod 5) • d)) *
          fiveReflOf k ε (c - d) : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = (2 : ZMod 5) • c := by
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx_c, hy_d, Matrix.mulVec_smul, hefix]
      have hline : (fiveReflOf k ε e * fiveReflOf k ε (c - (3 : ZMod 5) • d)) *
          fiveReflOf k ε (c - d) ∈ fiveLineStab k ε π c :=
        ⟨Units.mk0 (2 : ZMod 5) (by decide), by rw [Units.val_mk0]; exact hgc⟩
      refine ⟨Units.mk0 (2 : ZMod 5) (by decide),
        ⟨⟨(fiveReflOf k ε e * fiveReflOf k ε (c - (3 : ZMod 5) • d)) *
          fiveReflOf k ε (c - d), hgR, hline⟩, ?_⟩, by decide⟩
      apply fiveLineStab_smul_unique hc
      rw [← fiveLineStabHom_spec k ε π c hc, hgc, Units.val_mk0]
  obtain ⟨u, hu, hnonsq⟩ := huns
  have h4 : 4 ≤ Nat.card (fiveLineStabHom k ε π c hc).range := by
    have hle := Subgroup.card_le_of_le (H := Subgroup.zpowers u)
      (K := (fiveLineStabHom k ε π c hc).range) (Subgroup.zpowers_le.mpr hu)
    rwa [Nat.card_zpowers, orderOf_eq_four_of_not_isSquare u hnonsq] at hle
  have hle4 : Nat.card (fiveLineStabHom k ε π c hc).range ≤ 4 := by
    have := Subgroup.card_le_card_group (H := (fiveLineStabHom k ε π c hc).range)
    rwa [natCard_units_five] at this
  omega

theorem relIndex_normalizer_fiveReflectionsFixing_aux (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0)
    (hS5 : ∀ g : GL (Fin (k + 1)) (ZMod 5),
      g ∈ Subgroup.closure (fiveReflectionsFixing k ε π c) ↔
        g ∈ fiveReflectionGroup k ε π ∧
          (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c = c) :
    (Subgroup.closure (fiveReflectionsFixing k ε π c)).relIndex
        (fiveReflectionGroup k ε π ⊓
          Subgroup.normalizer (Subgroup.closure (fiveReflectionsFixing k ε π c) : Set _)) =
      if fiveForm k ε c c = 0 then 4 else 2 := by
  rw [inf_normalizer_fiveReflectionsFixing_eq_lineStab hk ε π hc]
  have hker := fiveLineStabHom_ker k ε π hc hS5
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  by_cases hQ : fiveForm k ε c c = 0
  · rw [if_pos hQ, fiveLineStabHom_range_card_of_eq hk ε π hc hQ]
  · rw [if_neg hQ, fiveLineStabHom_range_card_of_ne hk ε π hc hQ]

end CFSG.OddTranspositions.PartThree
