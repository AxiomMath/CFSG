module

public import CFSG.Quasithin.Vol2.KGFactSLnTwo

public section

namespace CFSG.Quasithin.SLnTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm

variable {n : ℕ}

theorem additive_single {M : Type*} [AddCommGroup M] (φ : (Fin n → ZMod 2) →+ M) (j : Fin n)
    (c : ZMod 2) : φ (Pi.single j c) = if c = 1 then φ (Pi.single j 1) else 0 := by
  rcases zmod_two_cases c with rfl | rfl <;> simp

@[expose] def matOf (φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => φ (Pi.single j 1) i

theorem matOf_mulVec (φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    matOf φ *ᵥ x = φ x := by
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  ext i
  simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases zmod_two_cases (x j) with h | h
  · rw [h]
    simp
  · rw [h]
    simp

theorem matrix_ext_mulVec {B C : Matrix (Fin n) (Fin n) (ZMod 2)} (h : ∀ x, B *ᵥ x = C *ᵥ x) :
    B = C := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem vec_ext_dot {u w : Fin n → ZMod 2} (h : ∀ x, u ⬝ᵥ x = w ⬝ᵥ x) : u = w := by
  ext i
  have := h (Pi.single i 1)
  simpa using this

theorem additive_eq_zero_or_id {φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)}
    (h : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
      φ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ φ x) :
    φ = 0 ∨ φ = AddMonoidHom.id _ := by
  have hc : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2),
      matOf φ * (g : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) * matOf φ := by
    intro g
    refine matrix_ext_mulVec fun x => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matOf_mulVec, matOf_mulVec, h]
  rcases eq_zero_or_one_of_commute hc with h0 | h1
  · left
    refine AddMonoidHom.ext fun x => ?_
    rw [← matOf_mulVec, h0, Matrix.zero_mulVec]
    rfl
  · right
    refine AddMonoidHom.ext fun x => ?_
    rw [← matOf_mulVec, h1, Matrix.one_mulVec]
    rfl

theorem additive_twisted_eq_zero (hn : 3 ≤ n) {φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)}
    (h : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
      φ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
        (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ φ x) : φ = 0 := by
  by_cases hker : ∃ x, x ≠ 0 ∧ φ x = 0
  · obtain ⟨x, hx, hφx⟩ := hker
    obtain ⟨g₁, hg₁⟩ := exists_mulVec_eq (by omega) hx
    refine AddMonoidHom.ext fun y => ?_
    by_cases hy : y = 0
    · rw [hy, map_zero]
      rfl
    obtain ⟨g₂, hg₂⟩ := exists_mulVec_eq (by omega) hy
    have hxy : ((g₂ * g₁⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = y := by
      rw [← hg₁, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        coe_inv_mul, Matrix.mul_one, hg₂]
    rw [← hxy, h, hφx, Matrix.mulVec_zero]
    rfl
  ·
    exfalso
    have hinj : ∀ x, matOf φ *ᵥ x = 0 → x = 0 := by
      intro x hx
      by_contra hx0
      exact hker ⟨x, hx0, by rw [← matOf_mulVec]; exact hx⟩
    have hdet : (matOf φ).det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      exact hv (hinj v hv0)
    let A : GL (Fin n) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' (matOf φ)
      (isUnit_iff_ne_zero.2 hdet)
    obtain ⟨g, hg⟩ := graph_ne_conj hn A
    apply hg
    apply Subtype.ext
    rw [coe_slConjugation]
    have hc : matOf φ * (g : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) * matOf φ := by
      refine matrix_ext_mulVec fun x => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matOf_mulVec, matOf_mulVec, h]
    have hA : (A : Matrix (Fin n) (Fin n) (ZMod 2)) = matOf φ := rfl
    rw [hA, hc, Matrix.mul_assoc, ← hA, Units.mul_inv, Matrix.mul_one]

theorem pairing_eq_zero_or_dot {P : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
    (hP₁ : ∀ x x' z, P (x + x') z = P x z + P x' z) (hP₂ : ∀ x z z', P x (z + z') = P x z + P x z')
    (hinv : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) x z,
      P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
        ((slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) = P x z) :
    (∀ x z, P x z = 0) ∨ (∀ x z, P x z = z ⬝ᵥ x) := by
  let ψ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun z j => P (Pi.single j 1) z) fun z z' => by
      ext j
      exact hP₂ _ z z'
  have hψ : ∀ x z, P x z = ψ z ⬝ᵥ x := by
    intro x z
    let f : (Fin n → ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun x => P x z) fun x x' => hP₁ x x' z
    have e : P x z = ∑ j, f (Pi.single j (x j)) := by
      change f x = _
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
    rw [e, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases zmod_two_cases (x j) with h | h
    · rw [h]
      simp
    · rw [h]
      simp [f, ψ]
  have hcomm : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) z,
      ψ ((slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) =
        (slGraphAut n (ZMod 2) g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ψ z := by
    intro g z
    refine vec_ext_dot fun x => ?_
    rw [← hψ]
    have e1 : x = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, coe_mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e1]
    rw [hinv, hψ, slGraphAut_matrix, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hsurj : Function.Surjective (slGraphAut n (ZMod 2)) := (slGraphAut n (ZMod 2)).surjective
  rcases additive_eq_zero_or_id (φ := ψ) (fun g x => by
    obtain ⟨g', rfl⟩ := hsurj g
    exact hcomm g' x) with h0 | h1
  · left
    intro x z
    rw [hψ, h0]
    simp
  · right
    intro x z
    rw [hψ, h1]
    rfl

end CFSG.Quasithin.SLnTwo
