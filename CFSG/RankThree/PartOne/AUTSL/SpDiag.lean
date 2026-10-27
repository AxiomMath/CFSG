module

public import CFSG.RankThree.PartOne.AUTSL.DiagCore
public import CFSG.RankThree.PartOne.AUTSL.SpWeights

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Sp

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {E : Type*} [CommGroup E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP K 2] in
theorem mult_le_inv (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] (ιB : B →* E)
    (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hrel : ∀ b : B, Q * diagOf f (ιB b) =
      Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K))⁻¹) * Q) (χ : B →* Kˣ) :
    mult (fun i => (f i).comp ιB) χ ≤ mult (fun i => (f i).comp ιB) χ⁻¹ := by
  have : Fintype K := Fintype.ofFinite K
  let d : B → Matrix ι ι K := fun b => diagOf f (ιB b)
  let d' : B → Matrix ι ι K := fun b =>
    Matrix.diagonal fun i => (((f i (ιB b) : Kˣ) : K))⁻¹
  have key := card_le_of_semilinear d d' (fun b => Matrix.isDiag_diagonal _)
    (fun b => Matrix.isDiag_diagonal _) (RingHom.id K) Q hQ (fun b => b) Function.surjective_id
    (fun b => by simpa [d, d'] using hrel b) (fun b => ((χ b : Kˣ) : K))
    (fun b => ((χ b : Kˣ) : K)) (fun b => rfl)
  unfold mult
  have h1 : (Finset.univ.filter fun i : ι => (fun i => (f i).comp ιB) i = χ) =
      Finset.univ.filter fun i : ι => ∀ b, d b i i = ((χ b : Kˣ) : K) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h b
      have := congrArg (fun φ : B →* Kˣ => ((φ b : Kˣ) : K)) h
      simpa [d, diagOf] using this
    · intro h
      ext b
      simpa [d, diagOf] using h b
  have h2 : (Finset.univ.filter fun i : ι => (fun i => (f i).comp ιB) i = χ⁻¹) =
      Finset.univ.filter fun i : ι => ∀ b, d' b i i = ((χ b : Kˣ) : K) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h b
      have := congrArg (fun φ : B →* Kˣ => ((φ b : Kˣ) : K)) h
      simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this
      simp only [d', Matrix.diagonal_apply_eq, this, inv_inv]
    · intro h
      ext b
      have := h b
      simp only [d', Matrix.diagonal_apply_eq] at this
      simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      rw [← this, inv_inv]
  rw [h1, h2]
  exact key

theorem weights_of_relation_sp (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hcard : Fintype.card ι = 6) (hB25 : Nat.card B = 25)
    (hB5 : ∀ b : B, b ^ 5 = 1) (hfaith : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1)
    (θ : MulAut B) (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1) (j e : ℕ) (he : e = 1 ∨ e = 4)
    (A : Matrix ι ι K) (hA : IsUnit A)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB (θ b)) * A) (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQrel : ∀ b : B, Q * diagOf f (ιB b) =
      Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K))⁻¹) * Q) :
    Function.Injective (fun i => (f i).comp ιB) ∧
      ∃ χ₀ : B →* Kˣ, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range (fun i => (f i).comp ιB) ∧
        ∀ ψ ∈ Set.range (fun i => (f i).comp ιB),
          ψ = χ₀ ∨ ψ = twist θ (e * 2 ^ j) χ₀ ∨ ψ = twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀) ∨
          ψ = χ₀⁻¹ ∨ ψ = (twist θ (e * 2 ^ j) χ₀)⁻¹ ∨
          ψ = (twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀))⁻¹ := by
  have hnorm : ∀ b, b * θ b * θ (θ b) = 1 := norm_eq_one_of_order_three hB25 θ hθ3 hθ1
  have hθ3' : ∀ b, θ (θ (θ b)) = b := theta_cube θ hnorm
  have hm : ¬ 5 ∣ e * 2 ^ j := not_dvd_five_mul j e he
  have he5 : ¬ 5 ∣ e := fun h => hm (h.mul_right _)
  have hf1 : ∃ i, (f i).comp ιB ≠ 1 := by
    have : Nontrivial B := (Finite.one_lt_card_iff_nontrivial).1 (by rw [hB25]; norm_num)
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    by_contra hall
    push Not at hall
    exact hb (hfaith b fun i => by
      have := congrArg (fun φ : B →* Kˣ => φ b) (hall i)
      simpa using this)
  have H1 := mult_le_twist f ιB hB5 θ hθ3' j e he5 A hA hrel
  have H2 := mult_le_inv f ιB Q hQ hQrel
  exact sp_weight_lemma hB5 θ hnorm (fun i => (f i).comp ιB) hcard (e * 2 ^ j) hm hf1 H1 H2

omit [Finite K] [CharP K 2] in
theorem diag_core_sp (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hE5 : ∀ x : E, x ^ 5 = 1) (hinj : Function.Injective fun i => (f i).comp ιB)
    (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQE : ∀ g : E, Q * diagOf f g = Matrix.diagonal (fun i => (((f i g : Kˣ) : K))⁻¹) * Q)
    (j e : ℕ) (hm : (e * 2 ^ j) % 5 = 4) (A : Matrix ι ι K)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB b) * A) (e₀ : E) :
    A * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e) ^ 2 ^ j) = diagOf f e₀ * A := by
  have hpow : ∀ (x : E) (i : ι), (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j = (((f i x : Kˣ) : K))⁻¹ := by
    intro x i
    have h5 : ((f i x : Kˣ) : K) ^ 5 = 1 := by
      have := congrArg (fun y : Kˣ => (y : K))
        (show (f i x) ^ 5 = 1 by rw [← map_pow, hE5 x, map_one])
      simpa using this
    rw [← pow_mul, pow_eq_pow_mod _ h5, hm]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h5)).symm
  have hdiagfun : ∀ x : E, Matrix.diagonal (fun i => (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j) =
      Matrix.diagonal (fun i => (((f i x : Kˣ) : K))⁻¹) := fun x => by simp only [hpow]
  have hΔ : ∀ b : B, (A * Q) * diagOf f (ιB b) = diagOf f (ιB b) * (A * Q) := fun b => by
    have h1 := hrel b
    rw [hdiagfun] at h1
    calc A * Q * diagOf f (ιB b) = A * (Q * diagOf f (ιB b)) := by rw [Matrix.mul_assoc]
      _ = A * (Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K))⁻¹) * Q) := by
          rw [hQE (ιB b)]
      _ = (A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K))⁻¹)) * Q := by
          rw [← Matrix.mul_assoc]
      _ = (diagOf f (ιB b) * A) * Q := by rw [h1]
      _ = diagOf f (ιB b) * (A * Q) := by rw [Matrix.mul_assoc]
  have hdiag := isDiag_of_commute f ιB hinj (A * Q) hΔ
  have h2 : (A * Q) * diagOf f e₀ = diagOf f e₀ * (A * Q) := by
    obtain ⟨d, hd⟩ : ∃ d : ι → K, A * Q = Matrix.diagonal d :=
      ⟨(A * Q).diag, hdiag.diagonal_diag.symm⟩
    rw [hd]
    simp only [diagOf, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hdiagfun]
  refine (hQ.mul_left_inj).1 ?_
  calc A * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K))⁻¹) * Q
      = A * (Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K))⁻¹) * Q) := by
        rw [Matrix.mul_assoc]
    _ = A * (Q * diagOf f e₀) := by rw [hQE e₀]
    _ = (A * Q) * diagOf f e₀ := by rw [Matrix.mul_assoc]
    _ = diagOf f e₀ * (A * Q) := h2
    _ = (diagOf f e₀ * A) * Q := by rw [Matrix.mul_assoc]

theorem fixes_of_relation_sp (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hB5 : ∀ b : B, b ^ 5 = 1)
    (hE5 : ∀ x : E, x ^ 5 = 1) (θ : MulAut B) (hnorm : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ)
    (hm : ¬ 5 ∣ m) (hinj : Function.Injective fun i => (f i).comp ιB) {χ₀ : B →* Kˣ}
    (hχ₀ : χ₀ ≠ 1) (h0 : χ₀ ∈ Set.range (fun i => (f i).comp ιB))
    (hall : ∀ ψ ∈ Set.range (fun i => (f i).comp ιB),
      ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨ ψ = twist θ m (twist θ m χ₀) ∨ ψ = χ₀⁻¹ ∨
        ψ = (twist θ m χ₀)⁻¹ ∨ ψ = (twist θ m (twist θ m χ₀))⁻¹)
    (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQE : ∀ g : E, Q * diagOf f g = Matrix.diagonal (fun i => (((f i g : Kˣ) : K))⁻¹) * Q)
    (l e' : ℕ) (he' : e' = 1 ∨ e' = 4) (A' : Matrix ι ι K) (hA' : IsUnit A')
    (hrel : ∀ b : B, A' * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A') (e₀ : E) :
    A' * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e') ^ 2 ^ l) = diagOf f e₀ * A' := by
  have hm' : ¬ 5 ∣ e' * 2 ^ l := not_dvd_five_mul l e' he'
  have he5 : ¬ 5 ∣ e' := fun h => hm' (h.mul_right _)
  have H := mult_le_twist f ιB hB5 (MulEquiv.refl B) (fun b => rfl) l e' he5 A' hA' hrel
  have hH' : ∀ χ : B →* Kˣ, mult (fun i => (f i).comp ιB) χ ≤
      mult (fun i => (f i).comp ιB) (χ ^ (e' * 2 ^ l)) := fun χ => by
    have := H χ
    rwa [twist_refl_eq_pow] at this
  have hscalar := sp_scalar_lemma hB5 θ hnorm (fun i => (f i).comp ιB) m hm hχ₀ h0 hall
    (e' * 2 ^ l) hm' hH'
  rcases hscalar with h1 | h4
  · exact diag_core_II f ιB hE5 hinj l e' h1 A' hrel e₀
  · exact diag_core_sp f ιB hE5 hinj Q hQ hQE l e' h4 A' hrel e₀

end Sp

end CFSG.RankThree.PartOne.AUTSL
