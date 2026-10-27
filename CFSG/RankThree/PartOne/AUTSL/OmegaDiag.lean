module

public import CFSG.RankThree.PartOne.AUTSL.SpDiag
public import CFSG.RankThree.PartOne.AUTSL.OmegaWeights
public import CFSG.RankThree.PartOne.AUTSL.FieldExt

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Cls

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {E : Type*} [CommGroup E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Finite K] [CharP K 2] [DecidableEq ι] in
theorem diag_vec_mem_span_cls (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E) (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
    (fun i => ((f i e₀ : Kˣ) : K)) ∈
      Submodule.span K (Set.range fun b : B => fun i => ((f i (ιB b) : Kˣ) : K)) := by
  let κ : Type _ := Set.range (fun i => (f i).comp ιB)
  have : Finite κ := Set.finite_range _
  have : Fintype κ := Fintype.ofFinite κ
  have hrep : ∀ χ : κ, ∃ i, (f i).comp ιB = χ.1 := fun χ => by
    obtain ⟨i, hi⟩ := χ.2
    exact ⟨i, hi⟩
  let rep : κ → ι := fun χ => Classical.choose (hrep χ)
  have hrep_spec : ∀ χ : κ, (f (rep χ)).comp ιB = χ.1 := fun χ => Classical.choose_spec (hrep χ)
  let f' : κ → (E →* Kˣ) := fun χ => f (rep χ)
  have hinj' : Function.Injective fun χ : κ => (f' χ).comp ιB := fun χ χ' h =>
    Subtype.ext (by rw [← hrep_spec χ, ← hrep_spec χ']; exact h)
  let g : ι → κ := fun i => ⟨(f i).comp ιB, ⟨i, rfl⟩⟩
  let Φ : (κ → K) →ₗ[K] (ι → K) := LinearMap.funLeft K K g
  have hκ := diag_vec_mem_span f' ιB hinj' e₀
  have hmem := Submodule.mem_map_of_mem (f := Φ) hκ
  rw [Submodule.map_span] at hmem
  have hu : Φ (fun χ => ((f' χ e₀ : Kˣ) : K)) = fun i => ((f i e₀ : Kˣ) : K) := by
    funext i
    have := hcls (rep (g i)) i (hrep_spec (g i))
    show ((f (rep (g i)) e₀ : Kˣ) : K) = _
    rw [this]
  have himg : Φ '' Set.range (fun b : B => fun χ : κ => ((f' χ (ιB b) : Kˣ) : K)) ⊆
      Set.range fun b : B => fun i => ((f i (ιB b) : Kˣ) : K) := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    funext i
    show ((f i (ιB b) : Kˣ) : K) = ((f (rep (g i)) (ιB b) : Kˣ) : K)
    exact congrArg (fun φ : B →* Kˣ => ((φ b : Kˣ) : K)) (hrep_spec (g i)).symm
  rw [hu] at hmem
  exact Submodule.span_mono himg hmem

omit [Finite K] [CharP K 2] in
theorem diag_mem_span_cls (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E) (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
    diagOf f e₀ ∈ Submodule.span K (Set.range fun b : B => diagOf f (ιB b)) := by
  have hu := diag_vec_mem_span_cls f ιB e₀ hcls
  have := Submodule.mem_map_of_mem (f := Matrix.diagonalLinearMap ι K K) hu
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

omit [Finite K] [CharP K 2] in
theorem blockDiag_of_commute (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (A : Matrix ι ι K) (h : ∀ b : B, A * diagOf f (ιB b) = diagOf f (ιB b) * A) :
    ∀ i k, (f i).comp ιB ≠ (f k).comp ιB → A i k = 0 := by
  intro i k hik
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b : B, f i (ιB b) ≠ f k (ιB b) := by
    by_contra hall
    push Not at hall
    exact hik (MonoidHom.ext fun b => hall b)
  have h1 := congrFun (congrFun (h b) i) k
  simp only [diagOf, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : A i k * (((f k (ιB b) : Kˣ) : K) - ((f i (ιB b) : Kˣ) : K)) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hne h3
  · exact hb (Units.ext (sub_eq_zero.1 h3).symm)

omit [Finite K] [CharP K 2] in
theorem commute_diagOf_of_cls (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (A : Matrix ι ι K) (hA : ∀ i k, (f i).comp ιB ≠ (f k).comp ιB → A i k = 0) (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
    A * diagOf f e₀ = diagOf f e₀ * A := by
  ext i k
  simp only [diagOf, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : (f i).comp ιB = (f k).comp ιB
  · rw [hcls i k h]
    exact mul_comm _ _
  · rw [hA i k h]
    simp

omit [Finite K] [CharP K 2] in
theorem diag_core_II_cls (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hE5 : ∀ x : E, x ^ 5 = 1) (j e : ℕ) (hm : (e * 2 ^ j) % 5 = 1) (A : Matrix ι ι K)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB b) * A) (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
    A * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e) ^ 2 ^ j) = diagOf f e₀ * A := by
  have hpow : ∀ (x : E) (i : ι), (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j = ((f i x : Kˣ) : K) := by
    intro x i
    have h5 : ((f i x : Kˣ) : K) ^ 5 = 1 := by
      have := congrArg (fun y : Kˣ => (y : K))
        (show (f i x) ^ 5 = 1 by rw [← map_pow, hE5 x, map_one])
      simpa using this
    rw [← pow_mul, pow_eq_pow_mod _ h5, hm, pow_one]
  have hdiagfun : ∀ x : E, Matrix.diagonal (fun i => (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f x := fun x => by simp only [hpow, diagOf]
  have hB : ∀ b : B, A * diagOf f (ιB b) = diagOf f (ιB b) * A := fun b => by
    have := hrel b
    rwa [hdiagfun] at this
  rw [hdiagfun]
  exact commute_diagOf_of_cls f ιB A (blockDiag_of_commute f ιB A hB) e₀ hcls

omit [Finite K] [CharP K 2] in
theorem diag_core_sp_cls (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hE5 : ∀ x : E, x ^ 5 = 1) (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQE : ∀ g : E, Q * diagOf f g = Matrix.diagonal (fun i => (((f i g : Kˣ) : K))⁻¹) * Q)
    (j e : ℕ) (hm : (e * 2 ^ j) % 5 = 4) (A : Matrix ι ι K)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB b) * A) (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
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
  have hcomm := commute_diagOf_of_cls f ιB (A * Q) (blockDiag_of_commute f ιB (A * Q) hΔ) e₀ hcls
  rw [hdiagfun]
  refine (hQ.mul_left_inj).1 ?_
  calc A * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K))⁻¹) * Q
      = A * (Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K))⁻¹) * Q) := by
        rw [Matrix.mul_assoc]
    _ = A * (Q * diagOf f e₀) := by rw [hQE e₀]
    _ = (A * Q) * diagOf f e₀ := by rw [Matrix.mul_assoc]
    _ = diagOf f e₀ * (A * Q) := hcomm
    _ = (diagOf f e₀ * A) * Q := by rw [Matrix.mul_assoc]

theorem weights_of_relation_omega (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hcard : Fintype.card ι = 8) (hB25 : Nat.card B = 25)
    (hB5 : ∀ b : B, b ^ 5 = 1) (hfaith : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1)
    (θ : MulAut B) (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1) (j e : ℕ) (he : e = 1 ∨ e = 4)
    (A : Matrix ι ι K) (hA : IsUnit A)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB (θ b)) * A) (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQrel : ∀ b : B, Q * diagOf f (ιB b) =
      Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K))⁻¹) * Q) :
    ∃ χ₀ : B →* Kˣ, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range (fun i => (f i).comp ιB) ∧
      twist θ (e * 2 ^ j) χ₀ ∈ Set.range (fun i => (f i).comp ιB) ∧
      twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀) ∈ Set.range (fun i => (f i).comp ιB) ∧
      (∀ ψ ∈ Set.range (fun i => (f i).comp ιB), ψ ≠ 1 →
        ψ = χ₀ ∨ ψ = twist θ (e * 2 ^ j) χ₀ ∨ ψ = twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀) ∨
        ψ = χ₀⁻¹ ∨ ψ = (twist θ (e * 2 ^ j) χ₀)⁻¹ ∨
        ψ = (twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀))⁻¹) ∧
      (∀ i k, (f i).comp ιB = (f k).comp ιB → (f i).comp ιB ≠ 1 → i = k) ∧
      (Finset.univ.filter fun i => (f i).comp ιB = 1).card = 2 := by
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
  exact omega_weight_lemma hB5 θ hnorm (fun i => (f i).comp ιB) hcard (e * 2 ^ j) hm hf1 H1 H2

theorem fixes_of_relation_omega (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hB5 : ∀ b : B, b ^ 5 = 1) (hE5 : ∀ x : E, x ^ 5 = 1) (θ : MulAut B)
    (hnorm : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ) (hm : ¬ 5 ∣ m) {χ₀ : B →* Kˣ}
    (hχ₀ : χ₀ ≠ 1) (h0 : χ₀ ∈ Set.range (fun i => (f i).comp ιB))
    (hall : ∀ ψ ∈ Set.range (fun i => (f i).comp ιB), ψ ≠ 1 →
      ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨ ψ = twist θ m (twist θ m χ₀) ∨ ψ = χ₀⁻¹ ∨
        ψ = (twist θ m χ₀)⁻¹ ∨ ψ = (twist θ m (twist θ m χ₀))⁻¹)
    (Q : Matrix ι ι K) (hQ : IsUnit Q)
    (hQE : ∀ g : E, Q * diagOf f g = Matrix.diagonal (fun i => (((f i g : Kˣ) : K))⁻¹) * Q)
    (l e' : ℕ) (he' : e' = 1 ∨ e' = 4) (A' : Matrix ι ι K) (hA' : IsUnit A')
    (hrel : ∀ b : B, A' * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A') (e₀ : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i e₀ = f k e₀) :
    A' * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e') ^ 2 ^ l) = diagOf f e₀ * A' := by
  have hm' : ¬ 5 ∣ e' * 2 ^ l := not_dvd_five_mul l e' he'
  have he5 : ¬ 5 ∣ e' := fun h => hm' (h.mul_right _)
  have H := mult_le_twist f ιB hB5 (MulEquiv.refl B) (fun b => rfl) l e' he5 A' hA' hrel
  have hH' : ∀ χ : B →* Kˣ, mult (fun i => (f i).comp ιB) χ ≤
      mult (fun i => (f i).comp ιB) (χ ^ (e' * 2 ^ l)) := fun χ => by
    have := H χ
    rwa [twist_refl_eq_pow] at this
  have hscalar := omega_scalar_lemma hB5 θ hnorm (fun i => (f i).comp ιB) m hm hχ₀ h0 hall
    (e' * 2 ^ l) hm' hH'
  rcases hscalar with h1 | h4
  · exact diag_core_II_cls f ιB hE5 l e' h1 A' hrel e₀ hcls
  · exact diag_core_sp_cls f ιB hE5 Q hQ hQE l e' h4 A' hrel e₀ hcls

end Cls

section Stable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K K' : Type*} [Field K] [Field K']
  [Algebra K K'] {E B : Type*} [CommGroup E] [Group B]

theorem rho_mem_span_cls (ρ : E →* Matrix ι ι K) (ιB : B →* E) (P : GL ι K')
    (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = diagOf f g) (g : E)
    (hcls : ∀ i k, (f i).comp ιB = (f k).comp ιB → f i g = f k g) :
    ρ g ∈ Submodule.span K (Set.range fun b : B => ρ (ιB b)) := by
  have hspan := diag_mem_span_cls f ιB g hcls
  have hPiP : ((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  let Cj : Matrix ι ι K' →ₗ[K'] Matrix ι ι K' :=
    (LinearMap.mulLeft K' ((P⁻¹ : GL ι K') : Matrix ι ι K')).comp
      (LinearMap.mulRight K' (P : Matrix ι ι K'))
  have hCj : ∀ z : E, Cj (diagOf f z) = (ρ z).map (algebraMap K K') := fun z => by
    have hz : diagOf f z = (P : Matrix ι ι K') * (ρ z).map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K') := (hD z).symm
    show ((P⁻¹ : GL ι K') : Matrix ι ι K') * (diagOf f z * (P : Matrix ι ι K')) = _
    rw [hz]
    calc ((P⁻¹ : GL ι K') : Matrix ι ι K') * ((P : Matrix ι ι K') *
          (ρ z).map (algebraMap K K') * ((P⁻¹ : GL ι K') : Matrix ι ι K') *
            (P : Matrix ι ι K'))
        = (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) *
          (ρ z).map (algebraMap K K') * (((P⁻¹ : GL ι K') : Matrix ι ι K') *
            (P : Matrix ι ι K')) := by noncomm_ring
      _ = _ := by rw [hPiP, one_mul, mul_one]
  have hmem := Submodule.mem_map_of_mem (f := Cj) hspan
  rw [Submodule.map_span, ← Set.range_comp] at hmem
  have hmem2 : (ρ g).map (algebraMap K K') ∈ Submodule.span K'
      ((fun a : Matrix ι ι K => a.map (algebraMap K K')) '' Set.range fun b : B => ρ (ιB b)) := by
    rw [← Set.range_comp]
    have hrange : (Cj ∘ fun b : B => diagOf f (ιB b)) =
        ((fun a : Matrix ι ι K => a.map (algebraMap K K')) ∘ fun b : B => ρ (ιB b)) := by
      funext b
      exact hCj (ιB b)
    rw [← hrange]
    have h4 : (ρ g).map (algebraMap K K') = Cj (diagOf f g) := (hCj g).symm
    rw [h4]
    exact hmem
  exact mem_span_of_map_mem_span (K := K) (K' := K') _ _ hmem2

end Stable

end CFSG.RankThree.PartOne.AUTSL
