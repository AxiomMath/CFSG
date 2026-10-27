module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofWeights

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful

open CFSG.RankThree.PartTwo.KFacts.KS116Proof (uu hh uu_add uu_zero uu_mul_comm)
open CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof
  (eigen_add eigen_zero linearIndependent_of_eigen natCard_le_finrank sigma_apply_ne_zero)
open scoped MatrixGroups TensorProduct

section Weights

variable {F : Type} [Field F]

theorem uu_one_pow {p : ℕ} (hp : (p : F) = 0) : (uu (1 : F)) ^ p = 1 := by
  have h : ∀ n : ℕ, (uu (1 : F)) ^ n = uu (n : F) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, uu_zero]
    | succ n ih => rw [pow_succ, ih, Nat.cast_succ, uu_add]
  rw [h, hp, uu_zero]

theorem uu_mul_hh_inv (y : Fˣ) (b : F) :
    uu b * hh y⁻¹ = hh y⁻¹ * uu ((y : F) ^ 2 * b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) *
      !![((y⁻¹ : Fˣ) : F), 0; 0, (((y⁻¹)⁻¹ : Fˣ) : F)] =
    !![((y⁻¹ : Fˣ) : F), 0; 0, (((y⁻¹)⁻¹ : Fˣ) : F)] * !![1, (y : F) ^ 2 * b; 0, 1]
  rw [inv_inv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  have hy0 : (y : F) ≠ 0 := y.ne_zero
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem card_squares_le_finrank [Finite F] {K W : Type} [Field K] [IsAlgClosed K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : SL(2, F) →* Module.End K W)
    {p : ℕ} (hp : (p : F) = 0) (hpK : (p : K) ≠ 0) (h1 : σ (uu 1) ≠ 1) :
    Nat.card {μ : Fˣ // IsSquare μ} ≤ Module.finrank K W := by
  classical
  have hcomm : ∀ a b : F, Commute (σ (uu a)) (σ (uu b)) := fun a b =>
    (show Commute (uu a) (uu b) from uu_mul_comm a b).map σ
  set b₁ := σ (uu (1 : F)) with hb₁
  have hb₁p : b₁ ^ p = 1 := by rw [hb₁, ← map_pow, uu_one_pow hp, map_one]
  set U := LinearMap.range (b₁ - 1) with hU
  have hU0 : U ≠ ⊥ := by
    rw [hU, Ne, LinearMap.range_eq_bot, sub_eq_zero]
    exact h1
  have hUinv : ∀ a : F, ∀ u ∈ U, σ (uu a) u ∈ U := by
    rintro a _ ⟨w, rfl⟩
    refine ⟨σ (uu a) w, ?_⟩
    have h := ((hcomm 1 a).sub_left (Commute.one_left _)).eq
    have h' := LinearMap.congr_fun h w
    rw [Module.End.mul_apply, Module.End.mul_apply] at h'
    exact h'
  obtain ⟨v, hvU, hv0, χ, hv⟩ := LSSolvableProof.exists_common_eigenvector_of_isAlgClosed
    (fun a : F => σ (uu a)) hcomm U hUinv hU0
  have hχ1 : χ 1 ≠ 1 := by
    intro h
    have hker : v ∈ LinearMap.ker (b₁ - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      have := hv 1
      rw [h, one_smul] at this
      exact this
    have hmem : v ∈ LinearMap.ker (b₁ - 1) ⊓ LinearMap.range (b₁ - 1) := ⟨hker, hvU⟩
    rw [LSSolvableProof.ker_inf_range_eq_bot hb₁p hpK] at hmem
    exact hv0 ((Submodule.mem_bot K).mp hmem)
  have hadd := eigen_add (σ := σ) hv0 hv
  have h0 := eigen_zero (σ := σ) hv0 hv
  have hχne : ∀ a, χ a ≠ 0 := fun a h => by
    have := hadd a (-a)
    rw [add_neg_cancel, h0, h, zero_mul] at this
    exact one_ne_zero this
  choose y hy using fun μ : {μ : Fˣ // IsSquare μ} => μ.2
  let w : {μ : Fˣ // IsSquare μ} → W := fun μ => σ (hh (y μ)⁻¹) v
  have hw0 : ∀ μ, w μ ≠ 0 := fun μ => sigma_apply_ne_zero σ _ hv0
  have hw : ∀ (μ : {μ : Fˣ // IsSquare μ}) (b : F),
      σ (uu b) (w μ) = χ ((μ.1 : F) * b) • w μ := by
    intro μ b
    change σ (uu b) (σ (hh (y μ)⁻¹) v) = _
    rw [← Module.End.mul_apply, ← map_mul, uu_mul_hh_inv, map_mul, Module.End.mul_apply, hv,
      map_smul]
    have hμ : (μ.1 : F) = (y μ : F) ^ 2 := by
      rw [hy μ, Units.val_mul, sq]
    rw [hμ]
  have hinj : Function.Injective
      (fun (μ : {μ : Fˣ // IsSquare μ}) (b : F) => χ ((μ.1 : F) * b)) := by
    intro μ ν h
    by_contra hne
    have hne' : (μ.1 : F) - ν.1 ≠ 0 :=
      sub_ne_zero.mpr (fun h' => hne (Subtype.ext (Units.ext h')))
    have e : χ ((μ.1 : F) * ((μ.1 : F) - ν.1)⁻¹) = χ ((ν.1 : F) * ((μ.1 : F) - ν.1)⁻¹) :=
      congrFun h _
    have hsplit : (μ.1 : F) * ((μ.1 : F) - ν.1)⁻¹ = (ν.1 : F) * ((μ.1 : F) - ν.1)⁻¹ + 1 := by
      rw [← sub_eq_iff_eq_add', ← sub_mul, mul_inv_cancel₀ hne']
    rw [hsplit, hadd] at e
    exact hχ1 (mul_left_cancel₀ (hχne _) (e.trans (mul_one _).symm))
  have hind : LinearIndependent K w := linearIndependent_of_eigen (fun a : F => σ (uu a)) hcomm
    (fun μ b => χ ((μ.1 : F) * b)) hinj w hw hw0
  exact natCard_le_finrank hind

theorem card_squares_le_finrank_zmod [Finite F] {r p : ℕ} [Fact r.Prime] (hp : (p : F) = 0)
    (hrp : ¬ r ∣ p) {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
    (σ : SL(2, F) →* Module.End (ZMod r) V) (h1 : σ (uu 1) ≠ 1) :
    Nat.card {μ : Fˣ // IsSquare μ} ≤ Module.finrank (ZMod r) V := by
  let K := AlgebraicClosure (ZMod r)
  let σK : SL(2, F) →* Module.End K (K ⊗[ZMod r] V) :=
    (Module.End.baseChangeHom (ZMod r) K V : Module.End (ZMod r) V →ₐ[ZMod r] _).toMonoidHom.comp
      σ
  have hpK : (p : K) ≠ 0 := fun h => hrp ((CharP.cast_eq_zero_iff K r p).mp h)
  have hinj : Function.Injective (Module.End.baseChangeHom (ZMod r) K V) :=
    LinearMap.baseChangeHom_injective (ZMod r) V K
  have h1K : σK (uu 1) ≠ 1 := fun h => h1 (hinj (by rw [map_one]; exact h))
  have := card_squares_le_finrank σK hp hpK h1K
  rwa [LSSolvableProof.finrank_baseChange_eq] at this

end Weights

section Squares

theorem card_units_le_two_mul_card_squares (F : Type) [Field F] [Finite F] :
    Nat.card Fˣ ≤ 2 * Nat.card {μ : Fˣ // IsSquare μ} := by
  classical
  have := Fintype.ofFinite Fˣ
  have key := Finset.card_le_mul_card_image (f := fun y : Fˣ => y * y) (Finset.univ : Finset Fˣ) 2
    (by
      intro a ha
      obtain ⟨y₀, -, rfl⟩ := Finset.mem_image.mp ha
      calc (Finset.univ.filter fun x : Fˣ => x * x = y₀ * y₀).card
          ≤ ({y₀, -y₀} : Finset Fˣ).card := by
            apply Finset.card_le_card
            intro x hx
            have hx' : x * x = y₀ * y₀ := (Finset.mem_filter.mp hx).2
            have h' : (x : F) ^ 2 = (y₀ : F) ^ 2 := by
              rw [sq, sq]
              exact_mod_cast congrArg Units.val hx'
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h | h
            · simp [Units.ext h]
            · simp [Units.ext (h.trans (Units.val_neg y₀).symm)]
        _ ≤ 2 := Finset.card_le_two)
  have hsq : (Finset.univ.image fun y : Fˣ => y * y) =
      Finset.univ.filter fun μ : Fˣ => IsSquare μ := by
    ext μ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  rw [hsq, Finset.card_univ] at key
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact key

end Squares

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeFaithful
