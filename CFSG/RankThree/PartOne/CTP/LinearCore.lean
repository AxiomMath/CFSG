module

public import CFSG.RankThree.PartOne.CTP.BlkGroup
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.ClassicalInvolution.WeakCT.Torus

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.LinearDescent CFSG.RankThree.UnitaryDescent
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_field_of_pow_eq_one {p : ℕ} (hp : Odd p) (α : MulAut (projectiveSL 3 F))
    (hα : α ^ p = 1) :
    ∃ (M : GL (Fin 3) F) (σ : F ≃+* F), α = conjAut 3 F M * fieldAut 3 F σ := by
  obtain ⟨htop, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  have hα' : α ∈ standardAutGroup 3 F := by rw [htop]; exact Subgroup.mem_top α
  have hE : α ∈ semilinearAutGroup 3 F := by
    rcases mem_or_mul_dualAut_mem hα' with h | h
    · exact h
    · have hδδ := (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
      set δ := dualAut 3 F
      have hβ : α * δ ∈ semilinearAutGroup 3 F := h
      have hsq : α * α ∈ semilinearAutGroup 3 F := by
        have h1 := dualAut_mul_mul_dualAut_mem hβ
        have h2 : α * α = (α * δ) * (δ * (α * δ) * δ) := by
          rw [show (α * δ) * (δ * (α * δ) * δ) = α * (δ * δ) * α * (δ * δ) by group, hδδ]
          group
        rw [h2]
        exact mul_mem hβ h1
      obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := hp.add_one.elim fun k hk => ⟨k, by omega⟩
      have : α = (α * α) ^ k := by
        rw [← sq, ← pow_mul, ← hk, pow_succ, hα, one_mul]
      rw [this]
      exact Subgroup.pow_mem _ hsq k
  exact mem_semilinearAutGroup_iff.mp hE


section Basics

theorem exists_primitiveRoot_card_sub_one : ∃ g : F, IsPrimitiveRoot g (Nat.card F - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, ?_⟩
  have h1 : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  rw [← h2, ← h1]
  exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf g)

theorem ringEquiv_eq_one_of_fix {μ : F} (hμ : IsPrimitiveRoot μ (Nat.card F - 1)) (σ : F ≃+* F)
    (h : σ μ = μ) : σ = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have : NeZero (Nat.card F - 1) := ⟨by have := Finite.one_lt_card (α := F); omega⟩
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have hpow : x ^ (Nat.card F - 1) = 1 := by
      have h1 := FiniteField.pow_card_sub_one_eq_one x hx
      rwa [Nat.card_eq_fintype_card]
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hpow
    simp [map_pow, h]

end Basics

section Sl2

variable (K : Type) [Field K]

@[expose] def weyl2 : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem weyl2_torus (s : Kˣ) :
    weyl2 K * CFSG.ClassicalInvolution.WeakCT.torusHom K s * (weyl2 K)⁻¹ =
      CFSG.ClassicalInvolution.WeakCT.torusHom K s⁻¹ := by
  have h : weyl2 K * CFSG.ClassicalInvolution.WeakCT.torusHom K s =
      CFSG.ClassicalInvolution.WeakCT.torusHom K s⁻¹ * weyl2 K := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      CFSG.ClassicalInvolution.WeakCT.coe_torusHom, CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weyl2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  group

theorem exists_noncomm_sl2 : ∃ a b : SL(2, K), a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro h
  have h' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h
  have h0 := congrFun (congrFun h' 0) 0
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 =
    (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 at h0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h0

end Sl2

theorem card_sl2_eq {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (h : Nat.card K = Nat.card K') : Nat.card SL(2, K) = Nat.card SL(2, K') := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  have e : K ≃+* K' := FiniteField.ringEquivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h)
  refine Nat.card_congr ⟨Matrix.SpecialLinearGroup.map e.toRingHom,
    Matrix.SpecialLinearGroup.map e.symm.toRingHom, fun A => ?_, fun A => ?_⟩
  · ext i j; simp
  · ext i j; simp

theorem isPerfect_sl2 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect SL(2, K) := by
  have : Fintype K := Fintype.ofFinite K
  refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa using hK)
  exact ⟨s, hs⟩


section Node

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

@[expose] noncomputable def semilinSL (M : GL (Fin 3) F) (σ : F ≃+* F) :
    SL(3, F) →* SL(3, F) :=
  (slConjugation 3 F M).toMonoidHom.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)

omit [Finite F] in
theorem coe_semilinSL (M : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    ((semilinSL M σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (M : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  change ((slConjugation 3 F M (Matrix.SpecialLinearGroup.map σ.toRingHom g) :
    SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [slConjugation_matrix]
  rfl

omit [Finite F] in
theorem proj_semilinSL (M : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    proj 3 F (semilinSL M σ g) = (conjAut 3 F M * fieldAut 3 F σ) (proj 3 F g) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rfl

variable [CharP F 2]

theorem node_lemma (hq : 4 ≤ Nat.card F) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ = Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) (φ : SL(2, K₀) →* SL(3, F)) (hφ : Function.Injective φ)
    (α : MulAut (projectiveSL 3 F)) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (hfix : ∀ a, α (proj 3 F (φ a)) = proj 3 F (φ a)) :
    ∃ (M : GL (Fin 3) F) (W ℓ : Submodule F (Fin 3 → F)) (a b : F),
      α = conjAut 3 F M ∧ IsCompl W ℓ ∧ Module.finrank F W = 2 ∧ a ≠ b ∧
      (∀ w ∈ W, (M : Matrix (Fin 3) (Fin 3) F).mulVec w = a • w) ∧
      (∀ u ∈ ℓ, (M : Matrix (Fin 3) (Fin 3) F).mulVec u = b • u) ∧
      φ.range = blkGroup F W ℓ := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨M, σ, hαMσ⟩ := exists_conj_field_of_pow_eq_one hpodd α hα
  have hpow : conjAut 3 F (twistedNorm σ M p) * fieldAut 3 F (σ ^ p) = 1 := by
    rw [← conjAut_mul_fieldAut_pow, ← hαMσ, hα]
  obtain ⟨hσp, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hpow
  have hσodd : Odd (orderOf σ) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  have hK4 : 4 ≤ Nat.card K₀ := by rw [hK₀]; exact hq
  have hperf : Group.IsPerfect SL(2, K₀) := isPerfect_sl2 hK4
  have hψα : ∀ g, proj 3 F (semilinSL M σ g) = α (proj 3 F g) := fun g => by
    rw [hαMσ]; exact proj_semilinSL M σ g
  have hcen : (proj 3 F).ker ≤ Subgroup.center SL(3, F) := by
    rw [ker_proj]; exact scalars_le_center 3 F
  have hψφ : (semilinSL M σ).comp φ = φ := by
    refine CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect (π := proj 3 F) hcen ?_
    ext a
    simp only [MonoidHom.comp_apply]
    rw [hψα, hfix]
  have hMφ : ∀ a, (M : Matrix (Fin 3) (Fin 3) F) *
      ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) := by
    intro a
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F))
      (DFunLike.congr_fun hψφ a)
    simp only [MonoidHom.comp_apply, coe_semilinSL] at h1
    have h2 : ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (M : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (M : Matrix (Fin 3) (Fin 3) F) * ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ
        = (M * ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ *
            ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
              (M : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = _ := by rw [h1]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K₀ˣ)
  have hord : orderOf (CFSG.ClassicalInvolution.WeakCT.torusHom K₀ g) = Nat.card F - 1 := by
    rw [orderOf_injective (CFSG.ClassicalInvolution.WeakCT.torusHom K₀)
      (CFSG.ClassicalInvolution.WeakCT.torusHom_injective (K := K₀)) g,
      orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK₀]
  have hσ1 : σ = 1 := by
    obtain ⟨μ, hμ, hσμ⟩ := sigma_fixes_generator σ hσodd
      (φ (CFSG.ClassicalInvolution.WeakCT.torusHom K₀ g)) (φ (weyl2 K₀)) M M.isUnit
      (Nat.card F - 1) (by omega) (by rw [orderOf_injective φ hφ, hord])
      exists_primitiveRoot_card_sub_one
      (by rw [← map_mul, ← map_inv, ← map_mul, weyl2_torus, map_inv, map_inv])
      (hMφ _)
    exact ringEquiv_eq_one_of_fix hμ σ hσμ
  subst hσ1
  have hα' : α = conjAut 3 F M := by rw [hαMσ, map_one, mul_one]
  have hcomm : ∀ a, ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) =
      (M : Matrix (Fin 3) (Fin 3) F) * ((φ a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    intro a
    have := hMφ a
    simpa using this.symm
  have hMp : ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 3) c = M ^ p := by
    have h1 : conjAut 3 F (M ^ p) * fieldAut 3 F (1 : F ≃+* F) = 1 := by
      rw [map_one, mul_one, map_pow, ← hα', hα]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h1).2
  obtain ⟨c, hc⟩ := hMp
  have hMpm : (M : Matrix (Fin 3) (Fin 3) F) ^ p = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [← this]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hns : ¬ ∃ c : F, (M : Matrix (Fin 3) (Fin 3) F) = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := M.isUnit
      rw [hc, zero_smul] at this
      exact not_isUnit_zero this
    apply hα1
    rw [hα']
    have : M = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      ext i j
      rw [hc]
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.one_apply]
    rw [this]
    exact conjAut_scalar _
  have hdiag : ∃ (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, (M : Matrix (Fin 3) (Fin 3) F).mulVec (b i) = d i • b i := by
    rcases eigenbasis_or_commutative hp hp3 hpq (M : Matrix (Fin 3) (Fin 3) F) (c : F) c.ne_zero
      hMpm with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_noncomm_sl2 K₀
      apply hab
      apply hφ
      rw [map_mul, map_mul]
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h _ _ (hcomm a) (hcomm b)
  have hperfR : Group.IsPerfect φ.range :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) (MonoidHom.rangeRestrict_surjective φ)
  have hcard : Nat.card φ.range = Nat.card SL(2, F) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, card_sl2_eq hK₀]
  obtain ⟨W, ℓ, a, b, hWℓ, hrk, hab, hW, hℓ, hH⟩ := exists_eq_blkGroup hq φ.range hcard
    (M : Matrix (Fin 3) (Fin 3) F) hdiag hns (by
      rintro _ ⟨x, rfl⟩
      exact hcomm x)
  exact ⟨M, W, ℓ, a, b, hα', hWℓ, hrk, hab, hW, hℓ, hH⟩

end Node


section Edge

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

theorem conj_range_eq {K₁ : Type} [Field K₁] [Finite K₁] (hK₁ : 4 ≤ Nat.card K₁)
    (φ : SL(2, K₁) →* SL(3, F)) (M : GL (Fin 3) F)
    (h : ∀ b, ∃ b', conjAut 3 F M (proj 3 F (φ b)) = proj 3 F (φ b')) :
    φ.range.map (slConjugation 3 F M).toMonoidHom = φ.range := by
  have hperf : Group.IsPerfect SL(2, K₁) := isPerfect_sl2 hK₁
  let χ : SL(2, K₁) →* SL(3, F) := (slConjugation 3 F M).toMonoidHom.comp φ
  have hcen := scalars_le_center 3 F
  have hchi : ∀ x, ∃ x' z, z ∈ Subgroup.center SL(3, F) ∧ χ x = φ x' * z := by
    intro x
    obtain ⟨x', hx'⟩ := h x
    rw [conjAut_proj] at hx'
    have := proj_eq_proj_iff.mp hx'.symm
    refine ⟨x', (φ x')⁻¹ * χ x, hcen this, ?_⟩
    simp
  have hD : (φ.range).comap χ = ⊤ := by
    rw [eq_top_iff]
    have hc : commutator SL(2, K₁) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← hc]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    obtain ⟨x', zx, hzx, hx⟩ := hchi x
    obtain ⟨y', zy, hzy, hy⟩ := hchi y
    rw [Subgroup.mem_comap, map_commutatorElement, hx, hy]
    have h1 : ⁅φ x' * zx, φ y' * zy⁆ = ⁅φ x', φ y'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have hx1 := Subgroup.mem_center_iff.mp hzx
      have hy1 := Subgroup.mem_center_iff.mp hzy
      calc φ x' * zx * (φ y' * zy) * (φ x' * zx)⁻¹ * (φ y' * zy)⁻¹
          = φ x' * (zx * (φ y' * zy)) * zx⁻¹ * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by group
        _ = φ x' * ((φ y' * zy) * zx) * zx⁻¹ * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by rw [hx1]
        _ = φ x' * φ y' * zy * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ := by group
        _ = _ := by
          rw [show φ x' * φ y' * zy * (φ x')⁻¹ * zy⁻¹ * (φ y')⁻¹ =
            φ x' * φ y' * (zy * (φ x')⁻¹ * zy⁻¹) * (φ y')⁻¹ by group, ← hy1 (φ x')⁻¹]
          group
    rw [h1, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hle : φ.range.map (slConjugation 3 F M).toMonoidHom ≤ φ.range := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have : b ∈ (φ.range).comap χ := by rw [hD]; trivial
    exact this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (slConjugation 3 F M).injective]


omit [Finite F] in
theorem normalizes_of_map_eq {R : Subgroup SL(3, F)} (M : GL (Fin 3) F)
    (h : R.map (slConjugation 3 F M).toMonoidHom = R) :
    (∀ g ∈ R, ∃ g' ∈ R, (M : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g' : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F)) ∧
    (∀ g ∈ R, ∃ g' ∈ R, (g : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) =
        (M : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F)) := by
  have hMi : ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro g hg
    refine ⟨slConjugation 3 F M g, ?_, ?_⟩
    · rw [← h]; exact ⟨g, hg, rfl⟩
    · rw [slConjugation_matrix, Matrix.mul_assoc, Matrix.mul_assoc, hMi, Matrix.mul_one]
  · intro g hg
    rw [← h] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    refine ⟨g', hg', ?_⟩
    change ((slConjugation 3 F M g' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      (M : Matrix (Fin 3) (Fin 3) F) = _
    rw [slConjugation_matrix, Matrix.mul_assoc, Matrix.mul_assoc, hMi, Matrix.mul_one]

variable [CharP F 2]

theorem linear_edge_core (hq : 4 ≤ Nat.card F) {KA KB : Type} [Field KA] [Field KB] [Finite KA]
    [Finite KB] (hKA : Nat.card KA = Nat.card F) (hKB : Nat.card KB = Nat.card F) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    (φA : SL(2, KA) →* SL(3, F)) (hφA : Function.Injective φA)
    (φB : SL(2, KB) →* SL(3, F)) (hφB : Function.Injective φB)
    (αA αB : MulAut (projectiveSL 3 F)) (hαA : αA ^ p = 1) (hαB : αB ^ p = 1)
    (hAfix : ∀ a, αA (proj 3 F (φA a)) = proj 3 F (φA a))
    (hBfix : ∀ b, αB (proj 3 F (φB b)) = proj 3 F (φB b))
    (hAB : ∀ b, ∃ b', αA (proj 3 F (φB b)) = proj 3 F (φB b'))
    (hBA : ∀ a, ∃ a', αB (proj 3 F (φA a)) = proj 3 F (φA a'))
    (hmovB : ∃ b, αA (proj 3 F (φB b)) ≠ proj 3 F (φB b))
    (hmovA : ∃ a, αB (proj 3 F (φA a)) ≠ proj 3 F (φA a)) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      φA.range = blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) ∧
      φB.range = blkGroup F (Submodule.span F {b 1, b 2}) (Submodule.span F {b 0}) := by
  have hαA1 : αA ≠ 1 := by
    rintro rfl
    obtain ⟨b, hb⟩ := hmovB
    exact hb rfl
  have hαB1 : αB ≠ 1 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hmovA
    exact ha rfl
  obtain ⟨MA, WA, ℓA, a₁, b₁, hαA', hcA, hdA, hab₁, hWA, hℓA, hrA⟩ :=
    node_lemma hq hKA hp hp2 hpq φA hφA αA hαA hαA1 hAfix
  obtain ⟨MB, WB, ℓB, a₂, b₂, hαB', hcB, hdB, hab₂, hWB, hℓB, hrB⟩ :=
    node_lemma hq hKB hp hp2 hpq φB hφB αB hαB hαB1 hBfix
  have hKA4 : 4 ≤ Nat.card KA := by rw [hKA]; exact hq
  have hKB4 : 4 ≤ Nat.card KB := by rw [hKB]; exact hq
  have hNB : φB.range.map (slConjugation 3 F MA).toMonoidHom = φB.range :=
    conj_range_eq hKB4 φB MA (fun b => by rw [← hαA']; exact hAB b)
  have hNA : φA.range.map (slConjugation 3 F MB).toMonoidHom = φA.range :=
    conj_range_eq hKA4 φA MB (fun a => by rw [← hαB']; exact hBA a)
  obtain ⟨hB1, hB2⟩ := normalizes_of_map_eq MA hNB
  obtain ⟨hA1, hA2⟩ := normalizes_of_map_eq MB hNA
  rw [hrB] at hB1 hB2
  rw [hrA] at hA1 hA2
  obtain ⟨hMAℓ, hMAW⟩ := normalizer_blkGroup hcB hdB (MA : Matrix (Fin 3) (Fin 3) F) MA.isUnit
    hB1 hB2
  obtain ⟨hMBℓ, hMBW⟩ := normalizer_blkGroup hcA hdA (MB : Matrix (Fin 3) (Fin 3) F) MB.isUnit
    hA1 hA2
  have hne : ¬ (WA = WB ∧ ℓA = ℓB) := by
    rintro ⟨hW, hℓ⟩
    obtain ⟨b, hb⟩ := hmovB
    apply hb
    have hmem : φB b ∈ φA.range := by
      have h0 : φB b ∈ φB.range := ⟨b, rfl⟩
      rw [hrB, ← hW, ← hℓ, ← hrA] at h0
      exact h0
    obtain ⟨a, ha⟩ := hmem
    rw [← ha]
    exact hAfix a
  obtain ⟨b, h1, h2, h3, h4⟩ := exists_basis_of_position WA ℓA WB ℓB hcA hdA hcB hdB hne
    (MA : Matrix (Fin 3) (Fin 3) F) (MB : Matrix (Fin 3) (Fin 3) F) a₁ b₁ a₂ b₂ hab₁ hab₂
    hWA hℓA hWB hℓB hMAW hMAℓ hMBW hMBℓ
  exact ⟨b, by rw [hrA, h1, h2], by rw [hrB, h3, h4]⟩

end Edge

end CFSG.RankThree.PartOne.CTP
