module

public import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.RankThree.QuadraticSL2

open Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LinearTwo (exists_mul_map_eq_smul)
open CFSG.ABGLocalTools (glNorm)
open scoped MatrixGroups

universe u

theorem quadratic_frobenius {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    Finite L ∧ orderOf σ = 2 ∧ ∀ c, σ c = c ↔ c ∈ Set.range (algebraMap K L) := by
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Finite L := Module.finite_of_finite K
  have : Fintype L := Fintype.ofFinite L
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hcard : Nat.card L = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdeg]
  have hfrob : ∀ c, FiniteField.frobeniusAlgEquivOfAlgebraic K L c = σ c := fun c => by
    rw [hσ, Nat.card_eq_fintype_card]
    rfl
  have hfix : ∀ c, σ c = c ↔ c ∈ Set.range (algebraMap K L) := by
    intro c
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    refine ⟨fun hc f => ?_, fun h => (hfrob c).symm.trans (h _)⟩
    obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f
    simp only [AlgEquiv.coe_pow]
    exact Function.iterate_fixed ((hfrob c).trans hc) _
  have hσ2 : σ ^ 2 = 1 := by
    ext c
    rw [pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← pow_two, ← hcard,
      Nat.card_eq_fintype_card, FiniteField.pow_card, RingAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hsurj : Function.Surjective (algebraMap K L) := fun c =>
      (hfix c).mp (by rw [h1, RingAut.one_apply])
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hcard] at this
    nlinarith
  exact ⟨inferInstance, orderOf_eq_prime hσ2 hσ1, hfix⟩

theorem eq_scalar_of_commute {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R)
    (hu : X * !![1, 1; 0, 1] = !![1, 1; 0, 1] * X)
    (hl : X * !![1, 0; 1, 1] = !![1, 0; 1, 1] * X) :
    X = Matrix.scalar (Fin 2) (X 0 0) := by
  have h1 := congrFun (congrFun hu 0) 0
  have h2 := congrFun (congrFun hu 0) 1
  have h3 := congrFun (congrFun hl 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  · exact h3
  · exact h1
  · linear_combination -h2

section SL2

variable {L : Type*} [Field L]

abbrev semilinearConj (M : GL (Fin 2) L) (σ : L ≃+* L) : SL(2, L) →* SL(2, L) :=
  (conjSL M).comp (SpecialLinearGroup.map (σ : L →+* L))

theorem commute_of_conjSL_eq (P : GL (Fin 2) L) {A : SL(2, L)} (h : conjSL P A = A) :
    (P : Matrix (Fin 2) (Fin 2) L) * A = A * P := by
  have h' := congrArg (fun B : SL(2, L) => (B : Matrix (Fin 2) (Fin 2) L) * P) h
  simp only [coe_conjSL, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h'
  exact h'

theorem conjSL_scalar (u : Lˣ) (A : SL(2, L)) :
    conjSL (GeneralLinearGroup.scalar (Fin 2) u) A = A := by
  apply Subtype.ext
  have h := congrArg Units.val (GeneralLinearGroup.scalar_commute u (SpecialLinearGroup.toGL A))
  rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] at h
  rw [coe_conjSL, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem map_conjSL (f : L →+* L) (P : GL (Fin 2) L) (A : SL(2, L)) :
    SpecialLinearGroup.map f (conjSL P A) =
      conjSL (GeneralLinearGroup.map f P) (SpecialLinearGroup.map f A) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_conjSL, coe_conjSL, SpecialLinearGroup.map_apply_coe,
    ← map_inv, map_mul, map_mul]
  rfl

end SL2

theorem even_quadratic_semilinear_SL2_fixed_matrix_group (K K₂ : Type u) [Field K] [Finite K]
    [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (M : GL (Fin 2) K₂)
    (hα : ∀ A, semilinearConj M σ (semilinearConj M σ A) = A) :
    ∃ P : GL (Fin 2) K₂, semilinearConj M σ = (semilinearConj P σ).comp (conjSL P⁻¹) ∧
      (semilinearConj M σ).eqLocus (MonoidHom.id _) =
        (SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) ∧
      (fun A : SL(2, K₂) => trace (A : Matrix (Fin 2) (Fin 2) K₂)) ''
          ((semilinearConj M σ).eqLocus (MonoidHom.id _) : Set (SL(2, K₂))) =
        Set.range (algebraMap K K₂) ∧
      Subgroup.centralizer (((semilinearConj M σ).eqLocus (MonoidHom.id _)).map
          SpecialLinearGroup.toGL : Set (GL (Fin 2) K₂)) =
        (GeneralLinearGroup.scalar (Fin 2)).range := by
  classical
  obtain ⟨hfin, hord, hfix⟩ := quadratic_frobenius hdeg σ hσ
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun τ : K₂ ≃+* K₂ => τ c) (pow_orderOf_eq_one σ)
    simpa only [hord, pow_two, RingAut.mul_apply, RingAut.one_apply] using h
  have hSS : ∀ A : SL(2, K₂), SpecialLinearGroup.map (σ : K₂ →+* K₂)
      (SpecialLinearGroup.map (σ : K₂ →+* K₂) A) = A := fun A => by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, hσσ]
  obtain ⟨N, hN⟩ : ∃ N, N = M * GeneralLinearGroup.map (σ : K₂ →+* K₂) M := ⟨_, rfl⟩
  have hNA : ∀ A : SL(2, K₂), conjSL N A = A := fun A => by
    have h := hα A
    simp only [semilinearConj, MonoidHom.comp_apply] at h
    rw [map_conjSL, hSS, ← conjSL_mul] at h
    rw [hN]
    exact h
  have hNsc : (N : Matrix (Fin 2) (Fin 2) K₂) =
      Matrix.scalar (Fin 2) ((N : Matrix (Fin 2) (Fin 2) K₂) 0 0) :=
    eq_scalar_of_commute _ (commute_of_conjSL_eq N (hNA (sl2Upper K₂ 1)))
      (commute_of_conjSL_eq N (hNA (sl2Lower K₂ 1)))
  have hc : ((glNorm σ M (orderOf σ) : GL (Fin 2) K₂) : Matrix (Fin 2) (Fin 2) K₂) =
      Matrix.scalar (Fin 2) ((N : Matrix (Fin 2) (Fin 2) K₂) 0 0) := by
    rw [← hNsc, hord]
    congr 1
    show 1 * GeneralLinearGroup.map ((σ ^ 0 : K₂ ≃+* K₂) : K₂ →+* K₂) M *
      GeneralLinearGroup.map ((σ ^ 1 : K₂ ≃+* K₂) : K₂ →+* K₂) M = N
    rw [pow_zero, pow_one, one_mul, hN]
    congr 1
  obtain ⟨P, d, hPd⟩ := exists_mul_map_eq_smul σ M hc
  have hMP : M * GeneralLinearGroup.map (σ : K₂ →+* K₂) P =
      P * GeneralLinearGroup.scalar (Fin 2) d := by
    ext i j
    have h := hPd i j
    rw [RingEquiv.toRingHom_eq_coe] at h
    rw [h, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal, mul_comm]
  have hMeq : M = P * GeneralLinearGroup.scalar (Fin 2) d *
      (GeneralLinearGroup.map (σ : K₂ →+* K₂) P)⁻¹ := by
    rw [← hMP, mul_inv_cancel_right]
  have hconj : ∀ A, semilinearConj M σ A =
      conjSL P (SpecialLinearGroup.map (σ : K₂ →+* K₂) (conjSL P⁻¹ A)) := fun A => by
    simp only [semilinearConj, MonoidHom.comp_apply]
    rw [map_conjSL, map_inv, hMeq, conjSL_mul, conjSL_mul, conjSL_scalar]
  have hPinv : ∀ A, conjSL P (conjSL P⁻¹ A) = A := fun A => by
    rw [← conjSL_mul, mul_inv_cancel, conjSL_one]
  have hinvP : ∀ A, conjSL P⁻¹ (conjSL P A) = A := fun A => by
    rw [← conjSL_mul, inv_mul_cancel, conjSL_one]
  have hdesc : ∀ B : SL(2, K₂), SpecialLinearGroup.map (σ : K₂ →+* K₂) B = B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap K K₂)).range := by
    intro B
    constructor
    · intro hB
      have hentry : ∀ i j, ∃ b : K, algebraMap K K₂ b = (B : Matrix (Fin 2) (Fin 2) K₂) i j := by
        intro i j
        have h := congrArg (fun C : SL(2, K₂) => (C : Matrix (Fin 2) (Fin 2) K₂) i j) hB
        simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
          RingEquiv.coe_toRingHom] at h
        exact (hfix _).mp h
      choose b hb using hentry
      have hmat : (algebraMap K K₂).mapMatrix (Matrix.of b) = (B : Matrix (Fin 2) (Fin 2) K₂) := by
        ext i j
        exact hb i j
      have hdet : (Matrix.of b).det = 1 := by
        apply (algebraMap K K₂).injective
        rw [RingHom.map_det, hmat, B.2, map_one]
      exact ⟨⟨Matrix.of b, hdet⟩, Subtype.ext hmat⟩
    · rintro ⟨C, rfl⟩
      ext i j
      simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        RingEquiv.coe_toRingHom]
      exact (hfix _).mpr ⟨_, rfl⟩
  have hFix : (semilinearConj M σ).eqLocus (MonoidHom.id _) =
      (SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) := by
    ext A
    change semilinearConj M σ A = A ↔ _
    rw [hconj, Subgroup.mem_map]
    constructor
    · intro hA
      refine ⟨conjSL P⁻¹ A, (hdesc _).mp ?_, hPinv A⟩
      have h := congrArg (conjSL P⁻¹) hA
      rwa [hinvP] at h
    · rintro ⟨B, hB, rfl⟩
      rw [hinvP, (hdesc B).mpr hB]
  have htrace : ∀ C : SL(2, K), trace ((conjSL P (SpecialLinearGroup.map (algebraMap K K₂) C) :
      SL(2, K₂)) : Matrix (Fin 2) (Fin 2) K₂) =
        algebraMap K K₂ (trace (C : Matrix (Fin 2) (Fin 2) K)) := by
    intro C
    rw [coe_conjSL, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.trace_fin_two,
      Matrix.trace_fin_two, SpecialLinearGroup.map_apply_coe, map_add]
    rfl
  have hTr : (fun A : SL(2, K₂) => trace (A : Matrix (Fin 2) (Fin 2) K₂)) ''
      ((semilinearConj M σ).eqLocus (MonoidHom.id _) : Set (SL(2, K₂))) =
        Set.range (algebraMap K K₂) := by
    rw [hFix]
    ext t
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨B, ⟨C, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hA
      exact ⟨_, (htrace C).symm⟩
    · rintro ⟨t, rfl⟩
      let C : SL(2, K) := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
      refine ⟨conjSL P (SpecialLinearGroup.map (algebraMap K K₂) C),
        Subgroup.mem_map.mpr ⟨_, ⟨C, rfl⟩, rfl⟩, ?_⟩
      change trace _ = _
      rw [htrace]
      simp [C, Matrix.trace_fin_two]
  have hupper : (SpecialLinearGroup.map (algebraMap K K₂) (sl2Upper K 1) :
      Matrix (Fin 2) (Fin 2) K₂) = !![1, 1; 0, 1] := by
    rw [SpecialLinearGroup.map_apply_coe, coe_sl2Upper]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hlower : (SpecialLinearGroup.map (algebraMap K K₂) (sl2Lower K 1) :
      Matrix (Fin 2) (Fin 2) K₂) = !![1, 0; 1, 1] := by
    rw [SpecialLinearGroup.map_apply_coe, coe_sl2Lower]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hCent : Subgroup.centralizer (((semilinearConj M σ).eqLocus (MonoidHom.id _)).map
      SpecialLinearGroup.toGL : Set (GL (Fin 2) K₂)) =
        (GeneralLinearGroup.scalar (Fin 2)).range := by
    rw [hFix, ← GeneralLinearGroup.center_eq_range_scalar]
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg
      have hY : ∀ C : SL(2, K), ((P⁻¹ * g * P : GL (Fin 2) K₂) : Matrix (Fin 2) (Fin 2) K₂) *
          (SpecialLinearGroup.map (algebraMap K K₂) C : Matrix (Fin 2) (Fin 2) K₂) =
            (SpecialLinearGroup.map (algebraMap K K₂) C : Matrix (Fin 2) (Fin 2) K₂) *
              ((P⁻¹ * g * P : GL (Fin 2) K₂) : Matrix (Fin 2) (Fin 2) K₂) := by
        intro C
        set X := SpecialLinearGroup.map (algebraMap K K₂) C
        have hmem : SpecialLinearGroup.toGL (conjSL P X) ∈
            ((((SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)).map
              SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) K₂)) : Set (GL (Fin 2) K₂)) :=
          ⟨conjSL P X, ⟨X, ⟨C, rfl⟩, rfl⟩, rfl⟩
        have h := hg _ hmem
        have hX : SpecialLinearGroup.toGL (conjSL P X) =
            P * SpecialLinearGroup.toGL X * P⁻¹ := Units.ext rfl
        rw [hX] at h
        have h2 : P⁻¹ * g * P * SpecialLinearGroup.toGL X =
            SpecialLinearGroup.toGL X * (P⁻¹ * g * P) := by
          calc P⁻¹ * g * P * SpecialLinearGroup.toGL X =
                P⁻¹ * (g * (P * SpecialLinearGroup.toGL X * P⁻¹)) * P := by group
            _ = P⁻¹ * (P * SpecialLinearGroup.toGL X * P⁻¹ * g) * P := by rw [h]
            _ = SpecialLinearGroup.toGL X * (P⁻¹ * g * P) := by group
        have h3 := congrArg Units.val h2
        rw [Units.val_mul, Units.val_mul] at h3
        exact h3
      have hu := hY (sl2Upper K 1)
      have hl := hY (sl2Lower K 1)
      rw [hupper] at hu
      rw [hlower] at hl
      have hYc : P⁻¹ * g * P ∈ Subgroup.center (GL (Fin 2) K₂) :=
        GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
          ⟨_, (eq_scalar_of_commute _ hu hl).symm⟩
      have hgY : g = P⁻¹ * g * P := by
        have h := Subgroup.mem_center_iff.mp hYc P
        calc g = P * (P⁻¹ * g * P) * P⁻¹ := by group
          _ = P⁻¹ * g * P * P * P⁻¹ := by rw [h]
          _ = P⁻¹ * g * P := by group
      rw [hgY]
      exact hYc
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact Subgroup.mem_center_iff.mp hg h
  exact ⟨P, MonoidHom.ext hconj, hFix, hTr, hCent⟩

end CFSG.RankThree.QuadraticSL2
