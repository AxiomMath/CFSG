module

public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Form

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem sl2_map_fixed_iff (Fr : L →+* L)
    (hfix : ∀ c, Fr c = c ↔ c ∈ Set.range (algebraMap K L)) (B : SL(2, L)) :
    SpecialLinearGroup.map Fr B = B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap K L)).range := by
  constructor
  · intro hB
    have hentry : ∀ i j, ∃ b : K, algebraMap K L b = (B : Matrix (Fin 2) (Fin 2) L) i j := by
      intro i j
      have h := congrArg (fun C : SL(2, L) => (C : Matrix (Fin 2) (Fin 2) L) i j) hB
      simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at h
      exact (hfix _).mp h
    choose b hb using hentry
    have hmat : (algebraMap K L).mapMatrix (Matrix.of b) = (B : Matrix (Fin 2) (Fin 2) L) := by
      ext i j
      exact hb i j
    have hdet : (Matrix.of b).det = 1 := by
      apply (algebraMap K L).injective
      rw [RingHom.map_det, hmat, B.2, map_one]
    exact ⟨⟨Matrix.of b, hdet⟩, Subtype.ext hmat⟩
  · rintro ⟨C, rfl⟩
    ext i j
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (hfix _).mpr ⟨_, rfl⟩

theorem sl2_twistedFixed_iff (Fr : L →+* L)
    (hfix : ∀ c, Fr c = c ↔ c ∈ Set.range (algebraMap K L)) (P : GL (Fin 2) L)
    (B : SL(2, L)) :
    conjSL (P * GeneralLinearGroup.map Fr P⁻¹) (SpecialLinearGroup.map Fr B) = B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) := by
  have hPinv : ∀ A, conjSL P (conjSL P⁻¹ A) = A := fun A => by
    rw [← conjSL_mul, mul_inv_cancel, conjSL_one]
  have hinvP : ∀ A, conjSL P⁻¹ (conjSL P A) = A := fun A => by
    rw [← conjSL_mul, inv_mul_cancel, conjSL_one]
  have h1 : conjSL (P * GeneralLinearGroup.map Fr P⁻¹) (SpecialLinearGroup.map Fr B) =
      conjSL P (SpecialLinearGroup.map Fr (conjSL P⁻¹ B)) := by
    rw [conjSL_mul, map_conjSL]
  rw [h1, Subgroup.mem_map]
  constructor
  · intro hB
    refine ⟨conjSL P⁻¹ B, (sl2_map_fixed_iff Fr hfix _).mp ?_, hPinv B⟩
    have h := congrArg (conjSL P⁻¹) hB
    rwa [hinvP] at h
  · rintro ⟨C, hC, rfl⟩
    rw [hinvP, (sl2_map_fixed_iff Fr hfix C).mpr hC]

theorem sl2_conj_range_centralizer (P : GL (Fin 2) L) :
    Subgroup.centralizer ((((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)).map
      SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (GeneralLinearGroup.scalar (Fin 2)).range := by
  have hupper : (SpecialLinearGroup.map (algebraMap K L) (sl2Upper K 1) :
      Matrix (Fin 2) (Fin 2) L) = !![1, 1; 0, 1] := by
    rw [SpecialLinearGroup.map_apply_coe, coe_sl2Upper]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hlower : (SpecialLinearGroup.map (algebraMap K L) (sl2Lower K 1) :
      Matrix (Fin 2) (Fin 2) L) = !![1, 0; 1, 1] := by
    rw [SpecialLinearGroup.map_apply_coe, coe_sl2Lower]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    have hY : ∀ C : SL(2, K), ((P⁻¹ * g * P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) *
        (SpecialLinearGroup.map (algebraMap K L) C : Matrix (Fin 2) (Fin 2) L) =
          (SpecialLinearGroup.map (algebraMap K L) C : Matrix (Fin 2) (Fin 2) L) *
            ((P⁻¹ * g * P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      intro C
      set X := SpecialLinearGroup.map (algebraMap K L) C
      have hmem : SpecialLinearGroup.toGL (conjSL P X) ∈
          ((((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)).map
            SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) :=
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
    have hYc : P⁻¹ * g * P ∈ Subgroup.center (GL (Fin 2) L) :=
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

theorem sl2_conj_range_quasisimple [Finite K] (hK4 : 4 ≤ Nat.card K) (P : GL (Fin 2) L) :
    Finite ((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) ∧
      CFSG.IsQuasisimple ((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) := by
  have hSLinj : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL(2, L) => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e : SL(2, K) ≃* ((SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) :=
    (MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)
  have : Fintype K := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have h : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hK4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h
    exact ⟨t, ht⟩
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (isQuasisimple_SL2 h4)⟩

end Form

theorem exists_WSL_twist {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ P : GL (Fin 2) L,
      P * GeneralLinearGroup.map Fr P⁻¹ = SpecialLinearGroup.toGL (WSL : SL(2, L)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hqL : (q : L) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card] at h
    have h2 := congrArg (algebraMap K L) h
    rwa [map_natCast, map_zero] at h2
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have hqpos : 0 < q ^ 2 - 1 := by omega
  have hq2L : ((q ^ 2 - 1 : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_sub hq1]
    push_cast
    rw [hqL]
    simp
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) hqpos
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hqpos.ne'] at ha
    exact one_ne_zero (neg_eq_zero.1 ha.symm)
  have haq : a ^ (q ^ 2) = -a := by
    have h : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
    rw [h, pow_succ, ha]
    ring
  have : NeZero ((q ^ 2 - 1 : ℕ) : L) := ⟨hq2L⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (q ^ 2 - 1)
  have hμ0 : μ ≠ 0 := hμ.ne_zero hqpos.ne'
  have hμq2 : μ ^ (q ^ 2) = μ := by
    have h : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
    rw [h, pow_succ, hμ.pow_eq_one, one_mul]
  have hμq : μ ^ q ≠ μ := by
    intro h
    have h1 : μ ^ (q - 1) = 1 := by
      have h2 : μ ^ q = μ ^ (q - 1) * μ := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h2] at h
      exact (mul_eq_right₀ hμ0).1 h
    have h3 := hμ.dvd_of_pow_eq_one _ h1
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 : q < q ^ 2 := by nlinarith
    omega
  have hdet : (!![a, μ * a; -(a ^ q), -((μ * a) ^ q)] : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have h : a * -((μ * a) ^ q) - μ * a * -(a ^ q) = a ^ (q + 1) * (μ - μ ^ q) := by
      rw [mul_pow, pow_succ]
      ring
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ ha0) (sub_ne_zero.2 hμq.symm)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  rw [map_inv, mul_inv_eq_iff_eq_mul]
  have hFa : Fr a = a ^ q := hFr a
  have hFma : Fr (μ * a) = (μ * a) ^ q := hFr _
  have h1 : Fr (a ^ q) = -a := by
    rw [map_pow, hFa, ← pow_mul, ← sq]
    exact haq
  have h2 : Fr ((μ * a) ^ q) = -(μ * a) := by
    rw [map_pow, hFma, ← pow_mul, ← sq, mul_pow, hμq2, haq]
    ring
  have hmapP : ((GeneralLinearGroup.map Fr (GeneralLinearGroup.mkOfDetNeZero _ hdet) :
      GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![a ^ q, (μ * a) ^ q; a, μ * a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.map, hFa, hFma, h1, h2]
  have hJ : ((SpecialLinearGroup.toGL (WSL : SL(2, L)) : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, 1; -1, 0] := rfl
  apply Units.ext
  rw [Units.val_mul, hmapP, hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_finite_field_into (ℓ f : ℕ) [Fact ℓ.Prime] (hf : 1 ≤ f) (L : Type) [Field L]
    [CharP L ℓ] [IsAlgClosed L] :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k L), Nat.card k = ℓ ^ f := by
  have : NeZero f := ⟨by omega⟩
  let _ : Algebra (ZMod ℓ) L := ZMod.algebra L ℓ
  refine ⟨GaloisField ℓ f, inferInstance, inferInstance,
    (IsAlgClosed.lift : GaloisField ℓ f →ₐ[ZMod ℓ] L).toRingHom.toAlgebra, ?_⟩
  exact GaloisField.card ℓ f (by omega)

end CFSG.RankThree.PartOne.KE
