module

public import CFSG.RankThree.SteinbergR3EEvenCubicCoboundary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public noncomputable section

namespace CFSG.RankThree.EvenQuartic

open Matrix
open LinearMap (BilinForm)
open CFSG.RankThree.EvenCubic (mem_range_of_pow_card_eq)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] def antiJ (R : Type*) [Zero R] [One R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if (i : ℕ) + j = 3 then 1 else 0

theorem antiJ_apply (R : Type*) [Zero R] [One R] (i j : Fin 4) :
    antiJ R i j = if (i : ℕ) + j = 3 then 1 else 0 := rfl

theorem antiJ_mul_self (R : Type*) [CommRing R] : antiJ R * antiJ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiJ, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def spJ (M : Type*) [Field M] : Subgroup (GL (Fin 4) M) where
  carrier := {P | (P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * (P : Matrix (Fin 4) (Fin 4) M) =
    antiJ M}
  mul_mem' {P Q} hP hQ := by
    have hP' : (P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * (P : Matrix (Fin 4) (Fin 4) M) =
        antiJ M := hP
    have hQ' : (Q : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * (Q : Matrix (Fin 4) (Fin 4) M) =
        antiJ M := hQ
    show ((P * Q : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M *
      ((P * Q : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M) = antiJ M
    rw [Units.val_mul, transpose_mul]
    calc (Q : Matrix (Fin 4) (Fin 4) M)ᵀ * (P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M *
          ((P : Matrix (Fin 4) (Fin 4) M) * Q) =
          (Q : Matrix (Fin 4) (Fin 4) M)ᵀ * ((P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * P) *
            Q := by simp only [Matrix.mul_assoc]
      _ = antiJ M := by rw [hP', hQ']
  one_mem' := by
    show ((1 : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M *
      ((1 : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M) = antiJ M
    simp
  inv_mem' {P} hP := by
    have hP' : (P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * (P : Matrix (Fin 4) (Fin 4) M) =
        antiJ M := hP
    show ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M *
      ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M) = antiJ M
    calc ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M *
          ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M) =
          ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)ᵀ *
            ((P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * P) *
              ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M) := by rw [hP']
      _ = ((P : Matrix (Fin 4) (Fin 4) M) * ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M))ᵀ *
            antiJ M * ((P : Matrix (Fin 4) (Fin 4) M) *
              ((P⁻¹ : GL (Fin 4) M) : Matrix (Fin 4) (Fin 4) M)) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = antiJ M := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one, Matrix.one_mul,
            Matrix.mul_one]

theorem mem_spJ {M : Type*} [Field M] {P : GL (Fin 4) M} :
    P ∈ spJ M ↔ (P : Matrix (Fin 4) (Fin 4) M)ᵀ * antiJ M * (P : Matrix (Fin 4) (Fin 4) M) =
      antiJ M := Iff.rfl

@[expose] def cyc4 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide
  right_inv := by decide

theorem cyc4_apply (i : Fin 4) : cyc4 i = ![1, 3, 0, 2] i := rfl

theorem cyc4_inv_apply (i : Fin 4) : cyc4⁻¹ i = ![2, 0, 3, 1] i := rfl

theorem perm_four_cases : ∀ π : Equiv.Perm (Fin 4), π ^ 2 ≠ 1 → π ^ 4 = 1 →
    (∀ i, π (Fin.rev i) = Fin.rev (π i)) → π = cyc4 ∨ π = cyc4⁻¹ := by decide

theorem permMatrix_transpose_mul_mul_apply {R : Type*} [CommRing R] (π : Equiv.Perm (Fin 4))
    (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    ((π.permMatrix R)ᵀ * A * π.permMatrix R) (π i) (π j) = A i j := by
  simp [Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem rev_of_permMatrix {R : Type*} [CommRing R] [Nontrivial R] (π : Equiv.Perm (Fin 4))
    (hJ : (π.permMatrix R)ᵀ * antiJ R * π.permMatrix R = antiJ R) (i : Fin 4) :
    π (Fin.rev i) = Fin.rev (π i) := by
  have h := congrFun (congrFun hJ (π i)) (π (Fin.rev i))
  rw [permMatrix_transpose_mul_mul_apply, antiJ_apply, antiJ_apply] at h
  have hi : (i : ℕ) + (Fin.rev i : ℕ) = 3 := by rw [Fin.val_rev]; omega
  simp only [hi, ↓reduceIte] at h
  have h2 : ((π i : ℕ) + (π (Fin.rev i) : ℕ)) = 3 := by
    by_contra hne
    simp only [hne, ↓reduceIte] at h
    exact zero_ne_one h.symm
  apply Fin.ext
  rw [Fin.val_rev]
  omega

@[expose] def rowMatrix {K₄ : Type*} [Field K₄] (σ : K₄ ≃+* K₄) (k : Fin 4 → ℕ)
    (x : Fin 4 → K₄) : Matrix (Fin 4) (Fin 4) K₄ :=
  Matrix.of fun i l => (⇑σ)^[k i] (x l)

variable {K : Type} [Field K] [Fintype K] {K₄ : Type} [Field K₄] [Algebra K K₄]

theorem even_quartic_symplectic_four_cycle_coboundary [CharP K 2] [FiniteDimensional K K₄]
    (h4 : Module.finrank K K₄ = 4) (σ : K₄ ≃+* K₄) (hσ : ∀ b, σ b = b ^ Fintype.card K)
    (π : Equiv.Perm (Fin 4)) (hπ : π.cycleType = {4})
    (hJ : (π.permMatrix K)ᵀ * antiJ K * π.permMatrix K = antiJ K) :
    ∃ P ∈ spJ K₄,
      π.permMatrix K₄ * (P : Matrix (Fin 4) (Fin 4) K₄).map σ = P ∧
      π.permMatrix K₄ = ((P * (glAut σ P)⁻¹ : GL (Fin 4) K₄) : Matrix (Fin 4) (Fin 4) K₄) ∧
      (∀ g : GL (Fin 4) K₄, P * (glAut σ P)⁻¹ * glAut σ g * (P * (glAut σ P)⁻¹)⁻¹ =
        P * glAut σ (P⁻¹ * g * P) * P⁻¹) ∧
      ∀ g ∈ spJ K₄, (P * (glAut σ P)⁻¹ * glAut σ g * (P * (glAut σ P)⁻¹)⁻¹ = g ↔
        ∃ h ∈ spJ K, g = P * Matrix.GeneralLinearGroup.map (algebraMap K K₄) h * P⁻¹) := by
  classical
  have : CharP K₄ 2 := charP_of_injective_algebraMap (algebraMap K K₄).injective 2
  have : Finite K₄ := Module.finite_of_finite K
  have := Fintype.ofFinite K₄
  have h2 : (2 : K₄) = 0 := CharTwo.two_eq_zero
  have hcard : Fintype.card K₄ = Fintype.card K ^ 4 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := K₄), h4]
  have hit : ∀ (i : ℕ) (z : K₄), (⇑σ)^[i] z = z ^ (Fintype.card K ^ i) := by
    intro i z
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, hσ, ← pow_mul, pow_succ]
  have hσ4 : ∀ z, σ (σ (σ (σ z))) = z := fun z => by
    have := hit 4 z
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at this
    rw [this, ← hcard, FiniteField.pow_card]
  have hσK : ∀ t : K, σ (algebraMap K K₄ t) = algebraMap K K₄ t := fun t => by
    rw [hσ, ← map_pow, FiniteField.pow_card]
  have htr : ∀ z : K₄, algebraMap K K₄ (Algebra.trace K K₄ z) =
      z + σ z + σ (σ z) + σ (σ (σ z)) := fun z => by
    rw [FiniteField.algebraMap_trace_eq_sum_pow, h4, Nat.card_eq_fintype_card]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← hit]
    simp [Function.iterate_succ_apply']
  let σ2 : K₄ →ₗ[K] K₄ :=
    { toFun := fun y => σ (σ y)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by simp [Algebra.smul_def, hσK] }
  let B : BilinForm K K₄ := (Algebra.traceForm K K₄).compl₂ σ2
  have hB : ∀ y z, B y z = Algebra.trace K K₄ (y * σ (σ z)) := fun y z => rfl
  have hBmap : ∀ y z, algebraMap K K₄ (B y z) = y * σ (σ z) + σ y * σ (σ (σ z)) +
      σ (σ y) * z + σ (σ (σ y)) * σ z := fun y z => by
    rw [hB, htr]
    simp only [map_mul, hσ4]
  have hBalt : B.IsAlt := fun y => by
    apply (algebraMap K K₄).injective
    rw [hBmap, map_zero]
    linear_combination (y * σ (σ y) + σ y * σ (σ (σ y))) * h2
  have hBnd : B.Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hBalt.isRefl).mpr ?_
    intro y hy
    apply (traceForm_nondegenerate K K₄).1 y
    intro z
    have := hy (σ.symm (σ.symm z))
    rw [hB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this
    rw [Algebra.traceForm_apply]
    exact this
  obtain ⟨m, b, hdim, hb1, hb2, hb3⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      B hBalt hBnd
  obtain rfl : m = 2 := by omega
  have hskew : ∀ y z, B z y = B y z := fun y z => by
    rw [← LinearMap.IsAlt.neg hBalt y z, CharTwo.neg_eq]
  have hb4 : ∀ i j, B (b (Sum.inr j)) (b (Sum.inl i)) = if i = j then 1 else 0 := fun i j => by
    rw [hskew]; exact hb3 i j
  set x : Fin 4 → K₄ := ![b (Sum.inl 0), b (Sum.inl 1), b (Sum.inr 1), b (Sum.inr 0)] with hx
  have hBx : ∀ j l : Fin 4, B (x j) (x l) = antiJ K j l := by
    intro j l
    fin_cases j <;> fin_cases l <;> simp [hx, antiJ_apply, hb1, hb2, hb3, hb4]
  have hantimap : ∀ j l : Fin 4, antiJ K₄ j l = algebraMap K K₄ (antiJ K j l) := fun j l => by
    simp only [antiJ_apply]
    split_ifs <;> simp
  have hpair : ∀ j l : Fin 4, x j * σ (σ (x l)) + σ (x j) * σ (σ (σ (x l))) +
      σ (σ (x j)) * x l + σ (σ (σ (x j))) * σ (x l) = antiJ K₄ j l := fun j l => by
    rw [hantimap, ← hBx, hBmap]
  have hord : orderOf π = 4 := by
    rw [← Equiv.Perm.lcm_cycleType, hπ]
    rfl
  have hπ4 : π ^ 4 = 1 := by
    have := pow_orderOf_eq_one π
    rwa [hord] at this
  have hπ2 : π ^ 2 ≠ 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  have hrev := rev_of_permMatrix π hJ
  have hit2 : ∀ z, (⇑σ)^[2] z = σ (σ z) := fun z => rfl
  have hit3 : ∀ z, (⇑σ)^[3] z = σ (σ (σ z)) := fun z => rfl
  obtain ⟨P, hPJ, hMP⟩ : ∃ P : Matrix (Fin 4) (Fin 4) K₄, Pᵀ * antiJ K₄ * P = antiJ K₄ ∧
      π.permMatrix K₄ * P.map σ = P := by
    rcases perm_four_cases π hπ2 hπ4 hrev with rfl | rfl
    · refine ⟨rowMatrix σ ![0, 3, 1, 2] x, ?_, ?_⟩
      · ext j l
        rw [← hpair j l]
        simp [rowMatrix, Matrix.mul_apply, Fin.sum_univ_four, antiJ_apply, hit2, hit3]
        ring
      · ext i l
        fin_cases i <;>
          simp [rowMatrix, Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply,
            cyc4_apply, hit2, hit3, hσ4]
    · refine ⟨rowMatrix σ ![0, 1, 3, 2] x, ?_, ?_⟩
      · ext j l
        rw [← hpair j l]
        simp [rowMatrix, Matrix.mul_apply, Fin.sum_univ_four, antiJ_apply, hit2, hit3]
        ring
      · ext i l
        fin_cases i <;>
          simp [rowMatrix, Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply,
            cyc4_inv_apply, hit2, hit3, hσ4]
  have hPinv : (antiJ K₄ * Pᵀ * antiJ K₄) * P = 1 := by
    calc (antiJ K₄ * Pᵀ * antiJ K₄) * P = antiJ K₄ * (Pᵀ * antiJ K₄ * P) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJ, antiJ_mul_self]
  obtain ⟨Pg, hPgm⟩ : ∃ Pg : GL (Fin 4) K₄, (Pg : Matrix (Fin 4) (Fin 4) K₄) = P :=
    ⟨⟨P, antiJ K₄ * Pᵀ * antiJ K₄, mul_eq_one_comm.mp hPinv, hPinv⟩, rfl⟩
  have hPgS : Pg ∈ spJ K₄ := by rw [mem_spJ, hPgm]; exact hPJ
  have hMP' : π.permMatrix K₄ * ((glAut σ Pg : GL (Fin 4) K₄) : Matrix (Fin 4) (Fin 4) K₄) =
      P := by
    rw [coe_glAut, hPgm]
    exact hMP
  have hMeq : π.permMatrix K₄ =
      ((Pg * (glAut σ Pg)⁻¹ : GL (Fin 4) K₄) : Matrix (Fin 4) (Fin 4) K₄) := by
    rw [Units.val_mul, hPgm]
    rw [← hMP', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hconj : ∀ g : GL (Fin 4) K₄, Pg * (glAut σ Pg)⁻¹ * glAut σ g * (Pg * (glAut σ Pg)⁻¹)⁻¹ =
      Pg * glAut σ (Pg⁻¹ * g * Pg) * Pg⁻¹ := fun g => by
    simp only [map_mul, map_inv]
    group
  have hfixK : ∀ h : GL (Fin 4) K, glAut σ (Matrix.GeneralLinearGroup.map (algebraMap K K₄) h) =
      Matrix.GeneralLinearGroup.map (algebraMap K K₄) h := fun h => by
    apply Units.ext
    ext i j
    rw [coe_glAut, Matrix.map_apply]
    exact hσK _
  have hantiJmap : (antiJ K).map (algebraMap K K₄) = antiJ K₄ := by
    ext i j
    rw [Matrix.map_apply, hantimap]
  have hinj : Function.Injective
      (fun A : Matrix (Fin 4) (Fin 4) K => A.map (algebraMap K K₄)) :=
    Matrix.map_injective (algebraMap K K₄).injective
  refine ⟨Pg, hPgS, by rw [hPgm]; exact hMP, hMeq, hconj, fun g hg => ⟨fun hfix => ?_, ?_⟩⟩
  ·
    obtain ⟨h, hh⟩ : ∃ h : GL (Fin 4) K₄, h = Pg⁻¹ * g * Pg := ⟨_, rfl⟩
    have hσh : glAut σ h = h := by
      have e : Pg * glAut σ h * Pg⁻¹ = Pg * h * Pg⁻¹ := by
        rw [hh, ← hconj, hfix]
        group
      exact mul_left_cancel (mul_right_cancel e)
    have hσh' : glAut σ h⁻¹ = h⁻¹ := by rw [map_inv, hσh]
    have hent : ∀ (A : GL (Fin 4) K₄), glAut σ A = A → ∀ i j, ∃ t : K,
        algebraMap K K₄ t = (A : Matrix (Fin 4) (Fin 4) K₄) i j := fun A hA i j => by
      have := congrArg (fun B : GL (Fin 4) K₄ => (B : Matrix (Fin 4) (Fin 4) K₄) i j) hA
      simp only [coe_glAut, Matrix.map_apply] at this
      rw [hσ] at this
      exact mem_range_of_pow_card_eq this
    choose h₀ hh₀ using hent h hσh
    choose h₁ hh₁ using hent h⁻¹ hσh'
    have hmap0 : (Matrix.of h₀).map (algebraMap K K₄) = (h : Matrix (Fin 4) (Fin 4) K₄) := by
      ext i j
      exact hh₀ i j
    have hmap1 : (Matrix.of h₁).map (algebraMap K K₄) =
        ((h⁻¹ : GL (Fin 4) K₄) : Matrix (Fin 4) (Fin 4) K₄) := by
      ext i j
      exact hh₁ i j
    have h01 : Matrix.of h₀ * Matrix.of h₁ = 1 := hinj (by
      change (Matrix.of h₀ * Matrix.of h₁).map (algebraMap K K₄) = (1 : Matrix _ _ K).map _
      rw [Matrix.map_mul, hmap0, hmap1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)])
    have h10 : Matrix.of h₁ * Matrix.of h₀ = 1 := mul_eq_one_comm.mp h01
    set hg0 : GL (Fin 4) K := ⟨Matrix.of h₀, Matrix.of h₁, h01, h10⟩ with hhg0
    have hmapg : Matrix.GeneralLinearGroup.map (algebraMap K K₄) hg0 = h := by
      apply Units.ext
      exact hmap0
    refine ⟨hg0, ?_, ?_⟩
    · have hhS : h ∈ spJ K₄ := by
        rw [hh]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPgS) hg) hPgS
      show (Matrix.of h₀)ᵀ * antiJ K * Matrix.of h₀ = antiJ K
      apply hinj
      change ((Matrix.of h₀)ᵀ * antiJ K * Matrix.of h₀).map (algebraMap K K₄) =
        (antiJ K).map (algebraMap K K₄)
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hmap0, hantiJmap]
      exact hhS
    · rw [hmapg, hh]
      group
  · rintro ⟨h, -, rfl⟩
    rw [hconj]
    have e : Pg⁻¹ * (Pg * Matrix.GeneralLinearGroup.map (algebraMap K K₄) h * Pg⁻¹) * Pg =
        Matrix.GeneralLinearGroup.map (algebraMap K K₄) h := by group
    rw [e, hfixK]

end CFSG.RankThree.EvenQuartic
