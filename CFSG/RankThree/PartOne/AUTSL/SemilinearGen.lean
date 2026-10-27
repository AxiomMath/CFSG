module

public import CFSG.RankThree.PartOne.AUTSL.SemilinearRel

public section

namespace CFSG.RankThree.PartOne.AUTSL

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K K' : Type*} [Field K] [Finite K] [CharP K 2]
  [Field K'] [CharP K' 2] [Algebra K K'] {G : Type*} [Group G]

theorem exists_relation_of_form (ρ : G →* Matrix ι ι K) (β : MulAut G) (A : GL ι K)
    (σ : K ≃+* K)
    (hform : ∀ g : G, ρ (β g) =
      (A : Matrix ι ι K) * (ρ g).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K)) (P : GL ι K') :
    ∃ (j : ℕ) (A₃ : Matrix ι ι K'), IsUnit A₃ ∧ ∀ (g : G) (d : ι → K'),
      (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
          ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal d →
        (P : Matrix ι ι K') * (ρ (β g)).map (algebraMap K K') *
          ((P⁻¹ : GL ι K') : Matrix ι ι K') * A₃ =
          A₃ * Matrix.diagonal (fun i => d i ^ 2 ^ j) := by
  obtain ⟨j, hj⟩ := exists_ringEquiv_eq_pow_two σ
  have : ExpChar K' 2 := ExpChar.prime Nat.prime_two
  let ι' : K →+* K' := algebraMap K K'
  let σ' : K' →+* K' := iterateFrobenius K' 2 j
  have hσ' : ∀ x, σ' x = x ^ 2 ^ j := iterateFrobenius_def 2 j
  have hσσ' : ∀ x : K, σ' (ι' x) = ι' (σ x) := fun x => by rw [hσ', hj x, map_pow]
  let ιM : Matrix ι ι K →+* Matrix ι ι K' := ι'.mapMatrix
  let σM : Matrix ι ι K' →+* Matrix ι ι K' := σ'.mapMatrix
  have hιM : ∀ M : Matrix ι ι K, ιM M = M.map (algebraMap K K') := fun M => rfl
  have hσM : ∀ M : Matrix ι ι K', σM M = M.map σ' := fun M => rfl
  have hcomm : ∀ M : Matrix ι ι K, ιM (M.map σ) = σM (ιM M) := fun M => by
    ext i k
    exact (hσσ' _).symm
  set Pm : Matrix ι ι K' := (P : Matrix ι ι K') with hPm
  set Pi : Matrix ι ι K' := ((P⁻¹ : GL ι K') : Matrix ι ι K') with hPi
  have hPPi : Pm * Pi = 1 := Units.mul_inv P
  have hPiP : Pi * Pm = 1 := Units.inv_mul P
  set C : Matrix ι ι K' := ιM (A : Matrix ι ι K) with hC
  set Ci : Matrix ι ι K' := ιM ((A⁻¹ : GL ι K) : Matrix ι ι K) with hCi
  have hCiC : Ci * C = 1 := by rw [hC, hCi, ← map_mul, Units.inv_mul, map_one]
  have hCCi : C * Ci = 1 := by rw [hC, hCi, ← map_mul, Units.mul_inv, map_one]
  have hCunit : IsUnit C := ⟨⟨C, Ci, hCCi, hCiC⟩, rfl⟩
  refine ⟨j, Pm * C * σM Pi, ?_, fun g d hd => ?_⟩
  · have hPu : IsUnit Pm := P.isUnit
    have hPiu : IsUnit (σM Pi) := by
      refine ⟨⟨σM Pi, σM Pm, ?_, ?_⟩, rfl⟩
      · rw [← map_mul, hPiP, map_one]
      · rw [← map_mul, hPPi, map_one]
    exact (hPu.mul hCunit).mul hPiu
  · have hβ : ιM (ρ (β g)) = C * σM (ιM (ρ g)) * Ci := by
      rw [hform g, map_mul, map_mul, hcomm]
    have hd' : Matrix.diagonal (fun i => d i ^ 2 ^ j) = σM (Pm * ιM (ρ g) * Pi) := by
      have : Pm * ιM (ρ g) * Pi = Matrix.diagonal d := hd
      rw [this, hσM, Matrix.diagonal_map (map_zero σ')]
      simp only [hσ']
    show Pm * ιM (ρ (β g)) * Pi * (Pm * C * σM Pi) = _
    rw [hβ, hd']
    exact conj_rel_zero σM Pm Pi C Ci _ hPiP hCiC

theorem exists_E_relation_gen {E : Type*} [CommGroup E] (ρG : G →* Matrix ι ι K)
    (ρ : E →* G) (β : MulAut G) (A : GL ι K) (σ : K ≃+* K)
    (hform : ∀ g : G, ρG (β g) =
      (A : Matrix ι ι K) * (ρG g).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K))
    (P : GL ι K') (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρG (ρ g)).map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K')) :
    ∃ (j e : ℕ) (A₃ : Matrix ι ι K'), IsUnit A₃ ∧ (e = 1 ∨ e = 4) ∧
      ∀ g : E, (P : Matrix ι ι K') * (ρG (β (ρ g))).map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K') * A₃ =
        A₃ * Matrix.diagonal (fun i => (((f i g : K'ˣ) : K') ^ e) ^ 2 ^ j) := by
  obtain ⟨j, A₃, hA₃, h⟩ := exists_relation_of_form ρG β A σ hform P
  refine ⟨j, 1, A₃, hA₃, Or.inl rfl, fun g => ?_⟩
  have := h (ρ g) (fun i => ((f i g : K'ˣ) : K')) (hD g)
  simpa only [pow_one] using this

end Gen

end CFSG.RankThree.PartOne.AUTSL
