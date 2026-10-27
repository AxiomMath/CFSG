module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix Polynomial

theorem exists_conj_diagonal_of_pow_three {ι : Type} [Fintype ι] [DecidableEq ι] {E' : Type}
    [Field E'] {ω : E'} (hω : IsPrimitiveRoot ω 3) (B : Matrix ι ι E') (hB : B ^ 3 = 1) :
    ∃ (T : GL ι E') (d : ι → E'),
      (T : Matrix ι ι E') * B * ((T⁻¹ : GL ι E') : Matrix ι ι E') = diagonal d ∧
        ∀ i, d i ^ 3 = 1 := by
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hω
    (fun _ : Unit => Matrix.toLinAlgEquiv' B) (fun _ _ => Commute.refl _)
    (fun _ => by rw [← map_pow, hB, map_one])
  let e : Fin (Module.finrank E' (ι → E')) ≃ ι :=
    (finCongr (Module.finrank_pi E')).trans (Fintype.equivFin ι).symm
  let b' : Module.Basis ι E' (ι → E') := b.reindex e
  let d : ι → E' := fun i => μ () (e.symm i)
  have hb' : ∀ j, B.mulVec (b' j) = d j • b' j := by
    intro j
    have := hb () (e.symm j)
    simpa [b', d, Module.Basis.reindex_apply] using this
  let P : Matrix ι ι E' := (Pi.basisFun E' ι).toMatrix b'
  have hPi : Invertible P := Module.Basis.invertibleToMatrix (Pi.basisFun E' ι) b'
  have hBP : B * P = P * diagonal d := by
    ext a j
    have h := congrFun (hb' j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    have hpow : ∀ m : ℕ, (B ^ m).mulVec (b' i) = d i ^ m • b' i := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_smul, ih, smul_smul, pow_succ]
        ring_nf
    have h3 := hpow 3
    rw [hB, Matrix.one_mulVec] at h3
    have hne : b' i ≠ 0 := b'.ne_zero i
    have h4 : (1 - d i ^ 3) • b' i = 0 := by
      rw [sub_smul, one_smul, ← h3, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact (sub_eq_zero.mp h5).symm
    · exact absurd h5 hne
  let Pu : GL ι E' := unitOfInvertible P
  refine ⟨Pu⁻¹, d, ?_, hd3⟩
  have h1 : ((Pu⁻¹ : GL ι E') : Matrix ι ι E') = ⅟P := rfl
  have h2 : (((Pu⁻¹)⁻¹ : GL ι E') : Matrix ι ι E') = P := by simp [Pu]
  rw [h1, h2, Matrix.mul_assoc, hBP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]

theorem exists_finite_extension_with_roots {E : Type} [Field E] [Finite E] (h3 : (3 : E) ≠ 0)
    (c : Eˣ) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E') (φ : E →+* E') (ω γ : E'),
      IsPrimitiveRoot ω 3 ∧ γ ^ 3 = φ (c : E) ∧ ∀ p : ℕ, CharP E p → CharP E' p := by
  classical
  set g : E[X] := X ^ 2 + X + 1 with hg
  set h : E[X] := X ^ 3 - C (c : E) with hh
  set f : E[X] := g * h with hf
  have hg0 : g ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [g] at this
  have hh0 : h ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [h] at this
  have hfne : f ≠ 0 := mul_ne_zero hg0 hh0
  haveI : Module.Finite E f.SplittingField := inferInstance
  haveI : Finite f.SplittingField := Module.finite_of_finite E
  refine ⟨f.SplittingField, inferInstance, inferInstance,
    algebraMap E f.SplittingField, ?_⟩
  set φ : E →+* f.SplittingField := algebraMap E f.SplittingField with hφ
  have hsplit : (f.map φ).Splits := Polynomial.SplittingField.splits f
  have hgs : (g.map φ).Splits := Polynomial.Splits.of_dvd hsplit (Polynomial.map_ne_zero hfne)
    (Polynomial.map_dvd φ (dvd_mul_right g h))
  have hhs : (h.map φ).Splits := Polynomial.Splits.of_dvd hsplit (Polynomial.map_ne_zero hfne)
    (Polynomial.map_dvd φ (dvd_mul_left h g))
  obtain ⟨ω, hω⟩ := hgs.exists_eval_eq_zero (by
    simp only [g, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    rw [show (X ^ 2 + X + 1 : f.SplittingField[X]).degree = 2 by compute_degree!]
    decide)
  obtain ⟨γ, hγ⟩ := hhs.exists_eval_eq_zero (by
    simp only [h, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [show (X ^ 3 - C (φ (c : E)) : f.SplittingField[X]).degree = 3 by compute_degree!]
    decide)
  have hω2 : ω ^ 2 + ω + 1 = 0 := by simpa [g] using hω
  have hγ3 : γ ^ 3 = φ (c : E) := by
    have : γ ^ 3 - φ (c : E) = 0 := by simpa [h] using hγ
    exact sub_eq_zero.mp this
  refine ⟨ω, γ, ?_, hγ3, fun p hp => charP_of_injective_algebraMap
    (algebraMap E f.SplittingField).injective p⟩
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1] at hω2
    have h3' : (3 : f.SplittingField) = 0 := by
      have : (1 : f.SplittingField) ^ 2 + 1 + 1 = 3 := by norm_num
      rw [← this]
      simpa using hω2
    apply h3
    apply φ.injective
    rw [map_zero, map_ofNat]
    exact h3'
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have := IsPrimitiveRoot.orderOf ω
  rwa [hord] at this

theorem exists_blockDiagonalization {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [Field E]
    [Finite E] (h3 : (3 : E) ≠ 0) {K : Type} [Group K] (ρ : K →* GL ι E) (B : GL ι E) (c : Eˣ)
    (hB : ((B : GL ι E) : Matrix ι ι E) ^ 3 = (c : E) • (1 : Matrix ι ι E))
    (hcomm : ∀ k, ρ k * B = B * ρ k) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E') (φ : E →+* E') (μ : ι → E')
      (M : K →* Matrix ι ι E'),
      (∀ p : ℕ, CharP E p → CharP E' p) ∧
      (∀ k₁ k₂, M k₁ = M k₂ → ρ k₁ = ρ k₂) ∧
      (∀ k i j, μ i ≠ μ j → M k i j = 0) ∧ (∀ i, μ i ^ 3 = φ (c : E)) ∧
      ∏ i, μ i = φ (B : Matrix ι ι E).det ∧
      ∑ i, μ i = φ (B : Matrix ι ι E).trace ∧
      ∑ i, (μ i)⁻¹ = φ ((B⁻¹ : GL ι E) : Matrix ι ι E).trace ∧
      ((∀ i j, μ i = μ j) → ∃ b : E, (B : Matrix ι ι E) = b • (1 : Matrix ι ι E)) ∧
      (∀ (k : K) (z : E), ((ρ k : GL ι E) : Matrix ι ι E) = z • (1 : Matrix ι ι E) →
        M k = φ z • (1 : Matrix ι ι E')) := by
  classical
  obtain ⟨E', hF, hfin, φ, ω, γ, hω, hγ, hcharE⟩ := exists_finite_extension_with_roots h3 c
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0] at hγ
    have : φ (c : E) = 0 := by rw [← hγ]; ring
    exact c.ne_zero (φ.injective (by rw [this, map_zero]))
  set Bm : Matrix ι ι E' := (B : Matrix ι ι E).map φ with hBm
  have hBm3 : Bm ^ 3 = φ (c : E) • (1 : Matrix ι ι E') := by
    have h1 : ((B : Matrix ι ι E) ^ 3).map φ =
        ((c : E) • (1 : Matrix ι ι E)).map φ :=
      congrArg (fun X : Matrix ι ι E => X.map φ) hB
    have h2 : ((B : Matrix ι ι E) ^ 3).map φ = Bm ^ 3 := by
      have := map_pow (RingHom.mapMatrix (m := ι) φ) (B : Matrix ι ι E) 3
      simpa [RingHom.mapMatrix_apply, hBm] using this
    rw [← h2, h1]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set B' : Matrix ι ι E' := γ⁻¹ • Bm with hB'
  have hB'3 : B' ^ 3 = 1 := by
    rw [hB', _root_.smul_pow, hBm3, smul_smul, ← hγ, ← mul_pow, inv_mul_cancel₀ hγ0, one_pow,
      one_smul]
  obtain ⟨T, d, hTd, hd3⟩ := exists_conj_diagonal_of_pow_three hω B' hB'3
  set Tm : Matrix ι ι E' := (T : Matrix ι ι E') with hTm
  set Ti : Matrix ι ι E' := ((T⁻¹ : GL ι E') : Matrix ι ι E')
    with hTi
  have hTiT : Ti * Tm = 1 := by rw [hTi, hTm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTTi : Tm * Ti = 1 := by rw [hTi, hTm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set μ : ι → E' := fun i => γ * d i with hμ
  have hBmB' : Bm = γ • B' := by
    rw [hB', smul_smul, mul_inv_cancel₀ hγ0, one_smul]
  have hTB : Tm * Bm * Ti = diagonal μ := by
    rw [hBmB', Matrix.mul_smul, Matrix.smul_mul, hTd, hμ]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  set ρ' : K →* GL ι E' := (Matrix.GeneralLinearGroup.map φ).comp ρ with hρ'
  set M : K →* Matrix ι ι E' :=
    (Units.coeHom (Matrix ι ι E')).comp ((MulAut.conj T).toMonoidHom.comp ρ')
    with hM
  have hρ'k : ∀ k, ((ρ' k : GL ι E') : Matrix ι ι E') =
      ((ρ k : GL ι E) : Matrix ι ι E).map φ := fun k => rfl
  have hMk : ∀ k, M k = Tm * ((ρ' k : GL ι E') : Matrix ι ι E') * Ti := by
    intro k
    simp [hM, MulAut.conj_apply, hTm, hTi]
  have hμ3 : ∀ i, μ i ^ 3 = φ (c : E) := by
    intro i
    rw [hμ]
    simp only []
    rw [mul_pow, hγ, hd3 i, mul_one]
  have hμ0 : ∀ i, μ i ≠ 0 := by
    intro i h0
    have := hμ3 i
    rw [h0] at this
    have hc0 : φ (c : E) ≠ 0 := fun h => c.ne_zero (φ.injective (by rw [h, map_zero]))
    exact hc0 (by rw [← this]; ring)
  refine ⟨E', hF, hfin, φ, μ, M, hcharE, ?_, ?_, hμ3, ?_, ?_, ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    have h1 : ρ' k₁ = ρ' k₂ := by
      have h2 : (T * ρ' k₁ * T⁻¹ : GL ι E') = T * ρ' k₂ * T⁻¹ := by
        apply Units.ext
        simpa [hMk, hTm, hTi] using h
      simpa using h2
    have h3 : ((ρ k₁ : GL ι E) : Matrix ι ι E).map φ =
        ((ρ k₂ : GL ι E) : Matrix ι ι E).map φ := by
      rw [← hρ'k, ← hρ'k, h1]
    exact Units.ext (Matrix.map_injective φ.injective h3)
  · intro k i j hij
    have hc : ((ρ' k : GL ι E') : Matrix ι ι E') * Bm =
        Bm * ((ρ' k : GL ι E') : Matrix ι ι E') := by
      have := congrArg (fun X : GL ι E => (X : Matrix ι ι E).map φ) (hcomm k)
      simp only [Units.val_mul] at this
      rw [hρ'k, hBm]
      simpa [Matrix.map_mul] using this
    have hMD : M k * diagonal μ = diagonal μ * M k := by
      rw [← hTB, hMk]
      calc Tm * (ρ' k : Matrix _ _ E') * Ti * (Tm * Bm * Ti)
          = Tm * ((ρ' k : Matrix _ _ E') * Bm) * Ti := by
            have : Tm * (ρ' k : Matrix _ _ E') * Ti * (Tm * Bm * Ti) =
                Tm * (ρ' k : Matrix _ _ E') * (Ti * Tm) * Bm * Ti := by
              simp only [Matrix.mul_assoc]
            rw [this, hTiT, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = Tm * (Bm * (ρ' k : Matrix _ _ E')) * Ti := by rw [hc]
        _ = (Tm * Bm * Ti) * (Tm * (ρ' k : Matrix _ _ E') * Ti) := by
            have : Tm * Bm * Ti * (Tm * (ρ' k : Matrix _ _ E') * Ti) =
                Tm * Bm * (Ti * Tm) * (ρ' k : Matrix _ _ E') * Ti := by
              simp only [Matrix.mul_assoc]
            rw [this, hTiT, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    have h1 := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    by_contra hne
    apply hij
    have h2 : M k i j * (μ j - μ i) = 0 := by
      rw [mul_sub, h1, mul_comm (M k i j) (μ i), sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hne
    · exact (sub_eq_zero.mp h3).symm
  · have h1 : (diagonal μ).det = ∏ i, μ i := Matrix.det_diagonal
    have h2 : (diagonal μ).det = Bm.det := by
      rw [← hTB]
      exact Matrix.det_units_conj T Bm
    have h3 : φ (B : Matrix ι ι E).det = Bm.det := RingHom.map_det φ _
    rw [← h1, h2, h3]
  · have h1 : (diagonal μ).trace = ∑ i, μ i := Matrix.trace_diagonal μ
    have h2 : (diagonal μ).trace = Bm.trace := by
      rw [← hTB]
      exact Matrix.trace_units_conj T Bm
    have h3 : φ (B : Matrix ι ι E).trace = Bm.trace := by
      simp [Matrix.trace, hBm, map_sum]
    rw [← h1, h2, h3]
  · set X : Matrix ι ι E' :=
      ((B⁻¹ : GL ι E) : Matrix ι ι E).map φ with hX
    have hXB : X * Bm = 1 := by
      have h0 : ((B⁻¹ : GL ι E) : Matrix ι ι E) *
          (B : Matrix ι ι E) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h := congrArg (fun Y : Matrix ι ι E => Y.map φ) h0
      have h' : X * Bm = (1 : Matrix ι ι E).map φ := by
        rw [← h]
        rw [hX, hBm, Matrix.map_mul]
      rw [h']
      exact Matrix.map_one φ (map_zero φ) (map_one φ)
    have hdiag : diagonal μ * diagonal (fun i => (μ i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hμ0 i]
      · simp [hij]
    have hTXT : Tm * X * Ti = diagonal (fun i => (μ i)⁻¹) := by
      have h1 : (Tm * X * Ti) * diagonal μ = 1 := by
        rw [← hTB]
        have e1 : Tm * X * Ti * (Tm * Bm * Ti) = Tm * X * (Ti * Tm) * Bm * Ti := by
          simp only [Matrix.mul_assoc]
        rw [e1, hTiT, Matrix.mul_one]
        have e2 : Tm * X * Bm * Ti = Tm * (X * Bm) * Ti := by simp only [Matrix.mul_assoc]
        rw [e2, hXB, Matrix.mul_one, hTTi]
      calc Tm * X * Ti = Tm * X * Ti * (diagonal μ * diagonal (fun i => (μ i)⁻¹)) := by
            rw [hdiag, Matrix.mul_one]
        _ = (Tm * X * Ti * diagonal μ) * diagonal (fun i => (μ i)⁻¹) := by
            rw [Matrix.mul_assoc _ (diagonal μ)]
        _ = diagonal (fun i => (μ i)⁻¹) := by rw [h1, Matrix.one_mul]
    have h2 : (diagonal (fun i => (μ i)⁻¹)).trace = X.trace := by
      rw [← hTXT]
      exact Matrix.trace_units_conj T X
    have h3 : φ ((B⁻¹ : GL ι E) : Matrix ι ι E).trace = X.trace := by
      simp [Matrix.trace, hX, map_sum]
    rw [h3, ← h2, Matrix.trace_diagonal]
  · intro hconst
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · exact ⟨1, Subsingleton.elim _ _⟩
    · have hD : diagonal μ = (μ i₀) • (1 : Matrix ι ι E') := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hconst i i₀]
        · simp [hij]
      have hBm1 : Bm = (μ i₀) • (1 : Matrix ι ι E') := by
        have e1 : Bm = Ti * (Tm * Bm * Ti) * Tm := by
          calc Bm = (Ti * Tm) * Bm * (Ti * Tm) := by
                rw [hTiT, Matrix.one_mul, Matrix.mul_one]
            _ = Ti * (Tm * Bm * Ti) * Tm := by simp only [Matrix.mul_assoc]
        rw [e1, hTB, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTiT]
      refine ⟨(B : Matrix ι ι E) i₀ i₀, ?_⟩
      ext i j
      have h := congrFun (congrFun hBm1 i) j
      have h0 := congrFun (congrFun hBm1 i₀) i₀
      simp only [hBm, Matrix.map_apply] at h h0
      by_cases hij : i = j
      · subst hij
        have : φ ((B : Matrix ι ι E) i i) = φ ((B : Matrix ι ι E) i₀ i₀) := by
          rw [h, h0]
          simp
        simpa using φ.injective this
      · have : φ ((B : Matrix ι ι E) i j) = φ 0 := by
          rw [h, map_zero]
          simp [hij]
        simpa [hij] using φ.injective this
  · intro k z hz
    rw [hMk, hρ'k, hz]
    have hmap : (z • (1 : Matrix ι ι E)).map φ = φ z • (1 : Matrix ι ι E') := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hTTi]

end CFSG.RankThree.PartTwo.Sec4.HeringOF
