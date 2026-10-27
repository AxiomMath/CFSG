module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierD
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTwisted

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

theorem mul_mul_eq_zero_of_anticomm {A : Type*} [Ring A] {g x : A} (hgx : g * x = -(x * g))
    (hg : g * g = 0) : g * x * g = 0 := by
  rw [hgx, neg_mul, mul_assoc, hg, mul_zero, neg_zero]

theorem mul_mul_mul_eq_zero_of_anticomm {A : Type*} [Ring A] {g x y : A}
    (hgx : g * x = -(x * g)) (hgy : g * y = -(y * g)) (hg : g * g = 0) : g * x * y * g = 0 := by
  rw [hgx, neg_mul, neg_mul, mul_assoc x g y, mul_assoc x, mul_mul_eq_zero_of_anticomm hgy hg,
    mul_zero, neg_zero]

namespace Fork

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) K P.W)

theorem ι_W_sq (x : P.W) : ι Q (x : V) * ι Q (x : V) = 0 := by
  rw [ι_sq_scalar, P.isotropic_W, map_zero]

theorem ι_W'_sq (y : P.W') : ι Q (y : V) * ι Q (y : V) = 0 := by
  rw [ι_sq_scalar, P.isotropic_W', map_zero]

theorem isOrtho_of_polar {x y : V} (h : QuadraticMap.polar Q x y = 0) : Q.IsOrtho x y := by
  rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply]
  exact h

theorem anticomm_W (x y : P.W) : ι Q (x : V) * ι Q (y : V) = -(ι Q (y : V) * ι Q (x : V)) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar (P.polar_W_eq_zero x y))

theorem anticomm_W' (x y : P.W') : ι Q (x : V) * ι Q (y : V) = -(ι Q (y : V) * ι Q (x : V)) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_of_polar (P.polar_W'_eq_zero x y))

theorem anticomm_basis_dual {i j : Fin n} (hij : i ≠ j) :
    ι Q (b i : V) * ι Q (P.dualVector b j : V) =
      -(ι Q (P.dualVector b j : V) * ι Q (b i : V)) :=
  ι_mul_ι_comm_of_isOrtho (P.isOrtho_basis_dualVector b hij)

theorem anticomm_dual_basis {i j : Fin n} (hij : i ≠ j) :
    ι Q (P.dualVector b j : V) * ι Q (b i : V) =
      -(ι Q (b i : V) * ι Q (P.dualVector b j : V)) := by
  rw [anticomm_basis_dual P b hij, neg_neg]

section Products

variable {i j : Fin n} (hij : i ≠ j)
include hij

theorem EE : ι Q (b i : V) * ι Q (P.dualVector b j : V) * (ι Q (b i : V) * ι Q (b j : V)) =
    0 := by
  rw [← mul_assoc, mul_mul_eq_zero_of_anticomm (anticomm_basis_dual P b hij) (ι_W_sq P _),
    zero_mul]

omit hij in
theorem EE' : ι Q (b i : V) * ι Q (b j : V) * (ι Q (b i : V) * ι Q (P.dualVector b j : V)) =
    0 := by
  rw [← mul_assoc, mul_mul_eq_zero_of_anticomm (anticomm_W P _ _) (ι_W_sq P _), zero_mul]

omit hij in
theorem EF : ι Q (b i : V) * ι Q (P.dualVector b j : V) *
    (ι Q (P.dualVector b j : V) * ι Q (P.dualVector b i : V)) = 0 := by
  rw [mul_assoc, ← mul_assoc (ι Q (P.dualVector b j : V)), ι_W'_sq P, zero_mul, mul_zero]

theorem FE : ι Q (P.dualVector b j : V) * ι Q (P.dualVector b i : V) *
    (ι Q (b i : V) * ι Q (P.dualVector b j : V)) = 0 := by
  rw [← mul_assoc]
  exact mul_mul_mul_eq_zero_of_anticomm (anticomm_W' P _ _)
    (anticomm_dual_basis P b hij) (ι_W'_sq P _)

omit hij in
theorem EF' : ι Q (b i : V) * ι Q (b j : V) * (ι Q (b j : V) * ι Q (P.dualVector b i : V)) =
    0 := by
  rw [mul_assoc, ← mul_assoc (ι Q (b j : V)), ι_W_sq P, zero_mul, mul_zero]

theorem FE' : ι Q (b j : V) * ι Q (P.dualVector b i : V) * (ι Q (b i : V) * ι Q (b j : V)) =
    0 := by
  rw [← mul_assoc]
  exact mul_mul_mul_eq_zero_of_anticomm (anticomm_basis_dual P b hij.symm) (anticomm_W P _ _)
    (ι_W_sq P _)

omit hij in
theorem FF : ι Q (b j : V) * ι Q (P.dualVector b i : V) *
    (ι Q (P.dualVector b j : V) * ι Q (P.dualVector b i : V)) = 0 := by
  rw [mul_assoc, ← mul_assoc (ι Q (P.dualVector b i : V)),
    mul_mul_eq_zero_of_anticomm (anticomm_W' P _ _) (ι_W'_sq P _), mul_zero]

theorem FF' : ι Q (P.dualVector b j : V) * ι Q (P.dualVector b i : V) *
    (ι Q (b j : V) * ι Q (P.dualVector b i : V)) = 0 := by
  rw [mul_assoc, ← mul_assoc (ι Q (P.dualVector b i : V)),
    mul_mul_eq_zero_of_anticomm (anticomm_dual_basis P b hij.symm) (ι_W'_sq P _), mul_zero]

end Products

section Bivectors

variable (hn : 2 ≤ n)

abbrev na : Fin n := ⟨n - 2, by omega⟩

abbrev nb : Fin n := ⟨n - 1, by omega⟩

theorem na_ne_nb : na hn ≠ nb hn := fun h => by
  have := congrArg Fin.val h
  simp only at this
  omega

theorem Ea_eq : P.typeDSimpleRootBivector b hn (na hn) =
    ι Q (b (na hn) : V) * ι Q (P.dualVector b (nb hn) : V) := by
  rw [SpinPolarizationData.typeDSimpleRootBivector_def, dite_eq_left (by simp; omega)]
  have h1 : (⟨(na hn : ℕ) + 1, by simp; omega⟩ : Fin n) = nb hn := Fin.ext (by simp; omega)
  rw [h1]

theorem Eb_eq : P.typeDSimpleRootBivector b hn (nb hn) =
    ι Q (b (na hn) : V) * ι Q (b (nb hn) : V) := by
  rw [SpinPolarizationData.typeDSimpleRootBivector_def, dite_eq_right (by simp; omega)]

theorem Fa_eq : P.typeDSimpleNegativeRootBivector b hn (na hn) =
    ι Q (b (nb hn) : V) * ι Q (P.dualVector b (na hn) : V) := by
  rw [SpinPolarizationData.typeDSimpleNegativeRootBivector_def, dite_eq_left (by simp; omega)]
  have h1 : (⟨(na hn : ℕ) + 1, by simp; omega⟩ : Fin n) = nb hn := Fin.ext (by simp; omega)
  rw [h1]

theorem Fb_eq : P.typeDSimpleNegativeRootBivector b hn (nb hn) =
    ι Q (P.dualVector b (nb hn) : V) * ι Q (P.dualVector b (na hn) : V) := by
  rw [SpinPolarizationData.typeDSimpleNegativeRootBivector_def, dite_eq_right (by simp; omega)]

theorem fork_products :
    P.typeDSimpleRootBivector b hn (na hn) * P.typeDSimpleRootBivector b hn (nb hn) = 0 ∧
    P.typeDSimpleRootBivector b hn (nb hn) * P.typeDSimpleRootBivector b hn (na hn) = 0 ∧
    P.typeDSimpleRootBivector b hn (na hn) *
      P.typeDSimpleNegativeRootBivector b hn (nb hn) = 0 ∧
    P.typeDSimpleNegativeRootBivector b hn (nb hn) *
      P.typeDSimpleRootBivector b hn (na hn) = 0 ∧
    P.typeDSimpleRootBivector b hn (nb hn) *
      P.typeDSimpleNegativeRootBivector b hn (na hn) = 0 ∧
    P.typeDSimpleNegativeRootBivector b hn (na hn) *
      P.typeDSimpleRootBivector b hn (nb hn) = 0 ∧
    P.typeDSimpleNegativeRootBivector b hn (na hn) *
      P.typeDSimpleNegativeRootBivector b hn (nb hn) = 0 ∧
    P.typeDSimpleNegativeRootBivector b hn (nb hn) *
      P.typeDSimpleNegativeRootBivector b hn (na hn) = 0 := by
  have h := na_ne_nb hn
  simp only [Ea_eq, Eb_eq, Fa_eq, Fb_eq]
  exact ⟨EE P b h, EE' P b, EF P b, FE P b h, EF' P b, FE' P b h, FF P b, FF' P b h⟩

end Bivectors

end Fork

namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier

variable (n : ℕ) (hn : 4 ≤ n)

theorem E_eq_spinAction (i : Fin n) : E n hn i = spinAction _ (polarization n)
    ((polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) i) := by
  rw [E, ρL_apply]
  exact (polarization n).typeDSpinRep_serreE_eq_spinAction (polarizationBasis n) hn i

theorem F_eq_spinAction (i : Fin n) : F n hn i = spinAction _ (polarization n)
    ((polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) i) := by
  rw [F, ρL_apply]
  exact (polarization n).typeDSpinRep_serreF_eq_spinAction (polarizationBasis n) hn i

theorem hasIntMatrix_E (i : Fin n) :
    HasIntMatrix (latticeBasis n) (E n hn i) (rootIntMatrix n hn (.inl i)) := fun s => by
  rw [E_eq]
  exact rep_rootGenerator_latticeBasis_eq_sum n hn (.inl i) s

theorem hasIntMatrix_F (i : Fin n) :
    HasIntMatrix (latticeBasis n) (F n hn i) (rootIntMatrix n hn (.inr i)) := fun s => by
  rw [F_eq]
  exact rep_rootGenerator_latticeBasis_eq_sum n hn (.inr i) s

omit hn in
theorem intMatrix_mul_eq_zero {T T' : Module.End ℚ (V n)} {X X' : Matrix _ _ ℤ}
    (h : HasIntMatrix (latticeBasis n) T X) (h' : HasIntMatrix (latticeBasis n) T' X')
    (h0 : T * T' = 0) : X * X' = 0 :=
  (h.mul h').unique (h0 ▸ HasIntMatrix.zero)

abbrev forkA : Fin n := ⟨n - 2, by omega⟩

abbrev forkB : Fin n := ⟨n - 1, by omega⟩

theorem isDisjointPair_fork (K : Type) [Field K] :
    (rootData n hn K).IsDisjointPair (forkA n hn) (forkB n hn) := by
  have key : ∀ {T T' : Module.End ℚ (V n)} {X X' : Matrix _ _ ℤ},
      HasIntMatrix (latticeBasis n) T X → HasIntMatrix (latticeBasis n) T' X' → T * T' = 0 →
        intMap K X * intMap K X' = 0 := fun h h' h0 => by
    rw [← intMap_mul, intMatrix_mul_eq_zero n h h' h0, intMap_zero]
  have hEa := hasIntMatrix_E n hn (forkA n hn)
  have hEb := hasIntMatrix_E n hn (forkB n hn)
  have hFa := hasIntMatrix_F n hn (forkA n hn)
  have hFb := hasIntMatrix_F n hn (forkB n hn)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    Fork.fork_products (polarization n) (polarizationBasis n) (by omega : 2 ≤ n)
  refine ⟨key hEa hEb ?_, key hEb hEa ?_, key hEa hFb ?_, key hFb hEa ?_, key hEb hFa ?_,
    key hFa hEb ?_, key hFa hFb ?_, key hFb hFa ?_⟩
  all_goals simp only [E_eq_spinAction, F_eq_spinAction, ← map_mul]
  · rw [h1, map_zero]
  · rw [h2, map_zero]
  · rw [h3, map_zero]
  · rw [h4, map_zero]
  · rw [h5, map_zero]
  · rw [h6, map_zero]
  · rw [h7, map_zero]
  · rw [h8, map_zero]

end CarrierD

end CFSG.RankThree.PartTwo.Census.Spin
