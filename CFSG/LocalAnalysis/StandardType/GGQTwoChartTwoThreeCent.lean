module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

@[expose] noncomputable def qTwoChartTwoThree_diag (c : Fin m → F0ˣ) : GL (Fin m) F0 where
  val := Matrix.diagonal fun i => ((c i : F0ˣ) : F0)
  inv := Matrix.diagonal fun i => (((c i)⁻¹ : F0ˣ) : F0)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp

@[expose] def qTwoChartTwoThree_induces (ψ : Su F0 2 1 m →* G) (b : G) (c : Fin m → F0ˣ) : Prop :=
  ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
    (u' : GL (Fin m) F0) =
      qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ ∧
    ψ u' = b * ψ u * b⁻¹

private theorem qTwoChartTwoThree_diag_val (c : Fin m → F0ˣ) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun i => (c i : F0) :=
  rfl

private theorem qTwoChartTwoThree_diag_conjTr_mul (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Fintype.card F0 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF0
  have h3 : ∀ i : Fin m, (c i : F0) ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (c i : F0) (c i).ne_zero
    rw [hcard] at h
    simpa using h
  rw [qTwoChartTwoThree_diag_val, CFSG.LieType.Steinberg.conjTr_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [show (c i : F0) ^ 2 * (c i : F0) = (c i : F0) ^ 3 by ring, h3 i]

private theorem qTwoChartTwoThree_matrix_ext_mulVec {A B : Matrix (Fin m) (Fin m) F0}
    (h : ∀ i : Fin m, A *ᵥ Pi.single i 1 = B *ᵥ Pi.single i 1) : A = B := by
  ext i j
  have h' := congrFun (h j) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h'

private theorem qTwoChartTwoThree_single_smul (i : Fin m) (x : F0) :
    Pi.single i x = x • Pi.single i 1 := by
  simpa using (Pi.single_smul' i x (1 : F0))

theorem qTwoChartTwoThree_diag_conj_mem (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ)
    (u : Su F0 2 1 m) : ∃ u' : Su F0 2 1 m, (u' : GL (Fin m) F0) =
      qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ := by
  have hσ : ∀ x : F0,
      CFSG.LieType.BorelTits.unitaryInvolution F0 2 1
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 x) = x :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive (by simpa using hF0)
  have hD : CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 :=
    qTwoChartTwoThree_diag_conjTr_mul hF0 c
  exact ⟨⟨qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹,
    CFSG.LieType.Steinberg.conj_mem_SUid hσ hD u.2⟩, rfl⟩

theorem qTwoChartTwoThree_induces_of_ordModel {Bs L : Subgroup G} {ψ : Su F0 2 1 m →* G}
    (hψ : QTwoOrdModel Bs L ψ) (b : ↥Bs) :
    ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (b : G) c := by
  rcases hψ.2.2 b with ⟨g, ⟨d, hgd⟩, hg⟩
  have hdet : (∏ i, d i) ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det (show (g : Matrix (Fin m) (Fin m) F0) *
        ((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    rw [Matrix.det_mul, Matrix.det_one, hgd, Matrix.det_diagonal, hzero, zero_mul] at h
    exact one_ne_zero h.symm
  let c : Fin m → F0ˣ :=
    fun i => Units.mk0 (d i) (Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i))
  refine ⟨c, ?_⟩
  have hdiag : qTwoChartTwoThree_diag c = g := by
    apply Units.ext
    rw [qTwoChartTwoThree_diag_val, hgd]
    rfl
  intro u
  rcases hg u with ⟨u', hu'mat, hu'ψ⟩
  exact ⟨u', by rw [hdiag, hu'mat], hu'ψ⟩

theorem qTwoChartTwoThree_perm_conj_diag {u : Su F0 2 1 m} {σ : Equiv.Perm (Fin m)}
    (hu : ∀ i : Fin m, ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single (σ i) 1) (c : Fin m → F0ˣ) :
    (u : GL (Fin m) F0) * qTwoChartTwoThree_diag c * (u : GL (Fin m) F0)⁻¹ =
      qTwoChartTwoThree_diag fun i => c (σ.symm i) := by
  have hkey : (u : GL (Fin m) F0) * qTwoChartTwoThree_diag c =
      qTwoChartTwoThree_diag (fun i => c (σ.symm i)) * (u : GL (Fin m) F0) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, qTwoChartTwoThree_diag_val, qTwoChartTwoThree_diag_val]
    apply qTwoChartTwoThree_matrix_ext_mulVec
    intro i
    conv_lhs => rw [← Matrix.mulVec_mulVec]
    conv_rhs => rw [← Matrix.mulVec_mulVec]
    rw [Matrix.diagonal_mulVec_single, hu i, Matrix.diagonal_mulVec_single]
    simp only [mul_one, Equiv.symm_apply_apply]
    rw [qTwoChartTwoThree_single_smul, Matrix.mulVec_smul, hu i]
    conv_rhs => rw [qTwoChartTwoThree_single_smul]
  rw [hkey]
  group

theorem qTwoChartTwoThree_induces_conj {ψ : Su F0 2 1 m →* G} {b : G} {c : Fin m → F0ˣ}
    (hb : qTwoChartTwoThree_induces ψ b c) {u : Su F0 2 1 m} {σ : Equiv.Perm (Fin m)}
    (hu : ∀ i : Fin m, ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single (σ i) 1) :
    qTwoChartTwoThree_induces ψ (ψ u * b * (ψ u)⁻¹) fun i => c (σ.symm i) := by
  intro v
  let w : Su F0 2 1 m := u⁻¹ * v * u
  rcases hb w with ⟨w', hw'mat, hw'ψ⟩
  have hwcoe : (w : GL (Fin m) F0) =
      (u : GL (Fin m) F0)⁻¹ * (v : GL (Fin m) F0) * (u : GL (Fin m) F0) := by
    simp [w]
  have hv : (v : GL (Fin m) F0) =
      (u : GL (Fin m) F0) * (w : GL (Fin m) F0) * (u : GL (Fin m) F0)⁻¹ := by
    rw [hwcoe]
    group
  have hwψ : ψ w = (ψ u)⁻¹ * ψ v * ψ u := by
    simp [w]
  refine ⟨u * w' * u⁻¹, ?_, ?_⟩
  · have hcoe : ((u * w' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) =
        (u : GL (Fin m) F0) * (w' : GL (Fin m) F0) * (u : GL (Fin m) F0)⁻¹ := by
      simp
    rw [hcoe, hw'mat, ← qTwoChartTwoThree_perm_conj_diag hu c, hv]
    group
  · have hcoeψ : ψ (u * w' * u⁻¹) = ψ u * ψ w' * (ψ u)⁻¹ := by
      simp
    rw [hcoeψ, hw'ψ, hwψ]
    group

theorem qTwoChartTwoThree_induces_unique {ψ : Su F0 2 1 m →* G} {b₁ b₂ : G} {c : Fin m → F0ˣ}
    (h₁ : qTwoChartTwoThree_induces ψ b₁ c) (h₂ : qTwoChartTwoThree_induces ψ b₂ c)
    (v : Su F0 2 1 m) : b₁ * ψ v * b₁⁻¹ = b₂ * ψ v * b₂⁻¹ := by
  rcases h₁ v with ⟨u₁, hmat₁, hψ₁⟩
  rcases h₂ v with ⟨u₂, hmat₂, hψ₂⟩
  have hsub : u₁ = u₂ := Subtype.ext (by rw [hmat₁, hmat₂])
  rw [← hψ₁, ← hψ₂, hsub]

end CFSG.StandardType.QTwo

end
