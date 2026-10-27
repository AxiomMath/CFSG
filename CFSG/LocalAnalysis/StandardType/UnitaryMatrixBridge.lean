module

public import CFSG.LocalAnalysis.StandardType.UnitaryPairs
public import CFSG.LocalAnalysis.StandardType.UnitaryAlgClosure

public section

namespace CFSG.StandardType

namespace UnitaryMatrix

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits InnerDiagSU UFusion

variable {F : Type} [Field F] {n : ℕ}

theorem coe_pow_eq_smul_one {A : GL (Fin n) F} {k : ℕ} {c : Fˣ}
    (h : A ^ k = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ k =
      (c : F) • (1 : Matrix (Fin n) (Fin n) F) := by
  have h' := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal] using h'

theorem coe_ne_smul_one {A : GL (Fin n) F}
    (hA : ∀ c : Fˣ, A ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c) (e : F) :
    (A : Matrix (Fin n) (Fin n) F) ≠ e • (1 : Matrix (Fin n) (Fin n) F) := by
  intro h
  by_cases hn : n = 0
  · subst hn
    refine hA 1 (Units.ext (funext fun i => funext fun j => ?_))
    exact isEmptyElim i
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hdet : IsUnit (Matrix.det (A : Matrix (Fin n) (Fin n) F)) :=
      (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have he : e ≠ 0 := ne_zero_pow hn hdet.ne_zero
    refine hA (Units.mk0 e he) (Units.ext ?_)
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
    exact h.trans (Matrix.smul_one_eq_diagonal e)

theorem transpose_form_of_isJUnitary {σ : F ≃+* F} {A : GL (Fin n) F} (hA : IsJUnitary σ A) :
    (A : Matrix (Fin n) (Fin n) F)ᵀ * antidiag n * (A : Matrix (Fin n) (Fin n) F).map σ =
      antidiag n := by
  unfold IsJUnitary at hA
  exact UnitaryAlg.transpose_form_of_conjTr σ hA

theorem transpose_form_of_mem_SU {σ : F ≃+* F} {A : GL (Fin n) F} (hA : A ∈ SU σ n) :
    (A : Matrix (Fin n) (Fin n) F)ᵀ * antidiag n * (A : Matrix (Fin n) (Fin n) F).map σ =
      antidiag n := by
  exact UnitaryAlg.transpose_form_of_conjTr σ (mem_SU.mp hA).2

@[expose] noncomputable def repHom (σ : F ≃+* F) (n : ℕ) (Γ : Subgroup (SU σ n)) :
    ↥Γ →* Matrix (Fin n) (Fin n) F :=
  (Units.coeHom (Matrix (Fin n) (Fin n) F)).comp ((SU σ n).subtype.comp Γ.subtype)

theorem repHom_apply (σ : F ≃+* F) (Γ : Subgroup (SU σ n)) (γ : ↥Γ) :
    repHom σ n Γ γ = (((γ : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem repHom_form (σ : F ≃+* F) (Γ : Subgroup (SU σ n)) (γ : ↥Γ) :
    (repHom σ n Γ γ)ᵀ * antidiag n * (repHom σ n Γ γ).map σ = antidiag n := by
  rw [repHom_apply]
  exact transpose_form_of_mem_SU (σ := σ) (A := ((γ : SU σ n) : GL (Fin n) F)) (γ : SU σ n).2

theorem eq_one_of_repHom_eq_one (σ : F ≃+* F) (Γ : Subgroup (SU σ n)) {γ : ↥Γ}
    (h : repHom σ n Γ γ = 1) : γ = 1 := by
  have h1 : ((γ : SU σ n) : GL (Fin n) F) = 1 := by
    apply Units.ext
    exact h
  apply Subtype.ext
  apply Subtype.ext
  simpa using h1

section Centralizer

variable {G : Type*} [Group G]

theorem three_dvd_card_centralizer_of_mem [Finite G] {H : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.centralizer (H : Set G)) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) := by
  have h := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (H : Set G)) hb
  rwa [orderOf_eq_prime hb3 hb1] at h

variable [Finite F] [CharP F 2] {f : ℕ}

theorem not_scalar_of_mem_suInducedPairs [Finite G] {ψ : SU (unitaryInvolution F 2 f) n →* G}
    {y : G} {A : GL (Fin n) F} (h : (y, A) ∈ suInducedPairs ψ) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hcen : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (ψ.range : Set G))) :
    ∀ c : Fˣ, A ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  intro c hc
  rw [hc] at h
  exact hcen (three_dvd_card_centralizer_of_mem
    (UnitaryPairs.mem_centralizer_of_mem_suInducedPairs_scalar h) hy3 hy1)

end Centralizer

end UnitaryMatrix

end CFSG.StandardType
