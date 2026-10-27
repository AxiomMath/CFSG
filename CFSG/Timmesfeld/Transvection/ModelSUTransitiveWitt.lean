module

public import CFSG.Timmesfeld.Transvection.ModelSUGen
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_suMat_mulVec_eq_of_witt {n : ℕ} {σ : F ≃+* F} {P : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    {x y : Fin n → F} {t : SUid σ n}
    (ht : t • ((P : Matrix (Fin n) (Fin n) F) *ᵥ x) = (P : Matrix (Fin n) (Fin n) F) *ᵥ y) :
    ∃ g : SU σ n, suMat σ n g *ᵥ x = y := by
  set Pm := (P : Matrix (Fin n) (Fin n) F) with hPm
  set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hPi
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨(conjEquiv P hP).symm t, ?_⟩
  have hmat : suMat σ n ((conjEquiv P hP).symm t) =
      Pi * ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Pm := rfl
  rw [hmat, ← mulVec_mulVec, ← mulVec_mulVec, ← CFSG.ClassicalGroups.Unitary.smul_def, ht,
    mulVec_mulVec, hPiP, one_mulVec]

theorem exists_suMat_mulVec_eq_of_iso (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    {x y : Fin n → F} (hx0 : x ≠ 0) (hxx : uForm (unitaryInvolution F p f) x x = 0)
    (hy0 : y ≠ 0) (hyy : uForm (unitaryInvolution F p f) y y = 0) :
    ∃ g : SU (unitaryInvolution F p f) n, suMat (unitaryInvolution F p f) n g *ᵥ x = y := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have hinj : ∀ {v : Fin n → F}, v ≠ 0 → (P : Matrix (Fin n) (Fin n) F) *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have := congrArg (fun w => ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w) h0
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  obtain ⟨t, -, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_iso hσ hn (hinj hx0)
    (by rw [herm_mulVec_mulVec_of_conjTr_mul hP, hxx]) (hinj hy0)
    (by rw [herm_mulVec_mulVec_of_conjTr_mul hP, hyy])
  exact exists_suMat_mulVec_eq_of_witt hP ht

theorem exists_suMat_mulVec_eq_of_norm_one (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}
    (hn : 4 ≤ n) {x y : Fin n → F} (hxx : uForm (unitaryInvolution F p f) x x = 1)
    (hyy : uForm (unitaryInvolution F p f) y y = 1) :
    ∃ g : SU (unitaryInvolution F p f) n, suMat (unitaryInvolution F p f) n g *ᵥ x = y := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨t, -, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_norm_one hσ
    (Or.inl hn) (by rw [herm_mulVec_mulVec_of_conjTr_mul hP, hxx])
    (by rw [herm_mulVec_mulVec_of_conjTr_mul hP, hyy])
  exact exists_suMat_mulVec_eq_of_witt hP ht

end CFSG.Timmesfeld.Transvection.ModelRank
