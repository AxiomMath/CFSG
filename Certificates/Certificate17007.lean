module

public import CFSG.Quasithin.EmptyFaithful.S143NAInputs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

namespace CertificateChecks.Batch17007

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

set_option maxRecDepth 100000 in
private theorem rawD_unit_eq_zero_iff_0 : ∀ (p : Fin 6) (σ : Equiv.Perm (Fin 6)), σ.sign = 1 →
    (rawD (unitVec p) σ = 0 ↔ σ p = p) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem exists_alt_perm_map_1 : ∀ p q : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = q := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem oddCases_one_2 : OddCases Vl1 (Equiv.swap 3 4) := by
  unfold OddCases
  decide +kernel

set_option maxRecDepth 100000 in
private theorem oddCases_two_3 : OddCases Vl2 (Equiv.swap 0 4) := by
  unfold OddCases
  decide +kernel

set_option maxRecDepth 100000 in
private theorem swap_comm_cases_4 : ∀ (p q : Fin 6) (σ₀ : Equiv.Perm (Fin 6)) (b : N6),
    (p ≠ q ∧ σ₀.sign = 1 ∧ σ₀ p = q) →
      (n6Act (Equiv.swap p q) b * b⁻¹ = 1 ∨ n6Act (Equiv.swap p q) b * b⁻¹ = dW (unitVec p) σ₀) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem exists_five_fixing_5 : ∀ p : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = p ∧
    σ ^ 5 = 1 ∧ σ ≠ 1 := by
  decide +kernel

private theorem rCorr1_6 : ∀ σ ∈ Vr1, ∃ P ∈ Rstd4, mat4Eq (mm c1 (matOf6 σ)) (mm P c1) = true := by
  decide +kernel

private theorem rCorr2_7 : ∀ σ ∈ Vr2, ∃ P ∈ Rstd4, mat4Eq (mm c2 (matOf6 σ)) (mm P c2) = true := by
  decide +kernel

end CertificateChecks.Batch17007

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model in
theorem certificate17007 : (
 ∀ (p : Fin 6) (σ : Equiv.Perm (Fin 6)), σ.sign = 1 →
    (rawD (CFSG.Quasithin.S143.A6Model.unitVec p) σ = 0 ↔ σ p = p) 
)
    ∧ (
 ∀ p q : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = q 
)
    ∧ (
 OddCases Vl1 (Equiv.swap 3 4) 
)
    ∧ (
 OddCases Vl2 (Equiv.swap 0 4) 
)
    ∧ (
 ∀ (p q : Fin 6) (σ₀ : Equiv.Perm (Fin 6)) (b : N6),
    (p ≠ q ∧ σ₀.sign = 1 ∧ σ₀ p = q) →
      (n6Act (Equiv.swap p q) b * b⁻¹ = 1 ∨ n6Act (Equiv.swap p q) b * b⁻¹ = CFSG.Quasithin.S143.A6Model.dW (CFSG.Quasithin.S143.A6Model.unitVec p) σ₀) 
)
    ∧ (
 ∀ p : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = p ∧
    σ ^ 5 = 1 ∧ σ ≠ 1 
)
    ∧ (
 ∀ σ ∈ Vr1, ∃ P ∈ Rstd4, mat4Eq (CFSG.Quasithin.S143.A6Model.mm CFSG.Quasithin.S143.A6Model.c1 (matOf6 σ)) (CFSG.Quasithin.S143.A6Model.mm P CFSG.Quasithin.S143.A6Model.c1) = true 
)
    ∧ (
 ∀ σ ∈ Vr2, ∃ P ∈ Rstd4, mat4Eq (CFSG.Quasithin.S143.A6Model.mm CFSG.Quasithin.S143.A6Model.c2 (matOf6 σ)) (CFSG.Quasithin.S143.A6Model.mm P CFSG.Quasithin.S143.A6Model.c2) = true 
) := by
  exact ⟨@CertificateChecks.Batch17007.rawD_unit_eq_zero_iff_0, @CertificateChecks.Batch17007.exists_alt_perm_map_1, @CertificateChecks.Batch17007.oddCases_one_2, @CertificateChecks.Batch17007.oddCases_two_3, @CertificateChecks.Batch17007.swap_comm_cases_4, @CertificateChecks.Batch17007.exists_five_fixing_5, @CertificateChecks.Batch17007.rCorr1_6, @CertificateChecks.Batch17007.rCorr2_7⟩

end Certificates
