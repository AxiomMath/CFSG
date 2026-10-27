module

public import Certificates.Certificate17007
public import Certificates.Certificate7950
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase


public section

namespace CFSG.Quasithin.S143

namespace A6Model

set_option maxRecDepth 100000 in
theorem rawD_unit_eq_zero_iff : ∀ (p : Fin 6) (σ : Equiv.Perm (Fin 6)), σ.sign = 1 →
    (rawD (unitVec p) σ = 0 ↔ σ p = p) :=
  Certificates.certificate17007.1

set_option maxRecDepth 100000 in
theorem exists_alt_perm_map : ∀ p q : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = q :=
  Certificates.certificate17007.2.1

set_option maxRecDepth 100000 in
theorem oddCases_one : OddCases Vl1 (Equiv.swap 3 4) :=
  Certificates.certificate17007.2.2.1

set_option maxRecDepth 100000 in
theorem oddCases_two : OddCases Vl2 (Equiv.swap 0 4) :=
  Certificates.certificate17007.2.2.2.1


set_option maxRecDepth 100000 in
theorem swap_comm_cases : ∀ (p q : Fin 6) (σ₀ : Equiv.Perm (Fin 6)) (b : N6),
    (p ≠ q ∧ σ₀.sign = 1 ∧ σ₀ p = q) →
      (n6Act (Equiv.swap p q) b * b⁻¹ = 1 ∨ n6Act (Equiv.swap p q) b * b⁻¹ = dW (unitVec p) σ₀) :=
  Certificates.certificate17007.2.2.2.2.1

set_option maxRecDepth 100000 in
theorem exists_five_fixing : ∀ p : Fin 6, ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ σ p = p ∧
    σ ^ 5 = 1 ∧ σ ≠ 1 :=
  Certificates.certificate17007.2.2.2.2.2.1


structure Conf6Plus (c : Mat4) (Vl Vr : List (Equiv.Perm (Fin 6))) (s : Equiv.Perm (Fin 6)) : Prop where
  conf : Conf6 c Vl s
  odd : OddCases Vl s
  swap : ∀ p : Fin 6, s p ≠ p → s = Equiv.swap p (s p)
  rEven : ∀ w : Fin 6 → ZMod 2, VanL Vr w → wEven w
  vr_sign : ∀ σ ∈ Vr, σ.sign = 1
  rMoves : ∀ p : Fin 6, s p ≠ p → ∃ σ ∈ Vr, σ p ≠ p

set_option maxRecDepth 100000 in
theorem conf6plus_one :
    Conf6Plus c1 Vl1 Vr1 (Equiv.swap 3 4) :=
  ⟨conf6_one, oddCases_one, Certificates.certificate7950.1,
    Certificates.certificate7950.2.1,
    Certificates.certificate7950.2.2.1,
    Certificates.certificate7950.2.2.2.1⟩

set_option maxRecDepth 100000 in
theorem conf6plus_two :
    Conf6Plus c2 Vl2 Vr2 (Equiv.swap 0 4) :=
  ⟨conf6_two, oddCases_two, Certificates.certificate7950.2.2.2.2.1,
    Certificates.certificate7950.2.2.2.2.2.1,
    Certificates.certificate7950.2.2.2.2.2.2.1,
    Certificates.certificate7950.2.2.2.2.2.2.2⟩

theorem rCorr1 : ∀ σ ∈ Vr1, ∃ P ∈ Rstd4, mat4Eq (mm c1 (matOf6 σ)) (mm P c1) = true :=
  Certificates.certificate17007.2.2.2.2.2.2.1

theorem rCorr2 : ∀ σ ∈ Vr2, ∃ P ∈ Rstd4, mat4Eq (mm c2 (matOf6 σ)) (mm P c2) = true :=
  Certificates.certificate17007.2.2.2.2.2.2.2

end A6Model

end CFSG.Quasithin.S143
