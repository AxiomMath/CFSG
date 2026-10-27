module

public import CFSG.Quasithin.Background.B4Models
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public import CFSG.Quasithin.Background.HA7DataInputs
public import Certificates.Certificate7022

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open Equiv
open scoped Matrix

theorem exists_conj_inv7 :
    ∀ σ : alternatingGroup (Fin 7), σ * σ = 1 → σ ≠ 1 →
    ∃ g : alternatingGroup (Fin 7), g * σ * g⁻¹ = inv7 :=
  Certificates.certificate7022.1

theorem card_centralizer_inv8 :
    (Finset.univ.filter fun π : alternatingGroup (Fin 8) => π * inv8 = inv8 * π).card = 96 :=
  Certificates.certificate7022.2.1

theorem card_transvections :
    (Finset.univ.filter fun M : Matrix (Fin 4) (Fin 4) (ZMod 2) => M * M = 1 ∧
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 8).card = 105 :=
  Certificates.certificate7022.2.2.1

theorem fix_eq_zero_of_pow_five :
    ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M ^ 5 = 1 → M ≠ 1 →
    ∀ v : Fin 4 → ZMod 2, M *ᵥ v = v → v = 0 :=
  Certificates.certificate7022.2.2.2

theorem coe_altLift7 (σ : alternatingGroup (Fin 7)) :
    ((altLift7 σ : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      Equiv.Perm.viaEmbedding (σ : Perm (Fin 7)) Fin.castSuccEmb := by
  simp only [altLift7, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    Equiv.Perm.viaEmbeddingHom_apply]

theorem altLift7_inv7 : altLift7 inv7 = inv8 := by
  apply Subtype.ext
  rw [coe_altLift7]
  ext j : 1
  show Equiv.Perm.viaEmbedding (swap (0 : Fin 7) 1 * swap 2 3) Fin.castSuccEmb j =
    (swap (0 : Fin 8) 1 * swap 2 3 : Perm (Fin 8)) j
  induction j using Fin.lastCases with
  | last =>
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · decide
    · rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
  | cast i =>
    have h := Equiv.Perm.viaEmbedding_apply (swap (0 : Fin 7) 1 * swap 2 3) Fin.castSuccEmb i
    rw [show Fin.castSucc i = Fin.castSuccEmb i from rfl, h]
    fin_cases i <;> decide

end A7

end H

end CFSG.Quasithin
