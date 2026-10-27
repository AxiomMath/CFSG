module

public import CFSG.Quasithin.H13.J4Quot
public import CFSG.Quasithin.H13.J4Chain12Spec
public meta import Certificates.Data.CFSGNative.H13.J4Chain12
public meta import Certificates.Data.CFSGNative.H13.J4Data
import Certificates.Data.CFSGNative.H13.J4Data
public import CFSG.Quasithin.H13.J4ImageInputs
public import Certificates.Certificate7013
public import Certificates.Certificate7015
public import Certificates.Certificate7018

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.SmallF2 (rowsMatrix) in
theorem image12_facts :
    rowsMatrix 12 uRows12 * rowsMatrix 12 uRows12 = 1 ∧
      rowsMatrix 12 vRows12 * (rowsMatrix 12 vRows12 * rowsMatrix 12 vRows12) = 1 ∧
      ∀ U V : GL (Fin 12) (ZMod 2),
        (U : Matrix (Fin 12) (Fin 12) (ZMod 2)) = rowsMatrix 12 uRows12 →
        (V : Matrix (Fin 12) (Fin 12) (ZMod 2)) = rowsMatrix 12 vRows12 →
        2661120 ≤ Nat.card (Subgroup.closure ({U, V} : Set (GL (Fin 12) (ZMod 2)))) :=
  Certificates.certificate7013

@[expose] def uvGen12 (i : ℕ) :
    GL (Fin 12) (ZMod 2) :=
  if i = 0 then U12 else if i = 1 then V12 else 1

theorem famRep12_uv :
    FamRep12 uvGen12 uvPairs12 := by
  obtain ⟨hU, hV, -⟩ := image12_facts
  have hU' : U12 * U12 = 1 := by
    apply Units.ext
    rw [Units.val_mul, imageChecks_spec.2.2.1, Units.val_one, hU]
  have hV' : V12 * (V12 * V12) = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, imageChecks_spec.2.2.2, Units.val_one, hV]
  intro i
  rcases i with _ | _ | i
  · refine ⟨imageChecks_spec.2.2.1.symm, ?_⟩
    show _ = ((U12⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
    rw [inv_eq_of_mul_eq_one_right hU']
    exact imageChecks_spec.2.2.1.symm
  · refine ⟨imageChecks_spec.2.2.2.symm, ?_⟩
    show CFSG.Sporadic.SmallF2.rowsMatrix 12
      (CFSG.Sporadic.SmallF2.Native.mulRows 12 vRows12 vRows12) =
      ((V12⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
    rw [inv_eq_of_mul_eq_one_right hV', Units.val_mul, CFSG.Sporadic.SmallF2.rowsMatrix_mulRows,
      imageChecks_spec.2.2.2]
  · have hb : uvGen12 (i + 2) = 1 := by unfold uvGen12; simp
    rw [hb]
    exact PrRep12.one

theorem le_card_range_rho :
    2661120 ≤ Nat.card rho.range := by
  have key := image12_facts.2.2 U12 V12 imageChecks_spec.2.2.1 imageChecks_spec.2.2.2
  rwa [← range_rho12, card_range_rho12] at key

end CFSG.Quasithin.H13.J4
