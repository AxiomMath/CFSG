module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.GH74.KGroups.L28Inputs
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
public import CFSG.Sporadic.Schreier.J1CertData
import Certificates.Kernel.Ivk8Norm.Free
import Certificates.Kernel.Ivk8NormP.M23Final
import Certificates.Kernel.Ivk8NormP.J3Final
import Certificates.Kernel.Ivk8NormP.L28Final
import Certificates.Kernel.Ivk8NormP.L216Final
import Certificates.Kernel.Ivk8NormP.J1Final
import Certificates.Kernel.Ivk8NormP.J2Final
import Certificates.Kernel.Ivk8NormP.M11Final
public import CFSG.Sporadic.Schreier.PairJ2CertBase
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace Certificates

open CFSG.Blueprint CFSG.Sporadic.Schreier in
theorem certificate5253 :
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 12)),
      P ≤ NativeSporadic.M12 → W ≤ NativeSporadic.M12 → Nat.card P = 2 ^ 6 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 12))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 22)),
      P ≤ NativeSporadic.M22 → W ≤ NativeSporadic.M22 → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 22))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 42)),
      P ≤ CFSG.ComponentClassification.PSL3Four.S → W ≤ CFSG.ComponentClassification.PSL3Four.R →
      Nat.card P = 2 ^ 6 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 42))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 23)),
      P ≤ NativeSporadic.M23 → W ≤ NativeSporadic.M23 → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 23))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 6156)),
      P ≤ j3P → W ≤ j3P → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 6156))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 9)),
      P ≤ CFSG.GH74.KGroups.L28.QP.originalSubgroup →
      W ≤ CFSG.GH74.KGroups.L28.QA.originalSubgroup → Nat.card P = 2 ^ 3 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 9))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 17)),
      P ≤ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QP.originalSubgroup →
      W ≤ CFSG.GH74.Uniqueness.SU.K.R4.L216M.QA.originalSubgroup → Nat.card P = 2 ^ 4 →
      IsPGroup p W → P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 17))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 3080)),
      P ≤ j1P → W ≤ j1P → Nat.card P = 2 ^ 3 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 3080))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup (Equiv.Perm (Fin 315)),
      P ≤ j2P → W ≤ j2P → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 315))) → W = ⊥) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ P W : Subgroup (Equiv.Perm (Fin 11)),
      P ≤ NativeSporadic.M11 → W ≤ NativeSporadic.M11 → Nat.card P = 2 ^ 4 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 11))) → W = ⊥) ∧
    (∀ x ∈ NativeSporadic.M11, orderOf x = 3 → ∃ u ∈ NativeSporadic.M11,
      ∃ v ∈ NativeSporadic.M11, u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧ x * u * x⁻¹ = v ∧
        x * v * x⁻¹ = u * v ∧ v ≠ u) :=
  ⟨fun _ hp hp2 => CFSG.KS.Ivk8Norm.Final.m12_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8Norm.Final.m22_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8Norm.Final.l34_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.M23.m23_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.J3.j3_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.L28.l28_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.L216.l216_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.J1.j1_noP hp hp2,
    fun _ hp hp2 => CFSG.KS.Ivk8NormP.J2.j2_noP hp hp2,
    fun _ hp hp2 hp3 => CFSG.KS.Ivk8NormP.M11.m11_noP hp hp2 hp3,
    CFSG.KS.Ivk8NormP.M11.m11_hh⟩

end Certificates
