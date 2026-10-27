module

public import CFSG.Monster.B.TwoA.Fischer.CertSeed
public import CFSG.Monster.B.TwoA.Fischer.CertRemText
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import Std.Data.HashSet
public meta import CFSG.Monster.B.TwoA.Fischer.CertSeed
public meta import CFSG.Monster.B.TwoA.Fischer.CertRemText
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import CFSG.Monster.B.TwoA.Fischer.CertRemOrbitInputs
public import Certificates.Certificate3069
public import CFSG.Certificates.Kernel.MonsterB.Rem3069Sound
import CFSG.Certificates.Kernel.MonsterB.FischerKSound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Binary.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.KC.Rem3069 CFSG.KC.FischerK
open scoped Matrix

inductive Reach4 (u : Fin 78 → ZMod 2) : (Fin 78 → ZMod 2) → Prop
  | refl : Reach4 u u
  | step {v : Fin 78 → ZMod 2} (k : ℕ) (hk : k < 4) : Reach4 u v → Reach4 u (fourMat k *ᵥ v)

theorem fourColArr_toList {g : ℕ} (hg : g < 4) : (fourColArr[g]!).toList = fourColL g := by
  interval_cases g <;> decide +kernel

theorem fourColArr_size {g : ℕ} (hg : g < 4) : (fourColArr[g]!).size = 78 := by
  rw [← Array.length_toList, fourColArr_toList hg]
  interval_cases g <;> decide +kernel

theorem reach4_of_reachL {x : ℕ} (h : ReachL x) :
    Reach4 (toVecD 78 16058837527637121392057) (toVecD 78 x) := by
  induction h with
  | seed => exact Reach4.refl
  | step g hg _ ih =>
    have := Reach4.step g hg ih
    rwa [fourMat_mulVec, vecMulN_eq (fourColArr_size hg), fourColArr_toList hg] at this

theorem fischer_rem_orbit_certificate :
    ∃ S : Set (Fin 78 → ZMod 2), S.ncard = 694980 ∧
      ∀ v ∈ S, Reach4 (toVecD 78 16058837527637121392057) v := by
  obtain ⟨R, hR⟩ := Certificates.certificate3069
  obtain ⟨hlt, hmono, hreach⟩ := rem_sound hR
  have hinj : Set.InjOn (fun i => toVecD 78 (vecOf (recAt R i))) (Set.Iio remN) := by
    intro i hi j hj e
    have e' := toVecD_injective (hlt i hi) (hlt j hj) e
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e' (hmono i j h hj).ne
    · exact h
    · exact absurd e' (hmono j i h hi).ne'
  refine ⟨(fun i => toVecD 78 (vecOf (recAt R i))) '' Set.Iio remN, ?_, ?_⟩
  · rw [hinj.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
    rfl
  · rintro _ ⟨i, hi, rfl⟩
    exact reach4_of_reachL (hreach i hi)

end CFSG.Monster.B.TwoA.Fischer.Cert
