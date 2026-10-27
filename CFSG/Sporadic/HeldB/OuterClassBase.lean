
module

public import CFSG.Sporadic.HeldB.OuterClassCheckBase
public import CFSG.Sporadic.HeldB.BaseTests
public import CFSG.Sporadic.HeldB.OuterArith
public import CFSG.Sporadic.HeldB.FixCount
public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

@[expose] public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native

theorem heAutU_inv : heAutU⁻¹ = heAutU := by
  rw [inv_eq_iff_mul_eq_one, ← sq, heAutU_sq]

theorem heAutU_mul_heAutU_mul
    (x : Equiv.Perm (Fin 8330)) : heAutU * (heAutU * x) = x := by
  rw [← mul_assoc, ← sq, heAutU_sq, one_mul]

theorem heAutU_conj_mem
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP) :
    heAutU * g * heAutU ∈ heP := by
  have := (Subgroup.mem_normalizer_iff.1 heAutU_mem_normalizer g).1 hg
  rwa [heAutU_inv] at this

theorem heAutU_comm_mem
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP) :
    (g * heAutU)⁻¹ * (heAutU * g) ∈ heP := by
  rw [mul_inv_rev, heAutU_inv,
    show heAutU * g⁻¹ * (heAutU * g) = heAutU * g⁻¹ * heAutU * g by group]
  exact heP.mul_mem (heAutU_conj_mem (heP.inv_mem hg)) hg

theorem heAutU_twist_sq_mem
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP) :
    (heAutU * g) ^ 2 ∈ heP := by
  rw [sq, show heAutU * g * (heAutU * g) = heAutU * g * heAutU * g by group]
  exact heP.mul_mem (heAutU_conj_mem hg) hg

theorem heAutU_mul_not_mem
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ heP) : heAutU * g ∉ heP :=
  fun h => heAutU_not_mem (by simpa using heP.mul_mem h (heP.inv_mem hg))

theorem heAutU_mul_mem_of_outer
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hxP : x ∉ heP) : heAutU * x ∈ heP := by
  rcases mem_heAutGroup_cases hx with h | h
  · exact absurd h hxP
  · have := heAutU_conj_mem h
    rwa [show heAutU * (x * heAutU) * heAutU = heAutU * x * (heAutU * heAutU) by group,
      ← sq, heAutU_sq, mul_one] at this

theorem sign_of_fixCard {x : Equiv.Perm (Fin 8330)} (h2 : x ^ 2 = 1) {f : ℕ}
    (hf : fixCard x = f) : Equiv.Perm.sign x = (-1) ^ ((8330 - f) / 2) := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2, card_fixedPoints_eq, hf, Fintype.card_fin]

@[expose] def heOuterInvs : Set (Equiv.Perm (Fin 8330)) :=
  {x | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2}

theorem mem_heOuterInvs {x : Equiv.Perm (Fin 8330)} :
    x ∈ heOuterInvs ↔ x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2 := Iff.rfl

theorem heOuterInvs_conj {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heOuterInvs)
    {h : Equiv.Perm (Fin 8330)} (hh : h ∈ heP) : h * x * h⁻¹ ∈ heOuterInvs := by
  obtain ⟨hR, hP, h2⟩ := hx
  refine ⟨heAutGroup.mul_mem (heAutGroup.mul_mem (heP_le_heAutGroup hh) hR)
    (heAutGroup.inv_mem (heP_le_heAutGroup hh)), fun hm => hP ?_, ?_⟩
  · have := heP.mul_mem (heP.mul_mem (heP.inv_mem hh) hm) hh
    rwa [show h⁻¹ * (h * x * h⁻¹) * h = x by group] at this
  · rw [orderOf_conj_eq, h2]

end CFSG.Sporadic.HeldB
