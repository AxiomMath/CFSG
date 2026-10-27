module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphDefs

public section

namespace CFSG.StandardType

open Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

private lemma psuBridge_fixed_scalar {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (B : primeFormUnitary h (psuJ n K)) (x : AutPSU.XJ h n)
    (hfix : primeFormConjHom h (psuJ n K) B (QuotientGroup.mk x : AutPSU.PJ h n) =
      (QuotientGroup.mk x : AutPSU.PJ h n)) :
    ∃ c : Kˣ, (B : GL (Fin n) K) * ((x : GL (Fin n) K))⁻¹ * (B : GL (Fin n) K)⁻¹ *
        (x : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  have hmk := primeFormConjHom_mk h (psuJ n K) B x
  have hq : QuotientGroup.mk (⟨B * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (psuJ n K) B.2 x.2⟩ : AutPSU.XJ h n) =
      (QuotientGroup.mk x : AutPSU.PJ h n) := by
    rw [← hmk]
    exact hfix
  have hmem : (⟨B * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (psuJ n K) B.2 x.2⟩ : AutPSU.XJ h n)⁻¹ * x ∈
      normOneScalars h (AutPSU.XJ h n) n :=
    QuotientGroup.eq.mp hq
  obtain ⟨c, -, -, hc⟩ := (mem_normOneScalars).mp hmem
  refine ⟨c, ?_⟩
  rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv]
  group

private lemma psuBridge_chat_of_scalar {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (B : GL (Fin n) K) (x : AutPSU.XJ h n) (c : Kˣ)
    (hc : B * ((x : GL (Fin n) K))⁻¹ * B⁻¹ * (x : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c) :
    x ∈ psuChat h B := by
  refine ⟨c, ?_⟩
  have h3 : (x : GL (Fin n) K) * B =
      GeneralLinearGroup.scalar (Fin n) c * (B * (x : GL (Fin n) K)) := by
    have h := congrArg (fun t => (x : GL (Fin n) K) * B⁻¹ * t * B) hc
    have hL : (x : GL (Fin n) K) * B⁻¹ * (B * ((x : GL (Fin n) K))⁻¹ * B⁻¹ *
        (x : GL (Fin n) K)) * B = B⁻¹ * (x : GL (Fin n) K) * B := by
      group
    have hR : (x : GL (Fin n) K) * B⁻¹ * GeneralLinearGroup.scalar (Fin n) c * B =
        GeneralLinearGroup.scalar (Fin n) c * (x : GL (Fin n) K) := by
      rw [(commute_scalar c ((x : GL (Fin n) K) * B⁻¹)).eq]
      group
    rw [hL, hR] at h
    calc (x : GL (Fin n) K) * B = B * (B⁻¹ * (x : GL (Fin n) K) * B) := by
          group
      _ = B * (GeneralLinearGroup.scalar (Fin n) c * (x : GL (Fin n) K)) := by
          rw [h]
      _ = GeneralLinearGroup.scalar (Fin n) c * (B * (x : GL (Fin n) K)) := by
          rw [← mul_assoc, (commute_scalar c B).eq, mul_assoc]
  have hS : (GeneralLinearGroup.scalar (Fin n) c : Matrix (Fin n) (Fin n) K) =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hval := congrArg (fun t : GL (Fin n) K => (t : Matrix (Fin n) (Fin n) K)) h3
  simp only [Units.val_mul] at hval
  rw [hS] at hval
  simpa [Matrix.smul_mul] using hval

theorem psuGraph_mem_chat_of_fixed {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (B : primeFormUnitary h (psuJ n K)) (x : AutPSU.XJ h n)
    (hfix : primeFormConjHom h (psuJ n K) B (QuotientGroup.mk x : AutPSU.PJ h n) =
      (QuotientGroup.mk x : AutPSU.PJ h n)) :
    x ∈ psuChat h (B : GL (Fin n) K) := by
  obtain ⟨c, hc⟩ := psuBridge_fixed_scalar h B x hfix
  exact psuBridge_chat_of_scalar h (B : GL (Fin n) K) x c hc

end CFSG.StandardType
