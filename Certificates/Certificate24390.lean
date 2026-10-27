module

public import CFSG.Sporadic.Recognition.ThMultiplierInputs
import Certificates.Kernel.Th.Fam.C24390
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CFSG.KC.Th.Expr CFSG.Sporadic.Recognition.ThMultiplier CertificateChecks.KernelTh.Fam

private theorem exists_bitsN (c : Fin 5 → ZMod 2) (hc : c ≠ 0) :
    ∃ m, m < 32 ∧ m ≠ 0 ∧ (fun j => (c j).val) = bitsN m := by
  have hb : ∀ j, (c j).val < 2 := fun j => ZMod.val_lt (c j)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  refine ⟨(c 0).val + 2 * (c 1).val + 4 * (c 2).val + 8 * (c 3).val + 16 * (c 4).val,
    by omega, fun hm => hc (funext fun j => ?_), funext fun j => ?_⟩
  · refine (ZMod.val_eq_zero _).1 ?_
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.zero_apply] <;> omega
  · fin_cases j <;> simp only [bitsN, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reducePow, pow_zero, Nat.div_one] <;> omega

open CFSG.Sporadic.Recognition.ThMultiplier in
theorem certificate24390 : thFacts := by
  refine ⟨fun j => ?_, fun i j => ?_, fun c hc => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have h := List.all_eq_true.1 ok24390a j (List.mem_finRange j)
    kernel_exact eqRows_true_of (e := .mul (vT j) (vT j)) (f := .one) thCtx h
  · have h := List.all_eq_true.1 (List.all_eq_true.1 ok24390b i (List.mem_finRange i)) j
      (List.mem_finRange j)
    kernel_exact eqRows_true_of (e := .mul (vT i) (vT j)) (f := .mul (vT j) (vT i)) thCtx h
  · obtain ⟨m, hm, hm0, hfun⟩ := exists_bitsN c hc
    have h := List.all_eq_true.1 ok24390c m (List.mem_range.2 hm)
    have hb : Nat.beq m 0 = false := by
      cases hq : Nat.beq m 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hq) hm0
    rw [hb, Bool.false_or] at h
    have hr : rowsIota (fun j => (c j).val) = rowsIota (bitsN m) := congrArg rowsIota hfun
    rw [hr]
    kernel_exact eqRows_false_of (e := iotaT (bitsN m)) (f := .one) thCtx h
  · have h := List.all_eq_true.1 ok24390d j (List.mem_finRange j)
    simp only [Bool.and_eq_true] at h
    kernel_exact eqRows_true_of (e := .mul mA1T (vT j)) (f := .mul (iotaT (colA1 j)) mA1T) thCtx
      h.1.1
  · have h := List.all_eq_true.1 ok24390d j (List.mem_finRange j)
    simp only [Bool.and_eq_true] at h
    kernel_exact eqRows_true_of (e := .mul mA2T (vT j)) (f := .mul (iotaT (colA2 j)) mA2T) thCtx
      h.1.2
  · have h := List.all_eq_true.1 ok24390d j (List.mem_finRange j)
    simp only [Bool.and_eq_true] at h
    kernel_exact eqRows_true_of (e := .mul mA3T (vT j)) (f := .mul (iotaT (colA3 j)) mA3T) thCtx
      h.2

end Certificates
