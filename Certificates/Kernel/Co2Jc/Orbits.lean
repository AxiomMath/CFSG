module

public import CFSG.Sporadic.Co2Jc.Native.Orbits
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCo2Jc

theorem orbits_check : CFSG.Sporadic.Co2Jc.Native.orbitsOK = true := by
  have pk : ∀ (L : List Nat) (w m : Nat), L.all (· < 2 ^ w) = true →
      L.getD m 0 = L.foldr (fun x acc => x + acc * 2 ^ w) 0 / 2 ^ (w * m) % 2 ^ w := by
    intro L w
    induction L with
    | nil => intro m _; simp
    | cons x L ih =>
      intro m h
      rw [List.all_cons, Bool.and_eq_true, decide_eq_true_iff] at h
      rw [List.foldr_cons]
      cases m with
      | zero =>
        rw [List.getD_cons_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.1]
      | succ m =>
        rw [List.getD_cons_succ, ih m h.2, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * m)),
          ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
          Nat.div_eq_of_lt h.1, Nat.zero_add]
  have ar : ∀ (a : Array Nat) (m : Nat), a[m]! = a.toList.getD m 0 := by
    intro a m
    rw [getElem!_def, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    cases a[m]? <;> rfl
  open CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data in
  have hlab : labAt = fun m =>
      lab.toList.foldr (fun x acc => x + acc * 2 ^ 2) 0 / 2 ^ (2 * m) % 2 ^ 2 := by
    funext m
    rw [labAt, ar, pk _ 2 m (by decide +kernel)]
  open CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data in
  have hpar : parAt = fun m =>
      par.toList.foldr (fun x acc => x + acc * 2 ^ 10) 0 / 2 ^ (10 * m) % 2 ^ 10 := by
    funext m
    rw [parAt, ar, pk _ 10 m (by decide +kernel)]
  open CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data in
  have hdep : depAt = fun m =>
      dep.toList.foldr (fun x acc => x + acc * 2 ^ 4) 0 / 2 ^ (4 * m) % 2 ^ 4 := by
    funext m
    rw [depAt, ar, pk _ 4 m (by decide +kernel)]
  open CFSG.Sporadic.Co2Jc.Native in
  simp only [orbitsOK, orbitsChecks, repChk, labZeroChk, labValChk, labOmChk, labStepChk,
    classSizeChk, classCount, classCoords, treeChk, fChk, fCount, fCoords, hlab, hpar, hdep]
  decide +kernel

end CertificateChecks.KernelCo2Jc
