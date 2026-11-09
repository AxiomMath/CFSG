module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6Inputs
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.A6
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound
public import Certificates.Kernel.Census.CatFacts.C2006K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6
  CFSG.Certificates.Kernel.PkEnum

local notation "V10" => VP 10

theorem rep2006_succ (a : V10) (k : Nat) : rep2006 a (k + 1) = a :: rep2006 a k := rfl

theorem pkpW_rep2006 (a : V10) (k : Nat) : pkpW (rep2006 a k) = pkp a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep2006_succ, pkpW_cons, ih, pow_succ']

theorem comm2006_eq (a b : V10) : comm2006 a b = decide (pkp a * pkp b = pkp b * pkp a) := by
  simp only [comm2006, eqW_eq, pkpW_cons, pkpW_nil, mul_one]

theorem sq2006_eq (a : V10) : sq2006 a = decide (pkp a * pkp a = 1) := by
  rw [sq2006, isOneW_eq, pkpW_cons, pkpW_single]

theorem one2006_eq (a : V10) : isOneW [a] = decide (pkp a = 1) := by
  rw [isOneW_eq, pkpW_single]

theorem pow15K2006_eq (a : V10) : pow15K2006 a = decide (pkp a ^ 15 = 1) := by
  rw [pow15K2006, forceV_eq, isOneW_eq, pkpW_rep2006, pkp_mulV, pkp_mulV, ← pow_three, ← pow_mul]

theorem pow120K2006_eq (a : V10) : pow120K2006 a = decide (pkp a ^ 120 = 1) := by
  rw [pow120K2006, forceV_eq, forceV_eq, forceV_eq, pow15K2006_eq, pkp_mulV, pkp_mulV, pkp_mulV, ← sq,
    ← sq, ← sq, ← pow_mul, ← pow_mul, ← pow_mul]

theorem pow32K2006_eq (a : V10) : pow32K2006 a = decide (pkp a ^ 32 = 1) := by
  rw [pow32K2006, forceV_eq, forceV_eq, forceV_eq, forceV_eq, sq2006_eq, pkp_mulV, pkp_mulV, pkp_mulV,
    pkp_mulV, ← sq, ← sq, ← sq, ← sq, ← sq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]

theorem pow8K2006_eq (a : V10) : pow8K2006 a = decide (pkp a ^ 8 = 1) := by
  rw [pow8K2006, forceV_eq, forceV_eq, sq2006_eq, pkp_mulV, pkp_mulV, ← sq, ← sq, ← sq, ← pow_mul,
    ← pow_mul]

theorem pow32_iff2006 {G : Type*} [Monoid G] {g : G} (h : g ^ 120 = 1) : g ^ 32 = 1 ↔ g ^ 8 = 1 := by
  constructor
  · intro h32
    calc g ^ 8 = g ^ 120 * g ^ 8 := by rw [h, one_mul]
      _ = (g ^ 32) ^ 4 := by rw [← pow_add, ← pow_mul]
      _ = 1 := by rw [h32, one_pow]
  · intro h8
    calc g ^ 32 = (g ^ 8) ^ 4 := by rw [← pow_mul]
      _ = 1 := by rw [h8, one_pow]

theorem innerE2006_eq (A : List V10) (h : expK2006 A = true) : innerE2006 A = innerN2006 A := by
  refine List.filter_congr fun a ha => ?_
  have h120 := List.all_eq_true.1 h a ha
  rw [pow120K2006_eq, decide_eq_true_eq] at h120
  rw [pow8K2006_eq, pow32K2006_eq, decide_eq_decide.mpr (pow32_iff2006 h120)]

theorem cmt2006_eq(o n : V10) :
    pkp (cmt2006 o n) = pkp o * pkp n * (pkp o)⁻¹ * (pkp n)⁻¹ := by
  rw [cmt2006, pkp_mulV, pkp_mulV, pkp_mulV, pkp_invV, pkp_invV]

theorem fix2006_eq (P : List V10) (s : V10) : fixCount (P.map pkp) (pkp s) = fix2006 P s := by
  simp only [fixCount, fix2006, List.filter_map, List.length_map, Function.comp_def, comm2006_eq]

theorem cent2006_eq (L C : List V10) : centCountC (L.map pkp) (C.map pkp) = cent2006 L C := by
  simp only [centCountC, cent2006, List.filter_map, List.length_map, Function.comp_def,
    List.all_map, comm2006_eq]

theorem mem2006_eq (P : List V10) (s : V10) :
    P.any (fun g => eqW [g] [s]) = (P.map pkp).contains (pkp s) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true, List.mem_map]
  simp only [eqW_eq, pkpW_single, decide_eq_true_eq]

theorem expK2006_eq (A : List V10) : expK2006 A = expCheck (A.map pkp) := by
  simp only [expK2006, expCheck, List.all_map, Function.comp_def]
  exact congrArg A.all (funext pow120K2006_eq)

theorem or3_2006 (a b c : Bool) : (!a || (b || c)) = (!a || b || c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem or4_2006 (a b c d : Bool) : (!(!a && b) || !c || d) = (!c || a || !b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem diagK2006_eq (A P : List V10) : diagK2006 A P = diagCheck (A.map pkp) (P.map pkp) := by
  simp only [diagK2006, forceL_eq, List.all_filter, List.any_filter, diagCheck, List.all_map,
    List.any_map, Function.comp_def, fix2006_eq, fix2006, sq2006_eq, comm2006_eq, one2006_eq,
    pow15K2006_eq, forceV_eq, cmt2006_eq, or4_2006, or3_2006]

theorem commsym2006 (a b : V10) : comm2006 a b = comm2006 b a := by
  rw [comm2006_eq, comm2006_eq]
  exact decide_eq_decide.mpr eq_comm

theorem fixsym2006 (P : List V10) (x : V10) :
    fix2006 P x = (P.filter fun y => comm2006 x y).length :=
  congrArg List.length (List.filter_congr fun y _ => commsym2006 y x)

theorem and3_2006 (a b c d : Bool) : (!(a && !b) || (c && d)) = (!a || b || c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem notnot2006 (a b : Bool) : (!!a || !b) = (!b || a) := by
  cases a <;> cases b <;> rfl

theorem innerK2006_eq (A P : List V10) :
    innerK2006 A P = innerCheck (A.map pkp) (P.map pkp) := by
  simp only [innerCheck, centCount, List.all_map, Function.comp_def, fix2006_eq, fixsym2006]
  simp only [innerK2006, forceL_eq, List.all_filter, List.filter_map, Function.comp_def,
    ← cent2006_eq,
    sq2006_eq, comm2006_eq, one2006_eq, pow32K2006_eq, notnot2006, Bool.and_assoc, and3_2006]

theorem or5_2006 (a b c d : Bool) : (!a || !b || c || d) = (!a || c || d || !b) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem noCommK2006_eq (A P : List V10) :
    noCommK2006 A P = noCommCheck (A.map pkp) (P.map pkp) := by
  simp only [noCommK2006, forceL_eq, List.all_filter, noCommCheck, List.all_map,
    Function.comp_def, sq2006_eq, fix2006_eq, comm2006_eq, mem2006_eq, or5_2006, or3_2006]

theorem nc2006_or (a b c : Bool) : (!!(b || c) || !a) = (!a || b || c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem noComm2006_of (A P I F B : List V10) (hI : diagI2006 A = I)
    (hFB : forceL P (fun P => forceL I fun I => (ncF2006 P I, ncB2006 P I)) = (F, B))
    (h : forceL F (fun F => forceL B (ncC2006 F)) = true) :
    forceL A (fun A => forceL P (noCommK2006 A)) = true := by
  simp only [forceL_eq, Prod.mk.injEq] at hFB h ⊢
  obtain ⟨hF, hB⟩ := hFB
  subst hI hF hB
  simp only [noCommK2006, forceL_eq, ncC2006, ncF2006, ncB2006, diagI2006, List.all_filter,
    nc2006_or] at h ⊢
  exact h

theorem noComm2006K : forceL A2006 (fun A => forceL P2006 (noCommK2006 A)) = true :=
  noComm2006_of A2006 P2006 I2006 F2006 B2006 subI2006 subFB2006 noComm2006C

theorem centrev2006 (L C : List V10) : cent2006 L C.reverse = cent2006 L C := by
  simp only [cent2006, List.all_reverse]

theorem diag2006_of(A P I O : List V10) (hI : diagI2006 A = I) (hO : diagO2006 A = O)
    (hlen : I.length ≤ 4 * 28)
    (h : ∀ j < 4, forceL P (fun P => forceL O (fun O => forceL I (diagC2006 j P O))) = true) :
    forceL A (fun A => forceL P (diagK2006 A)) = true := by
  have e : diagK2006 A P = forceL (diagI2006 A) fun I => forceL (diagO2006 A) fun O =>
      I.all (diagX2006 P O) := rfl
  rw [forceL_eq, forceL_eq, e, forceL_eq, forceL_eq, hI, hO]
  refine all_of_chunks _ _ 28 4 hlen fun j hj => ?_
  have hj' := h j hj
  rwa [forceL_eq, forceL_eq, forceL_eq, diagC2006] at hj'

theorem diag2006K : forceL A2006 (fun A => forceL P2006 (diagK2006 A)) = true :=
  diag2006_of A2006 P2006 I2006 O2006 subI2006 subO2006 diagLen2006 fun j hj => match j, hj with
    | 0, _ => diag2006K0
    | 1, _ => diag2006K1
    | 2, _ => diag2006K2
    | 3, _ => diag2006K3
    | _ + 4, h => absurd h (by omega)

theorem inner2006_of (A P N X : List V10) (hN : innerN2006 A = N) (hX : innerI2006 P = X)
    (hlen : X.length ≤ 2 * 24)
    (h : ∀ j < 2, forceL A (fun A => forceL P (fun P => forceL N (fun N =>
      forceL X (innerC2006 j A P N)))) = true) :
    forceL A (fun A => forceL P (innerK2006 A)) = true := by
  have e : innerK2006 A P = forceL (innerN2006 A) fun N => (innerI2006 P).all (innerX2006 A P N) := by
    simp only [innerK2006, innerN2006, innerI2006]
    congr 1
    funext N
    congr 1
    funext x
    simp only [innerX2006, centrev2006]
  rw [forceL_eq, forceL_eq, e, forceL_eq, hN, hX]
  refine all_of_chunks _ _ 24 2 hlen fun j hj => ?_
  have hj' := h j hj
  rwa [forceL_eq, forceL_eq, forceL_eq, forceL_eq, innerC2006] at hj'

theorem inner2006K : forceL A2006 (fun A => forceL P2006 (innerK2006 A)) = true :=
  inner2006_of A2006 P2006 N2006 X2006
    ((innerE2006_eq A2006 (by simpa only [forceL_eq] using exp2006K)).symm.trans subN2006) subX2006
    innerLen2006 fun j hj => match j, hj with
    | 0, _ => inner2006K0
    | 1, _ => inner2006K1
    | _ + 2, h => absurd h (by omega)

theorem elemsV_eq_map2006 {n : Nat} (Q : CFSG.Certificates.RawSchreierDatum n) :
    elemsV Q = (enumV (strongV Q) Q.base).map pkp := rfl

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 in
open CFSG.Certificates CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
theorem facts2006 : (expCheck (elemsT QA) = true)
    ∧ (diagCheck (elemsT QA) (elemsT QP) = true)
    ∧ (innerCheck (elemsT QA) (elemsT QP) = true)
    ∧ (noCommCheck (elemsT QA) (elemsT QP) = true) := by
  have h1 := exp2006K
  have h2 := diag2006K
  have h3 := inner2006K
  have h4 := noComm2006K
  simp only [forceL_eq, ← enumA2006, ← enumP2006] at h1 h2 h3 h4
  rw [elemsT_eq_elemsV, elemsT_eq_elemsV, elemsV_eq_map2006, elemsV_eq_map2006, ← expK2006_eq,
    ← diagK2006_eq, ← innerK2006_eq, ← noCommK2006_eq]
  exact ⟨h1, h2, h3, h4⟩

end CertificateChecks.KernelCatFacts
