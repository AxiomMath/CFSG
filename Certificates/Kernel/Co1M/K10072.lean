module

public import Certificates.Kernel.Co1M.Data10072
public import Certificates.Kernel.Co1M.Data10072Q
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.J4Q.VOrb
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.J4Q CFSG.KD.Co1M CFSG.KC.LQT.Syl CFSG.KC.Co1F2 CertificateChecks.KernelCo1Cover

@[expose] def cmCode4 : Nat := 10075731

@[expose] noncomputable def CH72 : List (List Nat) :=
  [FC0, FC1, FC2, FC3, FC4, FC5, FC6, FC7, FC8, FC9, FC10, FC11, FC12, FC13, FC14, FC15, FC16, FC17,
    FC18, FC19, FC20, FC21, FC22, FC23, FC24, FC25, FC26, FC27, FC28, FC29, FC30, FC31]

@[expose] noncomputable def SPC72 : List (List Nat) :=
  [FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FS12, FS13, FS14, FS15, FS16, FS17,
    FS18, FS19, FS20, FS21, FS22, FS23, FS24, FS25, FS26, FS27, FS28, FS29, FS30, FS31]

@[expose] noncomputable def cmPch : List (List Nat) :=
  List.cons (List.cons cmCode4 List.nil) (List.map (List.map fun e => Nat.land e RM112) CH72)

@[expose] noncomputable def FQL : List (List Nat) :=
  [FQ0, FQ1, FQ2, FQ3, FQ4, FQ5, FQ6, FQ7, FQ8, FQ9, FQ10, FQ11, FQ12, FQ13, FQ14, FQ15, FQ16, FQ17,
    FQ18, FQ19, FQ20, FQ21, FQ22, FQ23, FQ24, FQ25, FQ26, FQ27, FQ28, FQ29, FQ30, FQ31, FQ32]

@[expose] noncomputable def cm72T (i : Nat) : Bool :=
  vtChunkK RM112 GT3 (vptsK RM112 cmCode4 CH72.flatten) (CH72.getD i []) (FCP0.getD i 0) (1 + 1024 * i)

@[expose] noncomputable def cm72I (i : Nat) : Bool := inSK (cmPch.getD i []) SPC72.flatten

@[expose] noncomputable def cm72S (i : Nat) : Bool := spInK (SPC72.getD i []) cmPch

@[expose] noncomputable def cm72Q (i : Nat) : Bool :=
  andB (eqLK (sortN (cmPch.getD i [])) (FQL.getD i []))
    (eqLK (diffS (FQL.getD i []) SPC72.flatten) List.nil)

@[expose] noncomputable def cm72R (i : Nat) : Bool :=
  eqLK (List.foldl (fun acc s => diffS acc s) (SPC72.getD i []) FQL) List.nil

#j4q_all CFSG.KD.Co1M.T72 CertificateChecks.KernelCo1M.cm72T 32
#j4q_all CFSG.KD.Co1M.Q72 CertificateChecks.KernelCo1M.cm72Q 33
#j4q_all CFSG.KD.Co1M.R72 CertificateChecks.KernelCo1M.cm72R 32

theorem cm72_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact (Bool.false_ne_true h).elim

theorem cm72_eqLK : ∀ {xs ys : List Nat}, eqLK xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | x :: xs, y :: ys, h => by
    change andB (Nat.beq x y) (eqLK xs ys) = true at h
    obtain ⟨hxy, htail⟩ := cm72_andB h
    rw [Nat.eq_of_beq_eq_true hxy, cm72_eqLK htail]

theorem cm72_sorted {i : Nat} (hi : i < 33) :
    sortN (cmPch.getD i []) = FQL.getD i [] ∧ inSK (cmPch.getD i []) SPC72.flatten = true := by
  obtain ⟨h1, h2⟩ := cm72_andB (Q72.all i hi)
  have e := cm72_eqLK h1
  refine ⟨e, ?_⟩
  unfold inSK
  rw [e]
  exact h2

theorem _root_.CFSG.KD.Co1M.I72.all : ∀ t < 33, cm72I t = true := fun _ ht => (cm72_sorted ht).2

theorem cm72_map : cmPch.map sortN = FQL := by
  have hl : cmPch.length = 33 := rfl
  have hq : FQL.length = 33 := rfl
  refine List.ext_getElem (by rw [List.length_map, hl, hq]) fun i h1 h2 => ?_
  rw [List.getElem_map]
  have hi : i < 33 := by rw [hq] at h2; exact h2
  have e := (cm72_sorted hi).1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hl]; exact hi), List.getElem?_eq_getElem (by rw [hq]; exact hi),
    Option.getD_some, Option.getD_some] at e
  exact e

theorem _root_.CFSG.KD.Co1M.S72.all : ∀ t < 32, cm72S t = true := by
  intro t ht
  have h := R72.all t ht
  unfold cm72R at h
  rw [← cm72_map, List.foldl_map] at h
  exact h

theorem cm72_size : andB (Nat.beq (CH72.flatten.length + 1) 32400)
    (andB (Nat.beq SPC72.flatten.length 32400)
      (andB (allR 31 fun i => Nat.beq (CH72.getD i []).length 1024)
        (andB (CH72.all fun ch => Nat.ble ch.length 1024) (SPC72.all fun sc => Nat.ble sc.length 1024)))) =
    true := by quickRfl

theorem cm72_sinc : sincK SPC72.flatten 0 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
