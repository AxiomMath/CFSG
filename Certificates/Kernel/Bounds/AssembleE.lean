module

public import Certificates.Kernel.Bounds.Assemble
public import Certificates.Data.Kernel.Bounds.TableE

public section

namespace CFSG.Certificates.KB

theorem wCovListE_append (F : Nat → Nat) (RW RM N Lh nF : Nat) :
    ∀ (l1 l2 : List Nat) (x : Nat), wCovListE F RW RM N Lh nF (List.append l1 l2) x =
      wCovListE F RW RM N Lh nF l2 (wCovListE F RW RM N Lh nF l1 x)
  | [], _, _ => rfl
  | E :: l1, l2, x => wCovListE_append F RW RM N Lh nF l1 l2 (wCovElemE F RW RM N Lh nF E x)

theorem covE_step (F : Nat → Nat) (RW RM N Lh nF : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (wCovListE F RW RM N Lh nF l1 x) y = true)
    (h2 : Nat.beq (wCovListE F RW RM N Lh nF l2 y) z = true) :
    Nat.beq (wCovListE F RW RM N Lh nF (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [wCovListE_append, h1, h2]

theorem tableOkE_intro (inv L eps nLab nT N RW RM nR nS nW nF : Nat) (F D Wd Wd2 R S : Nat → Nat)
    (amap : Nat) (rels words : List (List (Nat × Bool))) (walk cov : List Nat)
    (h1 : Nat.ble (Nat.succ L) (nat_lit 128) = true) (h2 : Nat.ble (nat_lit 1) N = true)
    (h3 : Nat.ble N nLab = true)
    (h4 : Nat.beq nLab (Nat.succ nT) = true) (h5 : Nat.ble (Nat.succ nLab) bad = true)
    (h6 : Nat.ble (Nat.succ nF) bad = true) (h6a : Nat.ble (Nat.succ nR) bad = true)
    (h6b : Nat.ble (Nat.succ nS) bad = true) (h6c : lensLt rels (nat_lit 256) = true)
    (h6d : lensLt words (nat_lit 256) = true) (h7 : hdrOk inv L eps amap = true)
    (h8 : relsOk R nR amap rels = true) (h9 : subsOk S nS amap words = true)
    (h10 : wordsOkB (fun i => Wd (Nat.add i (nat_lit 0))) R S inv eps nR nS nW = true)
    (h11 : words2Ok (fun i => Wd (Nat.add i (nat_lit 0))) (fun i => Wd2 (Nat.add i (nat_lit 0)))
      inv nW = true)
    (h12 : treeRange F D L nLab (nat_lit 0) nT = true)
    (h13 : Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF = true)
    (h14 : Nat.beq (wCovListE F RW RM N (Nat.shiftRight L (nat_lit 1)) nF cov (nat_lit 0)) N =
      true) :
    tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true := by
  have h10' : wordsOkB Wd R S inv eps nR nS nW = true := h10
  have h11' : words2Ok Wd Wd2 inv nW = true := h11
  simp only [tableOkE, andB_eq, h1, h2, h3, h4, h5, h6, h6a, h6b, h6c, h6d, h7, h8, h9, h10', h11',
    h12, h13, h14, Bool.and_self]

end CFSG.Certificates.KB

end
