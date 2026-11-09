module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.CoreE

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def tableOkE (inv L eps nLab nT N RW RM nR nS nW nF : Nat)
    (F D Wd Wd2 R S : Nat → Nat) (amap : Nat) (rels words : List (List (Nat × Bool)))
    (walk cov : List Nat) : Bool :=
  andB (Nat.ble (Nat.succ L) (nat_lit 128))
  (andB (Nat.ble (nat_lit 1) N)
  (andB (Nat.ble N nLab)
  (andB (Nat.beq nLab (Nat.succ nT))
  (andB (Nat.ble (Nat.succ nLab) bad)
  (andB (Nat.ble (Nat.succ nF) bad)
  (andB (Nat.ble (Nat.succ nR) bad)
  (andB (Nat.ble (Nat.succ nS) bad)
  (andB (lensLt rels (nat_lit 256))
  (andB (lensLt words (nat_lit 256))
  (andB (hdrOk inv L eps amap)
  (andB (relsOk R nR amap rels)
  (andB (subsOk S nS amap words)
  (andB (wordsOkB Wd R S inv eps nR nS nW)
  (andB (words2Ok Wd Wd2 inv nW)
  (andB (treeRange F D L nLab (nat_lit 0) nT)
  (andB (Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF)
    (Nat.beq (wCovListE F RW RM N (Nat.shiftRight L (nat_lit 1)) nF cov (nat_lit 0)) N)))))))))))))))))

@[expose] def TableFactE (m : Nat) (rels words : List (List (Nat × Bool))) (N : Nat) : Prop :=
  ∃ (inv L eps nLab nT RW RM nR nS nW nF : Nat) (F D Wd Wd2 R S : Nat → Nat) (amap : Nat)
    (walk cov : List Nat),
    tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov = true ∧
      topOk amap m = true

theorem TableFactE.intro {m : Nat} {rels words : List (List (Nat × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : Nat} {F D Wd Wd2 R S : Nat → Nat} {amap : Nat}
    {walk cov : List Nat}
    (h : tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true)
    (htop : topOk amap m = true) : TableFactE m rels words N :=
  ⟨inv, L, eps, nLab, nT, RW, RM, nR, nS, nW, nF, F, D, Wd, Wd2, R, S, amap, walk, cov, h, htop⟩

end CFSG.Certificates.KB

end
