module

public import Certificates.Data.Kernel.Bounds.Table

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def factsOk (inv L eps nLab nT RW RM nR nS nW nF : Nat)
    (F D Wd Wd2 R S : Nat → Nat) (amap : Nat) (rels words : List (List (Nat × Bool)))
    (walk : List Nat) : Bool :=
  andB (Nat.ble (Nat.succ L) (nat_lit 128))
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
    (Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF))))))))))))))

theorem factsOk_intro (inv L eps nLab nT RW RM nR nS nW nF : Nat) (F D Wd Wd2 R S : Nat → Nat)
    (amap : Nat) (rels words : List (List (Nat × Bool))) (walk : List Nat)
    (h1 : Nat.ble (Nat.succ L) (nat_lit 128) = true)
    (h4 : Nat.beq nLab (Nat.succ nT) = true) (h5 : Nat.ble (Nat.succ nLab) bad = true)
    (h6 : Nat.ble (Nat.succ nF) bad = true) (h6a : Nat.ble (Nat.succ nR) bad = true)
    (h6b : Nat.ble (Nat.succ nS) bad = true) (h6c : lensLt rels (nat_lit 256) = true)
    (h6d : lensLt words (nat_lit 256) = true) (h7 : hdrOk inv L eps amap = true)
    (h8 : relsOk R nR amap rels = true) (h9 : subsOk S nS amap words = true)
    (h10 : wordsOkB (fun i => Wd (Nat.add i (nat_lit 0))) R S inv eps nR nS nW = true)
    (h11 : words2Ok (fun i => Wd (Nat.add i (nat_lit 0))) (fun i => Wd2 (Nat.add i (nat_lit 0)))
      inv nW = true)
    (h12 : treeRange F D L nLab (nat_lit 0) nT = true)
    (h13 : Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF = true) :
    factsOk inv L eps nLab nT RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk = true := by
  have h10' : wordsOkB Wd R S inv eps nR nS nW = true := h10
  have h11' : words2Ok Wd Wd2 inv nW = true := h11
  simp only [factsOk, h1, h4, h5, h6, h6a, h6b, h6c, h6d, h7, h8, h9, h10', h11', h12, h13]
  rfl

end CFSG.Certificates.KB
