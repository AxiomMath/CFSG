module

public import Certificates.Data.Kernel.Bounds.Table

public section

namespace CFSG.Certificates.KB

@[expose] def TableFact (m : Nat) (rels words : List (List (Nat × Bool))) (N : Nat) : Prop :=
  ∃ (inv L eps nLab nT RW RM nR nS nW nF : Nat) (F D Wd Wd2 R S : Nat → Nat) (amap : Nat)
    (walk cov : List Nat),
    tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov = true ∧
      topOk amap m = true

theorem TableFact.intro {m : Nat} {rels words : List (List (Nat × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : Nat} {F D Wd Wd2 R S : Nat → Nat} {amap : Nat}
    {walk cov : List Nat}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov = true)
    (htop : topOk amap m = true) : TableFact m rels words N :=
  ⟨inv, L, eps, nLab, nT, RW, RM, nR, nS, nW, nF, F, D, Wd, Wd2, R, S, amap, walk, cov, h, htop⟩

end CFSG.Certificates.KB
