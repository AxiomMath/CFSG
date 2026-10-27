module

public import Certificates.Data.Kernel.FiveStdKCover

public section

namespace CFSG.KC.FiveStdK

@[expose] def keyC (c : Nat) : Nat := c % 390625 * 2 + c / 390625

@[expose] def unkeyC (k : Nat) : Nat := k / 2 + 390625 * (k % 2)

theorem unkeyC_keyC {c : Nat} (h : c < 781250) : unkeyC (keyC c) = c := by
  unfold unkeyC keyC
  omega

@[expose] noncomputable def normKc (K1 K2 : List Nat) (c : Nat) : Bool :=
  normKK K1 c && normKK K2 c

@[expose] noncomputable def tpCond (a b : Nat) : Bool :=
  ordK a == 4 && ordK b == 4 && Nat.beq (mulK a b) (mulK b a) && decide (ppK a b 4 4).Nodup

@[expose] noncomputable def tpL (els : List Nat) : List (Nat × Nat) :=
  els.flatMap fun a => els.filterMap fun b => if tpCond a b then some (a, b) else none

@[expose] noncomputable def checkPK (K1 : List Nat) (t u a b : Nat) (P : List Nat) (tp : List (Nat × Nat)) :
    Bool :=
  let H0 := ppK a b 4 4
  P.length == 64 &&
  tp.all (fun p => H0.contains p.1 && H0.contains p.2) &&
  H0.contains zK && H0.contains u &&
  P.all (fun p => [a, b].all fun x => H0.contains (cjK p (invK p) x)) &&
  P.all (fun p => H0.contains (mulK p p)) &&
  !(K1.filter fun w => Nat.beq (mulK w w) zK && Nat.beq (cjK w (invK w) u) (mulK u zK)).isEmpty &&
  P.any (fun p => Nat.beq (cjK p (invK p) t) (mulK zK t))

end CFSG.KC.FiveStdK

end
