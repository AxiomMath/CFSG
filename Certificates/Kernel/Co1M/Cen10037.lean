module

public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10037
public import CFSG.Certificates.Kernel.Co1M.GmsPathSum
public meta import Certificates.Kernel.VecCert.Gen
public meta import Certificates.Kernel.Co1M.Data10037

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

@[expose] noncomputable def cen37 (j : Nat) : Nat :=
  CFSG.KC.GmsPath.cenAt CFSG.KD.Co1M.QP CFSG.KD.Co1M.MX CFSG.KD.Co1M.MY
    (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 98280 17 j

end CertificateChecks.KernelCo1M

open Lean Elab Command CFSG.KC.VecGen CFSG.KC.Tab in
elab "#c10037_census" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let n := 98280
  let mut S : Array Nat := #[]
  for k in [0:(n + 63) / 64] do
    let some v := (← getConstInfo (`CertificateChecks.KernelVec.Co1.S ++ Name.mkSimple s!"L{k}")).value?
      | throwError "#c10037_census: leaf {k} of S has no value"
    let .lit (.natVal x) := v | throwError "#c10037_census: leaf {k} of S is not a literal"
    for t in [0:64] do
      if S.size < n then S := S.push ((x >>> (32 * t)) % (1 <<< 32))
  let mem : Std.HashSet Nat := Std.HashSet.ofArray S
  let QP ← unsafe evalConst Nat ``CFSG.KD.Co1M.QP
  let MX ← unsafe evalConst Nat ``CFSG.KD.Co1M.MX
  let MY ← unsafe evalConst Nat ``CFSG.KD.Co1M.MY
  let par := fun (x : Nat) => Id.run do
    let mut r := false
    for k in [0:24] do
      if (x >>> k) % 2 == 1 then r := !r
    return r
  let cen := fun (j : Nat) =>
    let p := S[j]!
    if p < (1 <<< 24) && !par (p &&& MX) && !par (p &&& MY) &&
        !(p == 0 || p == 2 || p == 4 || p == 6) && !par (vm 24 QP p &&& p) then
      let m := if mem.contains (p ^^^ 2) then 1 else 2
      if mem.contains (p ^^^ 4) then m else if mem.contains (p ^^^ 6) then m else 2 * m
    else 0
  let P := `CertificateChecks.KernelCo1M
  let f := mkConst (P ++ `cen37)
  let sumN := fun (k : Expr) => mkApp2 (mkConst ``CFSG.KLie.CT.sumN) k f
  let mut pf := mkApp2 (mkConst ``Eq.refl [1]) natT (lit 0)
  let mut acc := 0
  for s in [0:(n + 255) / 256] do
    let lo := 256 * s
    let cnt := min 256 (n - lo)
    let mut c := 0
    for i in [0:cnt] do
      c := c + cen (lo + i)
    let nm := P ++ `C37 ++ Name.mkSimple s!"cen_{s}"
    addThm nm (isTrue (mkApp2 (mkConst ``Nat.beq)
      (mkAppN (mkConst ``CFSG.KC.GmsPath.sumS) #[lit lo, lit cnt, f]) (lit c))) reflBoolTrue
    pf := mkAppN (mkConst ``CFSG.KC.GmsPath.sum_chain) #[f, lit lo, lit acc, lit cnt, lit c, pf,
      mkConst nm]
    acc := acc + c
  addThm (P ++ `cen37All) (mkApp3 (mkConst ``Eq [1]) natT (sumN (lit n)) (lit acc)) pf

#c10037_census

end
