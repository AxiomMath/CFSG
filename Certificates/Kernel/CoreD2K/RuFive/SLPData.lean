module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.CoreD2RuFiveOne
meta import Std.Data.HashMap

namespace CertificateChecks.KernelCoreD2K.RuFive.SLPGen

open Certificates.CoreD2Perm

meta def symOf (z : Int) : Nat :=
  if z > 0 then 2 * (z.toNat - 1) else 2 * ((-z).toNat - 1) + 1

meta def subst (p : Nat × Nat) (sym : Nat) (s : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut j := 0
  while j < s.size do
    if j + 1 < s.size && s[j]! == p.1 && s[j + 1]! == p.2 then
      out := out.push sym
      j := j + 2
    else
      out := out.push s[j]!
      j := j + 1
  return out

meta def best (seqs : Array (Array Nat)) : (Nat × Nat) × Nat := Id.run do
  let mut cnt : Std.HashMap (Nat × Nat) Nat := {}
  for s in seqs do
    for i in [0:s.size - 1] do
      let p := (s[i]!, s[i + 1]!)
      cnt := cnt.insert p (cnt.getD p 0 + 1)
  let mut bp := (0, 0)
  let mut bk := 0
  for (p, k) in cnt.toList do
    if k > bk || (k == bk && (p.1 < bp.1 || (p.1 == bp.1 && p.2 < bp.2))) then
      bp := p
      bk := k
  return (bp, bk)

meta def grammar (nL : Nat) (ws : List (List Int)) : Array (Nat × Nat) × Array Nat := Id.run do
  let mut seqs : Array (Array Nat) := (ws.map fun wd => (wd.map symOf).toArray).toArray
  let mut rules : Array (Nat × Nat) := #[]
  for _ in [0:100000] do
    let (p, k) := best seqs
    if k < 2 then break
    let sym := nL + rules.size
    rules := rules.push p
    seqs := seqs.map (subst p sym)
  let mut tops : Array Nat := #[]
  for s in seqs do
    let mut t := s[s.size - 1]!
    for i in [0:s.size - 1] do
      rules := rules.push (s[s.size - 2 - i]!, t)
      t := nL + rules.size - 1
    tops := tops.push t
  return (rules, tops)

meta def vals (L : Array (Array Nat)) (rules : Array (Nat × Nat)) : Array (Array Nat) := Id.run do
  let mut vs := L
  for p in rules do
    vs := vs.push (CFSG.KS.RawGen.comp 4060 vs[p.1]! vs[p.2]!)
  return vs.extract L.size vs.size

meta def lets (S SI : Array (Array Nat)) : Array (Array Nat) :=
  (Array.range S.size).foldl (fun acc j => (acc.push S[j]!).push SI[j]!) #[]

meta def gA : Array (Nat × Nat) × Array Nat :=
  grammar 4 (ruFiveLinesData.base.eW ++ ruFiveLinesData.base.gWs)
meta def gB : Array (Nat × Nat) × Array Nat :=
  grammar 16 (ruFiveLinesData.wAs ++ ruFiveLinesData.wBs)

meta def gaA : Array (Array Nat) := gA.1.map fun p => #[p.1 ||| (p.2 <<< 16)]
meta def taA : Array (Array Nat) := gA.2.map fun t => #[t]
meta def vaA : Array (Array Nat) :=
  vals (lets (gsT ruFiveLinesData.base) (giT ruFiveLinesData.base)) gA.1
meta def gbA : Array (Array Nat) := gB.1.map fun p => #[p.1 ||| (p.2 <<< 16)]
meta def tbA : Array (Array Nat) := gB.2.map fun t => #[t]
meta def vbA : Array (Array Nat) :=
  vals (lets (gT ruFiveLinesData.base) (gTi ruFiveLinesData.base)) gB.1

end CertificateChecks.KernelCoreD2K.RuFive.SLPGen

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PAG CertificateChecks.KernelCoreD2K.RuFive.SLPGen.gaA 32
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PAT CertificateChecks.KernelCoreD2K.RuFive.SLPGen.taA 16
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PAV CertificateChecks.KernelCoreD2K.RuFive.SLPGen.vaA 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PBG CertificateChecks.KernelCoreD2K.RuFive.SLPGen.gbA 32
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PBT CertificateChecks.KernelCoreD2K.RuFive.SLPGen.tbA 16
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.PBV CertificateChecks.KernelCoreD2K.RuFive.SLPGen.vbA 12

end
