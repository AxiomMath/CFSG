module

public meta import Certificates.Data.Kernel.MaxD2.Gen

public section

namespace CFSG.KS.MaxD2.Gen

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

meta def invIdx (D : Data) (P : Pre) : Array Nat :=
  let idx := indexOf P.nT
  P.nT.map fun a => idx.getD (invTab D.n a) 0

meta def conjIdx (D : Data) (P : Pre) : Array Nat :=
  let u := (rGens D)[0]!
  let cs := P.nT.map fun a => conjTab D.n a (invTab D.n a) u
  let idx := indexOf cs
  P.rT.map fun x => idx.getD x 0

meta def nonCommPair (D : Data) (P : Pre) : Array Nat :=
  let gs := nGens D
  let gi := nGensI D
  let rIdx := indexOf P.rT
  let ps := (List.range gs.size).flatMap fun i => (List.range gs.size).map fun j => (i, j)
  match ps.find? (fun (i, j) => !found rIdx P.rT (commTab D.n gs[i]! gs[j]! gi[i]! gi[j]!)) with
  | some (i, j) => #[i, j]
  | none => #[0, 0]

end CFSG.KS.MaxD2.Gen

end
