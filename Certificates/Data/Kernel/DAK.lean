module

public import Certificates.Data.Kernel.TWDK

public section

namespace Certificates.DAK

open Certificates.DepASmall Certificates.TWDK

set_option compiler.extract_closed false

@[expose] def dakCells (p N b c0 mi ni : Nat) : List GGDepANPair :=
  (List.range p).flatMap fun u =>
    let aa := ggDepANAaParam p N b c0 ((p - mi) % p) u 1
    if aa.getD 0 0 == 0 then
      (List.range p).flatMap fun s => (List.range p).filterMap fun t =>
        let ha := ggDepANHaParam p N b c0 ((p - ni) % p) s t
        if ggDepANDot p aa ha == 2 % p then some (ha, aa) else none
    else []

@[expose] def dakSingle (p N : Nat) (F : List GGDepANPair) (key : Nat × Nat × Nat × Nat)
    (wits : List KWit) (idx : List Nat) : Bool :=
  kAll2 (fun c i => kTest p N F [c] (wits.getD i kW0))
    (dakCells p N key.1 key.2.1 key.2.2.1 key.2.2.2) idx

@[expose] def dakSingleAt (p N : Nat) (F : List GGDepANPair) (S : List KSingleE) (i : Nat) : Bool :=
  match S[i]? with
  | some e => dakSingle p N F e.1 e.2.1 e.2.2
  | none => false

@[expose] def dakCover (N : Nat) (S : List KSingleE) : Bool :=
  (List.range (N - 1)).all fun b => (List.range (N - 1)).all fun c0 =>
    [1, 2].all fun mi => [1, 2].all fun ni =>
      !ggDepANPatB N b c0 mi ni || (S.map (·.1)).contains (b, c0, mi, ni)

end Certificates.DAK

end
