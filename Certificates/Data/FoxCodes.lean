module

public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Array.Basic

public section

namespace CFSG.CGT.Foote82.FoxH1

@[expose] def foxW (gs : Array (Array Nat)) (vals : Array Nat) : List Nat → Nat
  | [] => 0
  | i :: w => vals[i]! ^^^ (gs[i]!)[foxW gs vals w]!

@[expose] def foxCheck2 (N : Nat) (gs : Array (Array Nat)) (rels : List (List Nat)) : Bool :=
  let ga := gs[0]!
  let gb := gs[1]!
  (List.range N).all fun α => (List.range N).all fun β =>
    !(rels.all fun w => foxW gs #[α, β] w == 0) ||
      (List.range N).any fun c => α == (ga[c]! ^^^ c) && β == (gb[c]! ^^^ c)

end CFSG.CGT.Foote82.FoxH1
