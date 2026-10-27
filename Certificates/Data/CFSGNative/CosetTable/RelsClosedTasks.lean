module

public import Certificates.Data.CFSGNative.CosetTable.ActionNative

public section

namespace CFSG.CosetTable

@[expose] def relsClosedFrom (L : Nat) (st : St) (rels : List (List Nat)) (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => (!st.live lo || rels.all fun r => r.foldl (fun c x => st.tab.getD (c * L + x) 0) lo == lo) &&
      relsClosedFrom L st rels (lo + 1) n

@[expose] def splitRange (lo hi : Nat) : Nat → List (Nat × Nat)
  | 0 => [(lo, hi)]
  | d + 1 => splitRange lo ((lo + hi) / 2) d ++ splitRange ((lo + hi) / 2) hi d

@[expose] def relsClosedTasks (L : Nat) (st : St) (rels : List (List Nat)) : Bool :=
  ((splitRange 0 st.next 5).map fun r =>
    Task.spawn fun _ => relsClosedFrom L st rels r.1 (r.2 - r.1)).all Task.get

end CFSG.CosetTable
