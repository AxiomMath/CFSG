module

public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CosetTable

@[expose] def invConsistentNative (L : Nat) (inv : Array Nat) (st : St) : Bool :=
  allBelow (fun c => !st.live c || allBelow (fun x =>
    st.tab.getD (st.tab.getD (c * L + x) 0 * L + inv.getD x 0) 0 == c) L) st.next

@[expose] def relsClosedNative (L : Nat) (st : St) (rels : List (List Nat)) : Bool :=
  allBelow (fun c => !st.live c || rels.all fun r =>
    r.foldl (fun c x => st.tab.getD (c * L + x) 0) c == c) st.next

end CFSG.CosetTable
