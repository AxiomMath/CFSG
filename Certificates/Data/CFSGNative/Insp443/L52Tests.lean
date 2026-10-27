module

public import Certificates.Data.CFSGNative.Insp443.PermTests

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def c2TestS (n : Nat) (us : List Table) (e : Nat) (T : Table) : Bool :=
  commAllT n us T && !(powFixW n [T] e)

@[expose] def sTestS (n : Nat) (us spZ spW : List Table) (cs : List (Table × Table)) (T : Table) :
    Bool :=
  commAllT n us T && !(inSp n spZ T) && !(inSp n spW T) &&
    cs.all fun ab => commT2 n T (compT n (compT n ab.1 T) ab.2)

@[expose] def cnTestS (n : Nat) (us vs spV spW : List Table) (T : Table) : Bool :=
  commAllT n us T && conjIn n vs spV T && !(inSp n spW T)

@[expose] def perm3TestS (n : Nat) (ws spW : List Table) (as spAs : List (List Table))
    (T : Table) : Bool :=
  conjIn n ws spW T && !((List.range 3).all fun i => (List.range 3).any fun j =>
    conjIn n (as.getD i []) (spAs.getD j []) T)

end CFSG.SectionRank.QTK.Insp443.PermKit.Native

end
