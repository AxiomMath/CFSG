module

public import Certificates.Data.J4Ov.Fam
public import Certificates.Data.J4Ov.Reps
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

instance : Hashable V2 := ⟨V2.hash⟩

@[expose] def repZ (r : RepEntry) : Array V2 :=
  mulRows (kR r.l) (wordRows (locMats ()) (locInvs ()) (decodeWord r.xw))

end CFSG.Quasithin.J4Ov
