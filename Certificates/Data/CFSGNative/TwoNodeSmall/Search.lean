module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchT
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchO
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchW

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def find (P : Pt) : Option Witness :=
  (match findK P with
    | some w => if verify P (.kernel w) then some (.kernel w) else none
    | none => none) <|>
  (match findT P with
    | some t => if verify P (.transv t) then some (.transv t) else none
    | none => none) <|>
  (match findO P P.bound with
    | some o => if verify P (.order o) then some (.order o) else none
    | none => none) <|>
  (match findW P with
    | some c => if verify P (.weyl c) then some (.weyl c) else none
    | none => none)

end CFSG.TwoNodeSmall
