module

public import Certificates.Data.YamakiPres
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Kernel.Bounds.Family
public import Mathlib

open CFSG.CosetTable CFSG.ClassicalInvolution.Solomon73.Yamaki

public section

#kb_family "data/F550701.json.gz" 1662 18423029860487420592
  (r0 := restrictWords (subsetOf 12 [0, 1, 2, 3, 4, 5, 6, 7, 8]) (yamakiRels ()))
  (r1 := yamakiRels ())

end
