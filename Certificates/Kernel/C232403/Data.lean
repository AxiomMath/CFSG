module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Data.Kernel.WittBad
public import Certificates.Data.Kernel.B3S3K

public section

namespace CertificateChecks.KernelC232403

open CFSG.KC.WCnt CertificateChecks.KernelLC.Witt

@[expose] def vP : List Nat :=
  [374473820810397467963188798655048, 227707358736676187763505063102796,
    772848887539061409216438782362242, 738353339986023558624410005194219,
    509779425537146520962821480614117, 295620761381057711089745033005450]

@[expose] def eP : List Nat :=
  [52236562913631583998738592908512, 816414695726958460443398426265888,
    389451420345263520803813825431104]

@[expose] def wP : List Nat :=
  [260158709255585447191565231556752, 587658822352722723260776246815953,
    61175965338748633381371102988973]

@[expose] def fP : List Nat := [69889, 133125, 9249]

@[expose] def tP : List (List Bool) :=
  [[true, false, true, true, false, true, true, true, false, true],
    [true, true, true, false, true, false, true, false],
    [true, true, true, false, true, false, true, false, true, true]]

@[expose] def dP : List Nat :=
  [56024643061394886521445323985203, 539512025954651773468698428869189,
    381728985556582338889591835661858]

@[expose] def xP : List Nat := [7, 16, 16]
@[expose] def yP : List Nat := [21, 8, 8]
@[expose] def pP : List Nat := [16, 2, 0]

@[expose] def vK (k : Nat) : Nat := vP.getD k 0
@[expose] def eK (j : Nat) : Nat := eP.getD j 0
@[expose] def wK (j : Nat) : Nat := wP.getD j 0
@[expose] def fK (j : Nat) : Nat := fP.getD j 0
@[expose] def tK (j : Nat) : List Bool := tP.getD j []
@[expose] def dK (j : Nat) : Nat := dP.getD j 0

@[expose] noncomputable def cntW (j : Nat) (Vs : List Nat) : Nat :=
  wcB (badT (eK j) (vK (2 * j)) (vK (2 * j + 1)) Vs) (dK j)
    (fun x => bIf(inM (fK j) x, false, true)) (fun x0 x1 => Nat.beq x1 (pt (eK j) x0))
    (fun _ _ x2 => inM (fK j) x2)

@[expose] noncomputable def cntK (j : Nat) : Nat :=
  cntW j [vK (2 * j), vK (2 * j + 1), wK j]

@[expose] noncomputable def prodV (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (CFSG.KC.Enum.pidn 22 5)
    (fun k _ ih => CFSG.KC.B3S3K.cm 22 5 (vK k) ih) w

end CertificateChecks.KernelC232403

end
