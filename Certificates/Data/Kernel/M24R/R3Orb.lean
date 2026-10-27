module

public import Certificates.Data.Kernel.KGC31P
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.M24R3

open CFSG.KC.Enum CFSG.KC.KGC31P
open CFSG.KC (andB orB)

@[expose] noncomputable def oFld (x o m : Nat) : Nat := Nat.land (Nat.shiftRight x o) m

@[expose] noncomputable def M120 : Nat := nat_lit 1329227995784915872903807060280344575

@[expose] noncomputable def GLIT : Nat := nat_lit 8717626987843785921689514621738908179095542677655960086552810632922518613447690298472658583831097067518633325552812529752840952662471749467971362449943199829376668952335527460465835850222009532884316146048199123373309635780695424875375004977631977006117068345953741130992467969761291642564917719318721274462555780265092752342317490924956288756139248415827623971

@[expose] noncomputable def GILIT : Nat := nat_lit 8717626987843785921689514621738908179095542677655960086552810632922518613447690298472658583831097067518633325552812529752840952662471749467971361092896194883445600182602455760924664274586282331481796701012280308627513576368168735482876664043031504443852100488516021472789322832281106601984498008698203012606047217813520543008129415202979149754223987418327944226

@[expose] noncomputable def KY0 : Nat := nat_lit 2284193952214240267224289467495164866351516259713166614541930353404369764238036251824704223142872581073833367081767430317230595408147591442040868

@[expose] noncomputable def oRoot : Nat := nat_lit 17202

@[expose] noncomputable def rPar (r : Nat) : Nat := oFld r (nat_lit 15) (nat_lit 32767)

@[expose] noncomputable def rGen (r : Nat) : Nat := oFld r (nat_lit 30) (nat_lit 15)

@[expose] noncomputable def rDep (r : Nat) : Nat := oFld r (nat_lit 34) (nat_lit 63)

@[expose] noncomputable def rKey (r : Nat) : Nat := Nat.shiftRight r (nat_lit 40)

@[expose] noncomputable def kEnt (K j : Nat) : Nat := oFld K (Nat.mul (nat_lit 120) j) M120

@[expose] noncomputable def entOK (gi g K K' j : Nat) : Bool :=
  Nat.beq (kEnt K' j) (pcj 24 5 gi g (kEnt K j))

@[expose] noncomputable def cjOK (k K K' : Nat) : Bool :=
  strictB (kEnt GILIT k) fun gi => strictB (kEnt GLIT k) fun g =>
    andB (entOK gi g K K' (nat_lit 0)) (andB (entOK gi g K K' (nat_lit 1))
      (andB (entOK gi g K K' (nat_lit 2)) (entOK gi g K K' (nat_lit 3))))

@[expose] noncomputable def recOK (F : Nat → Nat) (n r : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight r (nat_lit 520)) (nat_lit 0))
    (Bool.rec
      (strictB (F (rPar r)) fun p =>
        andB (Nat.blt (rPar r) (nat_lit 20160)) (andB (Nat.blt (rGen r) (nat_lit 10))
          (andB (Nat.beq (Nat.succ (rDep p)) (rDep r)) (cjOK (rGen r) (rKey p) (rKey r)))))
      (andB (Nat.beq (rDep r) (nat_lit 0)) (Nat.beq (rKey r) KY0))
      (Nat.beq n oRoot))

@[expose] noncomputable def orbOK (F : Nat → Nat) (n : Nat) : Bool :=
  strictB (F n) fun r =>
    andB (orB (Nat.beq n (nat_lit 0)) (Nat.blt (rKey (F (Nat.sub n (nat_lit 1)))) (rKey r)))
      (recOK F n r)

@[expose] noncomputable def orbBlk (F : Nat → Nat) (lo cnt : Nat) : Bool := allBlk lo (orbOK F) cnt

end CFSG.KC.M24R3

end
