module

public import Certificates.Data.Kernel.B433Alt.FCent
public import Certificates.Kernel.B433Alt.FixOK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AZ "Certificates/Kernel/B433Alt/Data/fcent.json.gz" 2452 17045138658914910267
  (PT : List Nat) (TW : List (List Nat)) (SK : List Nat) (SA : List Nat) (SP : List Nat)

namespace CFSG.KD.B4AZ

open CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Y333

@[expose] noncomputable def FS : Nat := fixW CFSG.KD.YMY432F.Nf fiveWL

@[expose] noncomputable def permW (p : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (dpW (TW.getD (Nat.sub p 1) [])) fiveWL.reverse (Nat.beq p 0)

@[expose] noncomputable def levelChk (i : Nat) : Bool :=
  Nat.ble (popc (nat_lit 15) (codeSet CFSG.KD.YMY432F.Nf CFSG.KD.B4AX.F0 FS (PT.getD i 0)
    (TW.take i) (PT.take i))) (SA.getD i 0)

@[expose] noncomputable def e7W : List Nat :=
  ([0, 1, 12, 16, 19, 20].map fun j => dpW (TW.getD j [])).flatten

@[expose] noncomputable def ordChk : Bool :=
  andB (isOne CFSG.KD.B4A.LP (wOfL (List.replicate 5 fiveWL).flatten))
  (andB (notB (Nat.beq (ev1 CFSG.KD.B4A.LP (wOfL fiveWL) (nat_lit 2)) (nat_lit 2)))
  (andB (isOne CFSG.KD.B4A.LP (wOfL (List.replicate 7 e7W).flatten))
  (andB (notB (Nat.beq (ev1 CFSG.KD.B4A.LP (wOfL e7W) (nat_lit 0)) (nat_lit 0)))
    (isOne CFSG.KD.B4A.LP (wOfL (e7W ++ fiveWL ++ e7W.reverse ++ fiveWL.reverse))))))

@[expose] noncomputable def deriveChk (i : Nat) : Bool :=
  andB (Nat.blt (SA.getD i 0) i) (andB (Nat.ble (SP.getD i 0) i)
    (Nat.beq (apP CFSG.KD.YMY432F.Nf (nat_lit 1) (permW (SP.getD i 0))
      (Nat.shiftLeft (nat_lit 1) (PT.getD (SA.getD i 0) 0)))
      (Nat.shiftLeft (nat_lit 1) (PT.getD i 0))))

@[expose] noncomputable def stepChk (i : Nat) : Bool :=
  andB (hubOK CFSG.KD.YMY432F.Nf (PT.getD i 0) (TW.getD i []))
    (Bool.rec (motive := fun _ => Bool) (deriveChk i) (levelChk i) (Nat.beq (SK.getD i 0) 0))

end CFSG.KD.B4AZ

end
