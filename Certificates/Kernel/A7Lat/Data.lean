module

public import Certificates.Data.Kernel.CosetLat.Defs
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat EL
  "Certificates/Kernel/A7Lat/data/el.bin.gz" 4 4 260 3405870532709925696
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat TE
  "Certificates/Kernel/A7Lat/data/te.bin.gz" 4 4 32 18100795018634731174
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat TP
  "Certificates/Kernel/A7Lat/data/tp.bin.gz" 4 4 32 14988634174925873820
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat TS
  "Certificates/Kernel/A7Lat/data/ts.bin.gz" 4 4 32 4023578954133065578
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat TC
  "Certificates/Kernel/A7Lat/data/tc.bin.gz" 4 4 64 2835073729914243262
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat UE
  "Certificates/Kernel/A7Lat/data/ue.bin.gz" 4 4 1260 10658840658354069834
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat UR
  "Certificates/Kernel/A7Lat/data/ur.bin.gz" 4 4 1260 5892503591013262503
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat CR
  "Certificates/Kernel/A7Lat/data/cr.bin.gz" 8 4 8136 3992479816270205147
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat MJ
  "Certificates/Kernel/A7Lat/data/mj.bin.gz" 4 4 504 15851839940740128376
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat SE
  "Certificates/Kernel/A7Lat/data/se.bin.gz" 4 4 348 11026627419649377563
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat SP
  "Certificates/Kernel/A7Lat/data/sp.bin.gz" 4 4 348 2094760184565812087
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat SS
  "Certificates/Kernel/A7Lat/data/ss.bin.gz" 4 4 348 2249228326752276187
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat SC
  "Certificates/Kernel/A7Lat/data/sc.bin.gz" 4 4 456 4229534725226717721
#kc_repo #kc_ktree_gz CertificateChecks.KernelA7Lat SK
  "Certificates/Kernel/A7Lat/data/sk.bin.gz" 4 4 80 14391951296817581808
#kc_repo #kc_json_gz CertificateChecks.KernelA7Lat
  "Certificates/Kernel/A7Lat/data/w7250.json.gz" 13894 8007898194359706275
  (subW : List (List Nat)) (repM : List (List Nat)) (repW : List (List (List Nat)))
  (joinW : List (List (List Nat))) (mInL : List (List Nat)) (lInM : List (List Nat))

public section

namespace CertificateChecks.KernelA7Lat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat

@[expose] noncomputable def m7 : Nat → Nat → Nat :=
  CFSG.KC.Enum.pcomp (nat_lit 7) (nat_lit 4) (CFSG.KS.mask (nat_lit 4))

@[expose] noncomputable def one7 : Nat := CFSG.KC.Enum.pidn (nat_lit 7) (nat_lit 4)

@[expose] noncomputable def lenL (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 3) (nat_lit 4) (Nat.beq t (nat_lit 6)))
    (nat_lit 2) (Nat.beq t (nat_lit 0))

@[expose] noncomputable def xo (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 4) t) (Nat.add (nat_lit 3) t)
    (Nat.blt t (nat_lit 7))

@[expose] noncomputable def LG (t j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (EL (Nat.add (xo t) (Nat.sub j (nat_lit 2)))) (EL j)
    (Nat.blt j (nat_lit 2))

@[expose] noncomputable def MG (j : Nat) : Nat := EL (Nat.add (nat_lit 2) j)

@[expose] noncomputable def LGG (a b l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (LG b (Nat.sub l (lenL a))) (LG a l) (Nat.blt l (lenL a))

@[expose] noncomputable def RC (a : Nat) : Nat := EL (Nat.add (nat_lit 16) a)

@[expose] noncomputable def TR (j l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RC j) (EL l) (Nat.blt l (nat_lit 2))

@[expose] noncomputable def getW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub i 1)) x
      (Nat.beq i (nat_lit 0))) l i

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def nth (l : List Nat) (i : Nat) : Nat := hd (List.drop i l)

@[expose] noncomputable def allIx (l : List (List (List Nat)))
    (f : Nat → List (List Nat) → Bool) (i₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => andB (f i x) (ih (Nat.succ i))) l i₀

@[expose] noncomputable def wordsAt (A : Nat → Nat) (nA : Nat) (ws : List (List Nat)) (o : Nat)
    (G : Nat → Nat) (n : Nat) : Bool :=
  allN n fun k => wordAt m7 one7 A nA (getW ws (Nat.add o k)) (G k)

@[expose] noncomputable def tOK : Bool :=
  allN (nat_lit 8) fun k => andB (treeAt m7 one7 EL (nat_lit 2) TE TP k)
    (andB (sortAt (nat_lit 8) TE TS k) (closedAt m7 EL (nat_lit 2) (nat_lit 8) TE TC k))

@[expose] noncomputable def uOK : Bool :=
  andB (Nat.beq (UE (nat_lit 0)) one7)
    (allN (nat_lit 315) (transAt m7 RC (nat_lit 49) TE (nat_lit 8) UE UR))

@[expose] noncomputable def ch7250m (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 105) s) (nat_lit 105)
    (ctabAt m7 MG (nat_lit 2) TE (nat_lit 8) UE (nat_lit 315) CR)

@[expose] noncomputable def memOK (t n o r₀ : Nat) : Bool :=
  andB (Nat.beq (MJ o) (nat_lit 0)) (andB (allN n fun i => Nat.blt (MJ (Nat.add o i)) (nat_lit 315))
    (allN n (ctabAt m7 (LG t) (lenL t) TE (nat_lit 8) (fun i => UE (MJ (Nat.add o i))) n
      (fun r => CR (Nat.add r₀ r)))))

@[expose] noncomputable def subOK (t N nK oE oC oK : Nat) : Bool :=
  andB (wordsAt (LG t) (lenL t) subW oK (fun j => SK (Nat.add oK j)) nK)
    (allN N fun k => andB
      (treeAt m7 one7 (fun j => SK (Nat.add oK j)) nK (fun i => SE (Nat.add oE i))
        (fun i => SP (Nat.add oE i)) k)
      (andB (sortAt N (fun i => SE (Nat.add oE i)) (fun i => SS (Nat.add oE i)) k)
        (closedAt m7 (fun j => SK (Nat.add oK j)) nK N (fun i => SE (Nat.add oE i))
          (fun r => SC (Nat.add oC r)) k)))

@[expose] noncomputable def repMOK : Bool :=
  wordsAt MG (nat_lit 2) repM (nat_lit 0) RC (nat_lit 49)

@[expose] noncomputable def repAt (j : Nat) (e : List (List Nat)) : Bool :=
  letB (hd (getW e 0)) fun t => andB (Nat.blt t (nat_lit 12))
    (andB (wordAt m7 one7 (LG t) (lenL t) (getW e 1) (RC j))
      (wordsAt (TR j) (nat_lit 3) e (nat_lit 2) (LG t) (lenL t)))

@[expose] noncomputable def repOK : Bool :=
  andB (Nat.beq (List.length repW) (nat_lit 49)) (allIx repW repAt (nat_lit 0))

@[expose] noncomputable def joinAt (e : List (List Nat)) : Bool :=
  letB (nth (getW e 0) 0) fun a => letB (nth (getW e 0) 1) fun b =>
  letB (nth (getW e 0) 2) fun c =>
    andB (Nat.blt a (nat_lit 12)) (andB (Nat.blt b (nat_lit 12)) (andB (Nat.blt c (nat_lit 12))
    (andB (wordsAt (LGG a b) (Nat.add (lenL a) (lenL b)) e (nat_lit 1) (LG c) (lenL c))
    (andB (wordsAt (LG c) (lenL c) e (Nat.add (nat_lit 1) (lenL c)) (LG a) (lenL a))
      (wordsAt (LG c) (lenL c) e (Nat.add (Nat.add (nat_lit 1) (lenL c)) (lenL a)) (LG b)
        (lenL b))))))

@[expose] noncomputable def joinOK : Bool :=
  andB (allIx joinW (fun _ e => joinAt e) (nat_lit 0))
    (allN (nat_lit 12) fun a => allN (nat_lit 12) fun b =>
      notB (allIx joinW (fun _ e => notB (andB (Nat.beq (nth (getW e 0) 0) a)
        (Nat.beq (nth (getW e 0) 1) b))) (nat_lit 0)))

@[expose] noncomputable def topOK : Bool :=
  andB (wordsAt (LG (nat_lit 11)) (nat_lit 3) mInL (nat_lit 0) MG (nat_lit 2))
    (wordsAt MG (nat_lit 2) lInM (nat_lit 0) (LG (nat_lit 11)) (nat_lit 3))

end CertificateChecks.KernelA7Lat

end
