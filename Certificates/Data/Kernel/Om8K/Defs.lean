module

public import CFSG.CGT.Harada80.OmegaEightCheck
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.KC.Om8K

open CFSG.CGT.Harada80 CFSG.CGT.Harada80.OmegaEight

@[expose] noncomputable def mAppK (M : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih x => Nat.xor (cond (Nat.beq (Nat.land x 1) 1) c 0) (ih (Nat.shiftRight x 1))) M x

@[expose] noncomputable def bK (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) 1

@[expose] noncomputable def polS (x u : Nat) : Nat :=
  bK x 0 * bK u 3 + bK x 3 * bK u 0 + bK x 1 * bK u 4 + bK x 4 * bK u 1 + bK x 2 * bK u 5 +
    bK x 5 * bK u 2 + bK x 6 * bK u 7 + bK x 7 * bK u 6

@[expose] noncomputable def qS (c : Nat) : Nat :=
  bK c 0 * bK c 3 + bK c 1 * bK c 4 + bK c 2 * bK c 5 + bK c 6 + bK c 6 * bK c 7 + bK c 7

@[expose] noncomputable def reflK (u x : Nat) : Nat :=
  cond (Nat.beq (Nat.mod (polS x u) 2) 1) (Nat.xor x u) x

@[expose] noncomputable def nsMask : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor (Nat.shiftLeft 1 c) ih) nsCodes

@[expose] noncomputable def nsKW (M : Nat) : Bool := (List.range 256).all fun c =>
  Nat.beq (Nat.mod (qS c) 2) (bK M c)

@[expose] noncomputable def nsK : Bool := nsKW nsMask

@[expose] noncomputable def genKW (C : List (List Nat)) : Bool :=
  (List.range 2).all fun i => (List.range 256).all fun x =>
    Nat.beq (mAppK (C.getD i []) x)
      (List.rec (motive := fun _ => Nat) x (fun u _ ih => reflK u ih) (sChain i))

@[expose] noncomputable def genK : Bool := genKW sCols

@[expose] noncomputable def foxK (l : Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.xor v (mAppK (sCols.getD l []) ih)) 5

@[expose] noncomputable def bmap : Nat := List.rec (motive := fun _ => Nat) 0 (fun x _ ih =>
  Nat.lor ih (Nat.shiftLeft 1 (Nat.add (Nat.mul (Nat.xor (mAppK (sCols.getD 0 []) x) x) 256)
    (Nat.xor (mAppK (sCols.getD 1 []) x) x)))) (List.range 256)

@[expose] noncomputable def foxB (B : Nat) : Bool :=
  (List.range 256).all fun v₀ =>
    !Nat.beq (foxK 0 v₀) 0 || (List.range 256).all fun v₁ =>
        !Nat.beq (foxK 1 v₁) 0 || Nat.beq (bK B (v₀ * 256 + v₁)) 1

@[expose] noncomputable def LM : Nat := 72340172838076673

@[expose] noncomputable def laneApp (M : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih X => Nat.xor (Nat.mul (Nat.land X LM) c) (ih (Nat.shiftRight X 1))) M X

@[expose] noncomputable def wordLanes (cs : List Char) : Nat :=
  List.rec (motive := fun _ => Nat) 9241421688590303745
    (fun ch _ ih => laneApp (cond (Nat.beq ch.toNat 49) (sCols.getD 1 []) (sCols.getD 0 [])) ih) cs

@[expose] noncomputable def lanesOf (g : Nat → Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun j _ ih => Nat.add (g j) (Nat.mul 256 ih)) L

@[expose] noncomputable def target (u : Nat) : Nat :=
  lanesOf (fun j => reflK u (reflK v0Code (Nat.shiftLeft 1 j))) (List.range 8)

@[expose] noncomputable def wordsK (C : List (List Char)) : Bool :=
  Nat.beq nsCodes.length C.length && (nsCodes.zip C).all fun p => Nat.beq (wordLanes p.2) (target p.1)

end CFSG.KC.Om8K

end
