module

public import Certificates.Data.F4ThreeRank
public import Certificates.Data.Kernel.U6Three.Defs
public import CFSG.Certificates.Kernel.TabPackSound

public section

namespace CFSG.KC.F4Three

open CFSG.RankThree.PartOne.F106 CFSG.LieType.Simplicity.TitsBits CFSG.KC.U6Three CFSG.KTabPack

@[expose] noncomputable def getN (L : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun a _ ih n => Nat.rec (motive := fun _ => ℕ) a (fun m _ => ih m) n) L

@[expose] noncomputable def getL (L : List (List ℕ)) : ℕ → List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun a _ ih n => Nat.rec (motive := fun _ => List ℕ) a (fun m _ => ih m) n) L

@[expose] noncomputable def look (TT : List (List ℕ)) (j : ℕ) : ℕ :=
  getN (getL TT (j / 27)) (j % 27)

@[expose] def chkTab (c : F4SylowCert) (GB : List ℕ) (TT : List (List ℕ)) : Bool :=
  TT.length == 27 && TT.all (fun l => l.length == 27) && TT.flatten == c.tabList GB

@[expose] noncomputable def chkNod (TT : List (List ℕ)) : Bool :=
  nodupN (TT.flatten.map (· % 2 ^ 2704))

@[expose] noncomputable def chkRt (GB : List ℕ) (TT : List (List ℕ)) (rt : List ℕ) : Bool :=
  allIdx (fun n r => Nat.blt r 729 &&
    Nat.beq (mul (look TT (n / 6)) (GB.getD (n % 6) 0) % 2 ^ 2704) (look TT r % 2 ^ 2704)) rt 0

@[expose] noncomputable def chkInv (TT : List (List ℕ)) (inv : List ℕ) : Bool :=
  allIdx (fun n v => Nat.blt v 729 &&
    Nat.beq (mul (look TT n) (look TT v) % 2 ^ 2704) (oneBits % 2 ^ 2704)) inv 0

@[expose] def conjL (inv : List ℕ) (tl : ℕ → ℕ) (i u : ℕ) : ℕ :=
  mul (mul (tl u) (tl i)) (tl (inv.getD u 0)) % 2 ^ 2704

@[expose] def commL (tl : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (mul (tl i) (tl j) % 2 ^ 2704 = mul (tl j) (tl i) % 2 ^ 2704)

@[expose] def witL (zl inv : List ℕ) (tl : ℕ → ℕ) (i : ℕ) : Wit → Bool
  | .exc => decide (i ∈ zl)
  | .conj4 u₀ u₁ u₂ u₃ =>
      decide (u₀ < 729 ∧ u₁ < 729 ∧ u₂ < 729 ∧ u₃ < 729) &&
        decide ([u₀, u₁, u₂, u₃].map (conjL inv tl i)).Nodup
  | .pair z x y =>
      decide (z < 729 ∧ x < 729 ∧ y < 729) && !commL tl z i && commL tl x i && commL tl y i &&
        !commL tl x y
  | .cube z x =>
      decide (z < 729 ∧ x < 729) && !commL tl z i && commL tl x i &&
        decide (mul (mul (tl x) (tl x)) (tl x) % 2 ^ 2704 ≠ oneBits % 2 ^ 2704)

@[expose] noncomputable def chkWit (TT : List (List ℕ)) (zl inv : List ℕ) (wit : List Wit) :
    Bool :=
  allIdx (fun n w => witL zl inv (look TT) n w) wit 0

end CFSG.KC.F4Three
