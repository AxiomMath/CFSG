module

public import Certificates.Data.Kernel.PackPerm

public section

namespace CFSG.KC.GRing

open CFSG.KC.PackPerm

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def keyOf (d : Nat) (q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.mul d ih)) q

@[expose] noncomputable def keyMap (d : Nat) (f : Nat → Nat) (q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add (f x) (Nat.mul d ih)) q

@[expose] noncomputable def mapPt (f : Nat → Nat) (q : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => f x :: ih) q

@[expose] noncomputable def bitOf (m k : Nat) : Bool := Nat.beq (fld(m, k, 1)) 1

@[expose] noncomputable def lane (V k : Nat) : Nat := fld(V, Nat.mul 16 k, 65535)

@[expose] noncomputable def childOf (P₀ P₁ : Nat) (e : List Nat × Nat) : List Nat :=
  mapPt (pget (nIf(Nat.beq e.2 0, P₀, P₁))) e.1

@[expose] noncomputable def wTup (P₀ P₁ : Nat) (bs w : List Nat) : List Nat :=
  mapPt (wimg P₀ P₁ w) bs

@[expose] noncomputable def fimg (d S : Nat) (fs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun f _ ih => pget S (Nat.add (Nat.mul f d) ih)) fs

@[expose] noncomputable def treeRun (d r P₀ P₁ : Nat) (tree : List (List Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih m => strictB m fun m => strictB (keyOf d (childOf P₀ P₁ e)) fun kc =>
      bAnd(Nat.beq (lenL e.1) r, bAnd(entriesLt d e.1, bAnd(bitOf m (keyOf d e.1),
        bIf(bitOf m kc, false, ih (Nat.lor m (Nat.shiftLeft 1 kc))))))) tree

@[expose] noncomputable def treeCheckP (d : Nat) (l₀ l₁ : List Nat) (P₀ P₁ : Nat) (bs : List Nat)
    (tree : List (List Nat × Nat)) (N : Nat) : Bool :=
  bAnd(Nat.ble d 256, bAnd(tabOk d l₀ P₀, bAnd(tabOk d l₁ P₁, bAnd(entriesLt d bs,
    bAnd(Nat.beq (Nat.succ (lenL tree)) N,
      treeRun d (lenL bs) P₀ P₁ tree (Nat.shiftLeft 1 (keyOf d bs)))))))

@[expose] noncomputable def treeCheck (d : Nat) (l₀ l₁ : List Nat) (bs : List Nat)
    (tree : List (List Nat × Nat)) (N : Nat) : Bool :=
  treeCheckP d l₀ l₁ (pack8 l₀) (pack8 l₁) bs tree N

@[expose] noncomputable def elemRun (d P₀ P₁ S : Nat) (ws : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => strictB k fun k =>
      bAnd(allLt d fun i => Nat.beq (pget S (Nat.add (Nat.mul k d) i)) (wimg P₀ P₁ w i),
        ih (Nat.succ k))) ws

@[expose] noncomputable def invRun (d S n : Nat) (terms : List (List Nat × Nat)) : Bool :=
  allL terms fun t => bAnd(entriesLt n t.1,
    allLt d fun i => Nat.beq (pget t.2 (fimg d S t.1 i)) i)

@[expose] noncomputable def tabsCheckP (d : Nat) (l₀ l₁ : List Nat) (P₀ P₁ : Nat)
    (ws : List (List Nat)) (S : Nat) (terms : List (List Nat × Nat)) : Bool :=
  bAnd(Nat.ble d 256, bAnd(tabOk d l₀ P₀, bAnd(tabOk d l₁ P₁,
    bAnd(elemRun d P₀ P₁ S ws 0, invRun d S (lenL ws) terms))))

@[expose] noncomputable def tabsCheck (d : Nat) (l₀ l₁ : List Nat) (ws : List (List Nat)) (S : Nat)
    (terms : List (List Nat × Nat)) : Bool :=
  tabsCheckP d l₀ l₁ (pack8 l₀) (pack8 l₁) ws S terms

@[expose] noncomputable def laneIs (V k : Nat) (c : Nat × Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq (lane V k) (Nat.add 32768 c.1))
    (Nat.beq (Nat.add (lane V k) c.1) 32768) c.2

@[expose] noncomputable def dflt (d V vm : Nat) (q : List Nat) : Bool :=
  strictB (keyOf d q) fun k => bIf(bitOf vm k, true, Nat.beq (lane V k) 32768)

@[expose] noncomputable def vRun (d P₀ P₁ V : Nat) (bs : List Nat) (vt : List (List Nat × (Nat × Bool)))
    (k : Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) k
    (fun t _ ih m => strictB m fun m => strictB (keyOf d (wTup P₀ P₁ bs t.1)) fun kt =>
      bIf(bitOf m kt, false, bAnd(laneIs V kt t.2, ih (Nat.lor m (Nat.shiftLeft 1 kt))))) vt

@[expose] noncomputable def vCheckP (d : Nat) (l₀ l₁ : List Nat) (P₀ P₁ : Nat) (bs : List Nat)
    (vt : List (List Nat × (Nat × Bool))) (V : Nat) (tree : List (List Nat × Nat)) : Bool :=
  bAnd(Nat.ble d 256, bAnd(tabOk d l₀ P₀, bAnd(tabOk d l₁ P₁,
    vRun d P₀ P₁ V bs vt (fun vm => bAnd(dflt d V vm bs,
      allL tree fun e => dflt d V vm (childOf P₀ P₁ e))) 0)))

@[expose] noncomputable def vCheck (d : Nat) (l₀ l₁ : List Nat) (bs : List Nat)
    (vt : List (List Nat × (Nat × Bool))) (V : Nat) (tree : List (List Nat × Nat)) : Bool :=
  vCheckP d l₀ l₁ (pack8 l₀) (pack8 l₁) bs vt V tree

@[expose] noncomputable def gKeys (d P₀ P₁ : Nat) (bs : List Nat) (gm : List (List Nat × (Nat × Bool))) :
    List (Nat × (Nat × Bool)) :=
  List.rec (motive := fun _ => List (Nat × (Nat × Bool))) []
    (fun g _ ih => (keyOf d (wTup P₀ P₁ bs g.1), g.2) :: ih) gm

@[expose] noncomputable def gSum (gk : List (Nat × (Nat × Bool))) (k : Nat) (s : Bool) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun g _ ih => Nat.add (nIf(Nat.beq g.1 k, nIf(Bool.rec (motive := fun _ => Bool) (!s) s g.2.2,
      g.2.1, 0), 0)) ih) gk

@[expose] noncomputable def tSum (d V : Nat) (terms : List (List Nat × Nat)) (q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun t _ ih => Nat.add (lane V (keyMap d (pget t.2) q)) ih) terms

@[expose] noncomputable def sumAt (d V : Nat) (terms : List (List Nat × Nat))
    (gk : List (Nat × (Nat × Bool))) (q : List Nat) : Bool :=
  strictB (keyOf d q) fun k =>
    Nat.beq (Nat.add (tSum d V terms q) (gSum gk k true))
      (Nat.add (Nat.mul 32768 (lenL terms)) (gSum gk k false))

@[expose] noncomputable def sumChunkP (d P₀ P₁ V : Nat) (terms : List (List Nat × Nat))
    (gk : List (Nat × (Nat × Bool))) (es : List (List Nat × Nat)) : Bool :=
  allL es fun e => sumAt d V terms gk (childOf P₀ P₁ e)

@[expose] noncomputable def sumChunk (d : Nat) (l₀ l₁ : List Nat) (V : Nat)
    (terms : List (List Nat × Nat)) (gm : List (List Nat × (Nat × Bool))) (bs : List Nat)
    (es : List (List Nat × Nat)) : Bool :=
  sumChunkP d (pack8 l₀) (pack8 l₁) V terms (gKeys d (pack8 l₀) (pack8 l₁) bs gm) es

@[expose] noncomputable def sumRoot (d : Nat) (l₀ l₁ : List Nat) (V : Nat)
    (terms : List (List Nat × Nat)) (gm : List (List Nat × (Nat × Bool))) (bs : List Nat) : Bool :=
  sumAt d V terms (gKeys d (pack8 l₀) (pack8 l₁) bs gm) bs

@[expose] noncomputable def xorRun (d S : Nat) (bs : List Nat) (terms : List (List Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun m => Nat.beq m 0)
    (fun fs _ ih m => strictB m fun m =>
      ih (Nat.xor m (Nat.shiftLeft 1 (keyOf d (mapPt (fimg d S fs) bs))))) terms

@[expose] noncomputable def xorCheckP (d : Nat) (l₀ l₁ : List Nat) (P₀ P₁ : Nat)
    (ws : List (List Nat)) (S : Nat) (bs : List Nat) (terms : List (List Nat)) : Bool :=
  bAnd(Nat.ble d 256, bAnd(tabOk d l₀ P₀, bAnd(tabOk d l₁ P₁, bAnd(elemRun d P₀ P₁ S ws 0,
    bAnd(allL terms (entriesLt (lenL ws)), xorRun d S bs terms 0)))))

@[expose] noncomputable def xorCheck (d : Nat) (l₀ l₁ : List Nat) (ws : List (List Nat)) (S : Nat)
    (bs : List Nat) (terms : List (List Nat)) : Bool :=
  xorCheckP d l₀ l₁ (pack8 l₀) (pack8 l₁) ws S bs terms

end CFSG.KC.GRing

end
