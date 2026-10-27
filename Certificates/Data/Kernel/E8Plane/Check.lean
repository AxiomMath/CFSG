module

public import Certificates.Data.Kernel.E7Plane.Check

public section

namespace CFSG.KC.E8Plane

open CFSG.KC.E7Plane

@[expose] noncomputable def allL {α : Type} (L : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def anyL {α : Type} (L : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) L

@[expose] noncomputable def allIL {α : Type} (L : List α) (f : Nat → α → Bool) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => letB i fun i => andB (f i x) (ih (Nat.succ i))) L s

@[expose] noncomputable def memL (L : List Nat) (x : Nat) : Bool := anyL L fun y => Nat.beq y x

@[expose] noncomputable def nthL {α : Type} (L : List α) (d : α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih j => Nat.rec (motive := fun _ => α) x (fun k _ => ih k) j) L i

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (f i)) n

@[expose] noncomputable def pk (w : Nat) (L : List Nat) : Nat := packL w (fun x => x) L

@[expose] noncomputable def bitsL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun b _ ih => Nat.lor ih (Nat.shiftLeft 1 b)) L

@[expose] noncomputable def incL (L : List Nat) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => andB (Nat.ble p x) (ih (Nat.succ x))) L s

@[expose] noncomputable def cntP (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.lor ih (Nat.shiftLeft (Nat.mod x 256) (Nat.mul 8 (Nat.div x 256)))) L

@[expose] noncomputable def pc (X : Nat) : Nat := sumN 240 fun k => toN (Nat.testBit X k)

@[expose] noncomputable def tb (T i k : Nat) : Nat := fld T 8 (Nat.add (Nat.mul 8 k) i)

@[expose] noncomputable def actW (T : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun i _ ih => letN ih fun y => tb T i y) w

@[expose] noncomputable def permP (T : Nat) (w : List Nat) : Nat := orN 240 8 fun k => actW T w k

@[expose] noncomputable def cl (c j : Nat) : Nat := fld c 4 j

@[expose] noncomputable def gramC (a b : Nat) : Nat :=
  Nat.sub
    (Nat.add (Nat.add (Nat.mul 2 (sumN 8 fun i => Nat.mul (cl a i) (cl b i)))
      (Nat.mul 8 (Nat.add (cl a 3) (cl b 3)))) 130)
    (Nat.add
      (Nat.add (Nat.add (Nat.mul (cl a 0) (cl b 2)) (Nat.mul (cl a 2) (cl b 0)))
       (Nat.add (Nat.add (Nat.mul (cl a 1) (cl b 3)) (Nat.mul (cl a 3) (cl b 1)))
        (sumN 5 fun i => Nat.add (Nat.mul (cl a (i + 2)) (cl b (i + 3)))
          (Nat.mul (cl a (i + 3)) (cl b (i + 2))))))
      (Nat.mul 8 (Nat.add (Nat.add (Nat.add (cl a 0) (cl a 1)) (cl a 7))
        (Nat.add (Nat.add (cl b 0) (cl b 1)) (cl b 7)))))

@[expose] noncomputable def gram (RP a b : Nat) : Nat := gramC (fld RP 32 a) (fld RP 32 b)

@[expose] noncomputable def bstep (SP t k p : Nat) : Nat :=
  letN p fun p => Bool.rec (motive := fun _ => Nat) p (Nat.add p k)
    (andB (Nat.blt (Nat.add p k) 240) (Nat.ble (fld SP 32 (Nat.add p k)) t))

@[expose] noncomputable def bpos (SP t : Nat) : Nat :=
  bstep SP t 1 (bstep SP t 2 (bstep SP t 4 (bstep SP t 8 (bstep SP t 16 (bstep SP t 32
    (bstep SP t 64 (bstep SP t 128 0)))))))

@[expose] noncomputable def rtF (RP SP IP b x : Nat) : Nat :=
  letN (fld RP 32 x) fun cx => letN (fld RP 32 b) fun cb => letN (gramC cx cb) fun g =>
    fld IP 8 (bpos SP (Nat.sub (Nat.add (Nat.add cx (Nat.mul (Nat.sub 2 g) cb))
      (Nat.mul (Nat.sub g 2) 2290649224)) (Nat.add (Nat.mul (Nat.sub g 2) cb)
        (Nat.mul (Nat.sub 2 g) 2290649224))))

@[expose] noncomputable def actR (RP SP IP : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun b _ ih => letN ih fun y => rtF RP SP IP b y) w

@[expose] noncomputable def wordsB (RP SP IP P : Nat) (WS : List (List Nat)) : Bool :=
  allL WS fun w => andB (allL w fun b => Nat.blt b 240) (allN 8 fun j =>
    Nat.beq (actR RP SP IP w j) (fld P 8 j))

@[expose] noncomputable def dg (n i : Nat) : Nat := Nat.mod (Nat.div n (Nat.pow 3 i)) 3

@[expose] noncomputable def chv (n c : Nat) : Nat :=
  Nat.mod (sumN 8 fun i => Nat.mul (dg n i) (Nat.add (cl c i) 1)) 3

@[expose] noncomputable def fixB (RP P n : Nat) : Bool :=
  allN 8 fun j => Nat.beq (chv n (fld RP 32 (fld P 8 j))) (dg n j)

@[expose] noncomputable def fixM (RP P : Nat) : Nat := orN 6561 1 fun n => toN (fixB RP P n)

@[expose] noncomputable def nkM (RP b : Nat) : Nat :=
  letN (fld RP 32 b) fun c => orN 6561 1 fun n => toN (notB (Nat.beq (chv n c) 0))

@[expose] noncomputable def kmN (RP n : Nat) : Nat :=
  orN 240 1 fun k => toN (Nat.beq (chv n (fld RP 32 k)) 0)

@[expose] noncomputable def combo (n₀ n₁ c₀ c₁ : Nat) : Nat :=
  sumN 8 fun j => Nat.mul (Nat.mod (Nat.add (Nat.mul c₀ (dg n₀ j)) (Nat.mul c₁ (dg n₁ j))) 3)
    (Nat.pow 3 j)

@[expose] noncomputable def k78 (CP n₀ n₁ : Nat) : Bool :=
  allN 8 fun c => Nat.beq (fld CP 8 (combo n₀ n₁ (Nat.mod (Nat.add c 1) 3)
    (Nat.div (Nat.add c 1) 3))) 78

@[expose] noncomputable def kmL (RP : Nat) (FL : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) [] (fun n _ ih => (n, kmN RP n) :: ih) FL

@[expose] noncomputable def wmL (WS : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => bitsL w :: ih) WS

@[expose] noncomputable def sigL (σ : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun k acc =>
    Bool.rec (motive := fun _ => List Nat) acc (List.cons (Nat.sub 239 k) acc)
      (Nat.testBit σ (Nat.sub 239 k))) 240

@[expose] noncomputable def hd (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x) L

@[expose] noncomputable def nz (RP a b : Nat) : Bool := notB (Nat.beq (gram RP a b) 2)

@[expose] noncomputable def blk (RP g₀ g₁ a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 2 1 (nz RP a g₁)) 0
    (nz RP a g₀)

@[expose] noncomputable def d2B (RP P σ : Nat) : Bool :=
  letB (hd (sigL σ)) fun g₀ => letB (fld P 8 g₀) fun g₁ => letB (fld P 8 g₁) fun g₂ =>
  andB (Nat.testBit σ g₀) (andB (Nat.testBit σ g₁) (andB (Nat.testBit σ g₂)
  (andB (allL (sigL σ) fun a => Nat.beq (Nat.add (Nat.add (toN (nz RP a g₀)) (toN (nz RP a g₁)))
      (toN (nz RP a g₂))) 1)
  (andB (allL (sigL σ) fun a => allL (sigL σ) fun b =>
      andB (Bool.rec (motive := fun _ => Bool)
        (notB (Nat.beq (blk RP g₀ g₁ a) (blk RP g₀ g₁ b)))
        (Nat.beq (blk RP g₀ g₁ a) (blk RP g₀ g₁ b)) (nz RP a b)) (Nat.ble (gram RP a b) 4))
    (nz RP (fld P 8 g₂) g₀)))))

@[expose] noncomputable def orthB (RP P d : Nat) : Bool :=
  letB (fld P 8 d) fun d₁ => letB (fld P 8 d₁) fun d₂ =>
    andB (Nat.beq (gram RP d d₁) 2) (andB (Nat.beq (gram RP d d₂) 2) (Nat.beq (gram RP d₁ d₂) 2))

@[expose] noncomputable def d3B (RP P σ : Nat) : Bool :=
  andB (Nat.beq (lenL (sigL σ)) 24) (andB (allL (sigL σ) fun g =>
      orB (Nat.beq (fld P 8 g) g) (Nat.beq (gram RP g (fld P 8 g)) 2))
    (anyL (sigL σ) fun d => orthB RP P d))

@[expose] noncomputable def tripL (RP P σ : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun d _ ih =>
    Bool.rec (motive := fun _ => List Nat) ih (List.cons d ih) (orthB RP P d)) (sigL σ)

@[expose] noncomputable def trF (RP SP IP P δ x : Nat) : Nat :=
  letN (fld P 8 δ) fun δ₁ => letN (fld P 8 δ₁) fun δ₂ =>
    rtF RP SP IP δ (rtF RP SP IP δ₁ (rtF RP SP IP δ₂ x))

@[expose] noncomputable def inTgt (P d x : Nat) : Bool :=
  orB (Nat.beq x d) (orB (Nat.beq x (fld P 8 d)) (Nat.beq x (fld P 8 (fld P 8 d))))

@[expose] noncomputable def inT (RP P σ δ : Nat) : Bool := andB (Nat.testBit σ δ) (orthB RP P δ)

@[expose] noncomputable def witB (RP SP IP P σ d β c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (letB (Nat.sub (Nat.div c 256) 1) fun δ₁ => letB (Nat.sub (Nat.mod c 256) 1) fun δ₂ =>
        andB (inT RP P σ δ₁) (andB (inT RP P σ δ₂)
          (inTgt P d (trF RP SP IP P δ₁ (trF RP SP IP P δ₂ β)))))
      (andB (inT RP P σ (Nat.sub c 1)) (inTgt P d (trF RP SP IP P (Nat.sub c 1) β)))
      (Nat.blt c 256))
    (inTgt P d β) (Nat.beq c 0)

@[expose] noncomputable def d3tB (RP SP IP P σ : Nat) (ws : List Nat) : Bool :=
  letB (pk 16 ws) fun WP => letB (lenL (tripL RP P σ)) fun m =>
  allIL (tripL RP P σ) (fun i d => allIL (tripL RP P σ) (fun j β =>
    witB RP SP IP P σ d β (fld WP 16 (Nat.add (Nat.mul i m) j))) 0) 0

@[expose] noncomputable def qB (T : Nat) (QW RW : List (List Nat))
    (CJ : List (Nat × Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × List Nat) → Nat → Bool) (fun _ _ => true)
    (fun v _ ih cj c => List.rec (motive := fun _ => Bool) false (fun x rest _ =>
      andB (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (andB (Nat.beq x.1 2) (allN 8 fun j => Nat.beq (actW T v (actW T x.2.2 j))
            (actW T x.2.2 (actW T (nthL RW [] x.2.1) j))))
          (andB (Nat.blt x.2.1 8)
            (notB (Nat.beq (actW T v (actW T v (actW T v x.2.1))) x.2.1)))
          (Nat.beq x.1 1))
        (Nat.beq c 0) (Nat.beq x.1 0))
      (ih rest (Nat.succ c))) cj) QW CJ 0

@[expose] noncomputable def easyB (RP SP IP P FM : Nat) (WS : List (List Nat)) : Bool :=
  andB (Nat.beq (fixM RP P) FM) (andB (wordsB RP SP IP P WS)
    (allL WS fun w => allL w fun b => Nat.beq (Nat.land FM (nkM RP b)) 0))

@[expose] noncomputable def fixB' (RP SP IP P FM : Nat) (FL : List Nat) (WS : List (List Nat)) :
    Bool :=
  andB (Nat.beq (fixM RP P) FM) (andB (Nat.beq (bitsL FL) FM) (andB (incL FL 0)
    (wordsB RP SP IP P WS)))

@[expose] noncomputable def pairsB (RP : Nat) (FL FC : List Nat) (WS : List (List Nat))
    (D2 D3 : List Nat) : Bool :=
  letB (cntP FC) fun CP =>
  andB (allL FC fun x => Nat.beq (pc (kmN RP (Nat.div x 256))) (Nat.mod x 256))
  (allL (kmL RP FL) fun x => allL (kmL RP FL) fun y =>
    letB (Nat.land x.2 y.2) fun σ =>
      orB (anyL (wmL WS) fun m => Nat.beq (Nat.land σ m) m) (orB (memL D2 σ)
        (andB (k78 CP x.1 y.1) (memL D3 σ))))

@[expose] noncomputable def fstL (L : List (Nat × List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => x.1 :: ih) L

@[expose] noncomputable def excB (RP SP IP P : Nat) (D2 : List Nat) (D3 : List (Nat × List Nat)) :
    Bool :=
  andB (allL D2 (d2B RP P))
    (allL D3 fun x => andB (d3B RP P x.1) (d3tB RP SP IP P x.1 x.2))

@[expose] noncomputable def rep3B (RP SP IP P FM : Nat) (FL FC : List Nat) (WS : List (List Nat))
    (D2 : List Nat) (D3 : List (Nat × List Nat)) : Bool :=
  andB (fixB' RP SP IP P FM FL WS) (andB (pairsB RP FL FC WS D2 (fstL D3)) (excB RP SP IP P D2 D3))

@[expose] noncomputable def rep4B (RP SP IP P FM : Nat) (FL : List Nat) (WS : List (List Nat)) :
    Bool :=
  andB (fixB' RP SP IP P FM FL WS)
  (andB (allL FL fun n => letB (kmN RP n) fun K => andB (orB (Nat.beq n 0) (Nat.beq (pc K) 78))
      (anyL (wmL WS) fun m => Nat.beq (Nat.land K m) m))
    (andB (allN 240 fun r => notB (Nat.beq (fld P 8 r) r))
      (Nat.beq (sumN 8 fun j => cl (fld RP 32 (fld P 8 j)) j) 60)))

end CFSG.KC.E8Plane
