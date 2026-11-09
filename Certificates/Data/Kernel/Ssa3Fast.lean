module

public import Certificates.Data.Kernel.Ssa3Free

public section

namespace CFSG.KC.Ssa3F

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.Ssa3

@[expose] def blocksF : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | f + 1, l => l.take 32 :: blocksF f (l.drop 32)

@[expose] def fget (l : List Nat) (i d : Nat) : Nat :=
  ((blocksF (l.length / 32 + 1) l).getD (i / 32) []).getD (i % 32) d

theorem blocksF_get? : ∀ (f : Nat) (l : List Nat) (q : Nat),
    (blocksF f l)[q]? = if q < f then some ((l.drop (32 * q)).take 32) else none
  | 0, _, _ => by simp [blocksF]
  | f + 1, l, 0 => by simp [blocksF]
  | f + 1, l, q + 1 => by
    simp only [blocksF, List.getElem?_cons_succ, blocksF_get? f (l.drop 32) q, List.drop_drop]
    have h1 : 32 + 32 * q = 32 * (q + 1) := by omega
    rw [h1]
    by_cases h : q < f
    · simp [h, show q + 1 < f + 1 by omega]
    · simp [h, show ¬ q + 1 < f + 1 by omega]

theorem fget_eq (l : List Nat) (i d : Nat) : fget l i d = l.getD i d := by
  unfold fget
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    blocksF_get?]
  by_cases h : i / 32 < l.length / 32 + 1
  · simp only [h, ↓reduceIte, Option.getD_some]
    rw [List.getElem?_take]
    simp only [Nat.mod_lt i (show 32 > 0 by omega), ↓reduceIte]
    rw [List.getElem?_drop, Nat.div_add_mod]
  · simp only [h, ↓reduceIte]
    have h2 : l.length ≤ i := by
      have := Nat.div_add_mod i 32
      have := Nat.div_add_mod l.length 32
      have := Nat.mod_lt l.length (show 32 > 0 by omega)
      omega
    simp [List.getElem?_eq_none h2]

structure Lk where
  nk : Nat → Nat → Nat
  na : Nat → Nat → Nat
  nb : Nat → Nat → Nat
  fv : Nat → Nat → Nat
  qk : Nat → Nat → Nat
  qx : Nat → Nat → Nat
  qy : Nat → Nat → Nat
  qt : Nat → Nat → Nat
  qf : Nat → Nat → Nat

@[expose] def lkS (D : SData) : Lk :=
  ⟨D.nk.getD, D.na.getD, D.nb.getD, D.fv.getD, D.qk.getD, D.qx.getD, D.qy.getD, D.qt.getD,
    D.qf.getD⟩

@[expose] def lkF (D : SData) : Lk :=
  ⟨fget D.nk, fget D.na, fget D.nb, fget D.fv, fget D.qk, fget D.qx, fget D.qy, fget D.qt,
    fget D.qf⟩

theorem lkF_eq (D : SData) : lkF D = lkS D := by
  unfold lkF lkS
  simp only [show fget D.nk = D.nk.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.na = D.na.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.nb = D.nb.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.fv = D.fv.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.qk = D.qk.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.qx = D.qx.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.qy = D.qy.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.qt = D.qt.getD from funext fun i => funext fun d => fget_eq _ i d,
    show fget D.qf = D.qf.getD from funext fun i => funext fun d => fget_eq _ i d]

@[expose] def pidL (K : Lk) (y e x : Nat) : Bool :=
  bif Nat.beq e 0 then Nat.beq x 2 else bif Nat.beq e 1 then Nat.beq x y else
    Nat.ble 3 x && Nat.beq (K.nk (x - 3) 1) e && Nat.beq (K.na (x - 3) 0) y

@[expose] def mulL (K : Lk) (y z x : Nat) : Bool :=
  Nat.ble 3 x && Nat.beq (K.nk (x - 3) 1) 0 && Nat.beq (K.na (x - 3) 0) y &&
    Nat.beq (K.nb (x - 3) 0) z

@[expose] def progL (K : Lk) (fv : List Nat) : List Op → List Nat → List Nat → Bool
  | [], [], V => V == fv
  | .mul i j k :: p, x :: xs, V =>
    mulL K (V.getD i 0) (V.getD j 0) x && progL K fv p xs (V.set k x)
  | .pow e i k :: p, x :: xs, V => pidL K (V.getD i 0) e x && progL K fv p xs (V.set k x)
  | _, _, _ => false

@[expose] def widL (K : Lk) : Word → Nat → Bool
  | [], x => Nat.beq x 2
  | [(r, e)], x => pidL K (K.fv r 0) e x
  | (r, e) :: w, x => mulL K (K.na (x - 3) 0) (K.nb (x - 3) 0) x &&
      pidL K (K.fv r 0) e (K.na (x - 3) 0) && widL K w (K.nb (x - 3) 0)

@[expose] def factL (K : Lk) (n : Nat) (q : Nat) : MFact → Bool
  | .ord r e => Nat.beq (K.qk q 1) 0 && Nat.blt r n && Nat.blt 0 e &&
      pidL K (K.fv r 0) e (K.qx q 0) && Nat.beq (K.qy q 0) 2
  | .conj h u w => Nat.beq (K.qk q 1) 0 && Nat.blt h n && wordLt n u && wordLt n w &&
      mulL K (K.fv h 0) (K.nb (K.qx q 0 - 3) 0) (K.qx q 0) &&
      widL K u (K.nb (K.qx q 0 - 3) 0) &&
      mulL K (K.na (K.qy q 0 - 3) 0) (K.fv h 0) (K.qy q 0) &&
      widL K w (K.na (K.qy q 0 - 3) 0)
  | .ne w₁ w₂ t => !Nat.beq (K.qk q 0) 0 && wordLt n w₁ && wordLt n w₂ &&
      Nat.beq (K.qt q 0) t && widL K w₁ (K.qx q 0) && widL K w₂ (K.qy q 0)
  | .eq w₁ w₂ => Nat.beq (K.qk q 1) 0 && wordLt n w₁ && wordLt n w₂ &&
      widL K w₁ (K.qx q 0) && widL K w₂ (K.qy q 0)

@[expose] def cmpsL (K : Lk) (len n : Nat) (facts : List MFact) : Bool :=
  (List.range len).all fun q =>
    Nat.blt (K.qf q 0) facts.length && factL K n q (facts.getD (K.qf q 0) (.eq [] []))

theorem pidS_eq (D : SData) (y e x : Nat) : pidS D y e x = pidL (lkS D) y e x := rfl

theorem mulS_eq (D : SData) (y z x : Nat) : mulS D y z x = mulL (lkS D) y z x := rfl

theorem progS_eq (D : SData) :
    ∀ (p : List Op) (xs V : List Nat), progS D p xs V = progL (lkS D) D.fv p xs V
  | [], [], _ => by simp [progS, progL]
  | [], _ :: _, _ => by simp [progS, progL]
  | .mul i j k :: p, [], V => by simp [progS, progL]
  | .pow e i k :: p, [], V => by simp [progS, progL]
  | .mul i j k :: p, x :: xs, V => by
    simp only [progS, progL, mulS_eq, progS_eq D p xs]
  | .pow e i k :: p, x :: xs, V => by
    simp only [progS, progL, pidS_eq, progS_eq D p xs]

theorem widS_eq (D : SData) : ∀ (w : Word) (x : Nat), widS D w x = widL (lkS D) w x
  | [], _ => by simp [widS, widL]
  | [(r, e)], x => by simp only [widS, widL, pidS_eq]; rfl
  | (r, e) :: a :: w, x => by
    simp only [widS, widL, pidS_eq, mulS_eq, widS_eq D (a :: w)]; rfl

theorem factS_eq (D : SData) (n q : Nat) : ∀ f : MFact, factS D n q f = factL (lkS D) n q f
  | .ord r e => by simp only [factS, factL, pidS_eq]; rfl
  | .conj h u w => by simp only [factS, factL, mulS_eq, widS_eq]; rfl
  | .ne w₁ w₂ t => by simp only [factS, factL, widS_eq]; rfl
  | .eq w₁ w₂ => by simp only [factS, factL, widS_eq]; rfl

theorem cmpsS_eq (D : SData) (n : Nat) (facts : List MFact) :
    cmpsS D n facts = cmpsL (lkF D) D.qk.length n facts := by
  rw [lkF_eq]
  unfold cmpsS cmpsL
  simp only [factS_eq]
  rfl

theorem ssaOK_eq (D : SData) (prog : List Op) (n : Nat) :
    ssaOK D prog n = (Nat.ble 2 n && prog.all (Op.lt n) && structS D &&
      progL (lkF D) D.fv prog D.opn ((List.range n).map fun r => Nat.min r 2)) := by
  rw [lkF_eq]
  unfold ssaOK
  rw [progS_eq]

@[expose] def exSL (K : Lk) (C : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, x => [(x, 1)]
  | f + 1, x =>
    bif Nat.blt x 2 || memS x C then [(x, 1)] else bif Nat.beq x 2 then [] else
    bif Nat.blt (K.na (x - 3) 0) x && Nat.blt (K.nb (x - 3) 0) x then
      bif Nat.beq (K.nk (x - 3) 1) 0 then
        exSL K C f (K.na (x - 3) 0) ++ exSL K C f (K.nb (x - 3) 0)
      else powL (K.nk (x - 3) 1) (exSL K C f (K.na (x - 3) 0))
    else []

@[expose] def wexSL (K : Lk) (C : List Nat) (f : Nat) : Word → List (Nat × Nat)
  | [] => []
  | (r, e) :: w => powL e (exSL K C f (K.fv r 0)) ++ wexSL K C f w

@[expose] def freeSL (K : Lk) (f : Nat) (w₁ w₂ : Word) : Bool :=
  eqL (mergeS (wexSL K (w₂.map fun p => K.fv p.1 0) f w₁))
    (mergeS (wexSL K (w₂.map fun p => K.fv p.1 0) f w₂))

@[expose] def freeFSL (K : Lk) (n f : Nat) : MFact → Bool
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && freeSL K f w₁ w₂
  | _ => false

@[expose] def coverSL (K : Lk) (len n f : Nat) (facts : List MFact) : Bool :=
  (List.range facts.length).all fun i =>
    (List.range len).any (fun q => Nat.beq (K.qf q 0) i) ||
      freeFSL K n f (facts.getD i (.eq [] []))

theorem exS_eq (D : SData) (C : List Nat) : ∀ (f x : Nat), exS D C f x = exSL (lkS D) C f x
  | 0, _ => rfl
  | f + 1, x => by simp only [exS, exSL, exS_eq D C f]; rfl

theorem wexS_eq (D : SData) (C : List Nat) (f : Nat) :
    ∀ w : Word, wexS D C f w = wexSL (lkS D) C f w
  | [] => rfl
  | (r, e) :: w => by simp only [wexS, wexSL, exS_eq, wexS_eq D C f w]; rfl

theorem freeF_eq (D : SData) (n f : Nat) : ∀ m : MFact, freeF D n f m = freeFSL (lkS D) n f m
  | .eq w₁ w₂ => by simp only [freeF, freeFSL, freeS, freeSL, wexS_eq]; rfl
  | .ord _ _ => rfl
  | .conj _ _ _ => rfl
  | .ne _ _ _ => rfl

theorem coverS_eq (D : SData) (n f : Nat) (facts : List MFact) :
    coverS D n f facts = coverSL (lkF D) D.qk.length n f facts := by
  rw [lkF_eq]
  unfold coverS coverSL
  simp only [freeF_eq]
  rfl

end CFSG.KC.Ssa3F

end
