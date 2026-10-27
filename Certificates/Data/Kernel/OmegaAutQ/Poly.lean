module

public import Init

public section

namespace CFSG.KD.OmegaAutQ

section Poly

variable {G : Type} [Mul G] [One G] [DecidableEq G]

@[expose] def span1P (g : G) (T : List G) : List G := T ++ T.map fun t => g * t

@[expose] def commLP (L : List G) (g : G) : List G := L.filter fun x => decide (x * g = g * x)

@[expose] def firstOutP (Q T : List G) : G := (Q.find? fun x => decide (x ∉ T)).getD 1

@[expose] def conjPairsP (B T : List G) (g : G) : List (G × G) :=
  B.flatMap fun q => (T.filter fun c => decide (c * g = g * q)).map fun c => (q, c)

@[expose] def imgAuxP (Q : List G) (g : G) (hasSq : Bool) (ps : List (G × G)) : List G :=
  Q.filter fun h => (!hasSq || decide (h * h = g * g)) && ps.all fun p => decide (h * p.1 = p.2 * h)

@[expose] def imgCandP (Q B T : List G) (g : G) : List G :=
  imgAuxP Q g (decide (g * g ∈ T)) (conjPairsP B T g)

@[expose] def candsOfP (Q B T : List G) (g1 g2 : G) : List (G × G) :=
  let E := T.filter fun e => decide (e * (g2 * g1) = g1 * g2)
  (imgCandP Q B T g1).flatMap fun h1 =>
    ((imgCandP Q B T g2).filter fun h2 => E.all fun e => decide (h1 * h2 = e * (h2 * h1))).map
      fun h2 => (h1, h2)

@[expose] def leafOfP (Q B T : List G) (g1 g2 : G) : Bool :=
  decide (g1 ∈ Q) && decide (g2 ∈ Q) &&
    (let T5 := span1P g2 (span1P g1 T)
     Q.all fun y => decide (y ∈ T5)) && decide ((candsOfP Q B T g1 g2).length ≤ 8)

@[expose] def leafP (Q B T : List G) : Bool :=
  let g1 := firstOutP Q T
  leafOfP Q B T g1 (firstOutP Q (span1P g1 T))

@[expose] def level2P (Q B T2 Iab : List G) : Bool :=
  Iab.all fun c => decide (c ∈ T2) || leafP Q (B ++ [c]) (span1P c T2)

@[expose] def level1P (Q B T1 Ia : List G) : Bool :=
  Ia.all fun b => decide (b ∈ T1) || level2P Q (B ++ [b]) (span1P b T1) (commLP Ia b)

@[expose] def chainChkP (Q I : List G) : Bool :=
  I.all fun a => level1P Q [a] (span1P a [1]) (commLP I a)

@[expose] def chainPartP (Q I J : List G) : Bool :=
  J.all fun a => level1P Q [a] (span1P a [1]) (commLP I a)

@[expose] def invsOfP (Q : List G) : List G :=
  Q.filter fun x => decide (x * x = 1 ∧ x ≠ 1)

end Poly

@[expose] def laneW (w t i : Nat) : Nat := (t >>> (w * i)) &&& (2 ^ w - 1)

@[expose] noncomputable def allLt (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && f k) m

structure QT (t e : Nat) where
  v : Fin 32

theorem QT.eq_iff {t e : Nat} {a b : QT t e} : a = b ↔ a.v.val = b.v.val := by
  cases a
  cases b
  simp [Fin.ext_iff]

instance {t e : Nat} : DecidableEq (QT t e) := fun a b => decidable_of_iff _ QT.eq_iff.symm

theorem laneW_lt (t i : Nat) : laneW 5 t i < 32 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

instance {t e : Nat} : Mul (QT t e) :=
  ⟨fun a b => ⟨⟨laneW 5 t (32 * a.v.val + b.v.val), laneW_lt t _⟩⟩⟩

instance {t e : Nat} : One (QT t e) := ⟨⟨⟨e % 32, Nat.mod_lt _ (by decide)⟩⟩⟩

@[expose] def lq (t e : Nat) : List (QT t e) :=
  (List.range 32).map fun i => ⟨⟨i % 32, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def imgP (tA tB : Nat → Nat) (k l x : Nat) : Nat := laneW 7 (tA k) (laneW 7 (tB l) x)

@[expose] def pairOf (tP i : Nat) : Nat × Nat := (laneW 6 tP i / 8, laneW 6 tP i % 8)

@[expose] def imgI (tA tB : Nat → Nat) (tP i x : Nat) : Nat :=
  imgP tA tB (pairOf tP i).1 (pairOf tP i).2 x

@[expose] noncomputable def sigNe (tA tB : Nat → Nat) (p q : Nat × Nat) : Bool :=
  !allLt 81 fun x => imgP tA tB p.1 p.2 x == imgP tA tB q.1 q.2 x

@[expose] def pairs64 : List (Nat × Nat) :=
  (List.range 8).flatMap fun k => (List.range 8).map fun l => (k, l)

@[expose] noncomputable def mulChk (tA tB : Nat → Nat) (tP t : Nat) : Bool :=
  allLt 32 fun a => allLt 32 fun b => allLt 81 fun x =>
    imgI tA tB tP a (imgI tA tB tP b x) == imgI tA tB tP (laneW 5 t (32 * a + b)) x

@[expose] noncomputable def oneChk (tA tB : Nat → Nat) (tP e : Nat) : Bool :=
  allLt 81 fun x => imgI tA tB tP e x == x

end CFSG.KD.OmegaAutQ
