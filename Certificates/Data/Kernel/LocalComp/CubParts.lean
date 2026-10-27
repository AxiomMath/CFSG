module

public import Certificates.Data.Kernel.LocalComp.ElemParts
public import Certificates.Data.Kernel.LocalComp.Replay
public import Certificates.Data.CFSGNative.Filter.Sec2

public section

namespace CFSG.SectionRank.Native

@[expose] def CubData.asData (D : CubData) : Data :=
  { seedA := D.seedA, seedB := D.seedB, nregs := D.nregs, prog := D.prog,
    outs := [D.rx, D.ry, D.rh], tests := [D.t] }

@[expose] def SecData.asData (D : SecData) : Data :=
  { seedA := D.seedA, seedB := D.seedB, nregs := D.nregs, prog := D.prog,
    outs := D.outs ++ [D.tReg], tests := D.tests }

@[expose] def CubData.extOps (D : CubData) : List Op :=
  let n := D.nregs
  let Z := n + 7
  [.pow D.r D.rx n, .pow D.r D.ry (n + 1), .pow D.oh D.rh (n + 2),
    .mul D.rx D.ry (n + 3), .pow (D.r - 1) D.rx (n + 4), .pow (D.r - 1) D.ry (n + 5),
    .mul (n + 3) (n + 4) (n + 6), .mul (n + 6) (n + 5) Z,
    .mul Z D.rx (n + 8), .mul D.rx Z (n + 9), .mul Z D.ry (n + 10), .mul D.ry Z (n + 11),
    .mul D.rh D.rx (n + 12), .pow D.a D.rx (n + 13), .pow D.b D.ry (n + 14), .pow D.k Z (n + 15),
    .mul (n + 13) (n + 14) (n + 16), .mul (n + 16) (n + 15) (n + 17), .mul (n + 17) D.rh (n + 18),
    .mul D.rh D.ry (n + 19), .pow D.c D.rx (n + 20), .pow D.d D.ry (n + 21), .pow D.l Z (n + 22),
    .mul (n + 20) (n + 21) (n + 23), .mul (n + 23) (n + 22) (n + 24), .mul (n + 24) D.rh (n + 25),
    .mul D.rh Z (n + 26), .pow D.μ Z (n + 27), .mul (n + 27) D.rh (n + 28)]

@[expose] def SecData.extOps (D : SecData) : List Op :=
  let n := D.nregs
  let o := D.outs.toArray
  let r := o.size
  let T := D.tReg
  let B := n + 1 + 3 * r
  [.mul T T n] ++
    ((List.range r).flatMap fun i =>
      [.mul o[i]! T (n + 1 + 3 * i), .mul T o[i]! (n + 2 + 3 * i), .mul o[i]! o[i]! (n + 3 + 3 * i)]) ++
    ((List.range r).flatMap fun i => ((List.range r).filter (i < ·)).flatMap fun j =>
      let q := B + 3 * (r * i + j)
      [.mul o[i]! o[j]! q, .mul o[j]! o[i]! (q + 1), .mul T (q + 1) (q + 2)])

@[expose] def CubData.extData (D : CubData) : Data :=
  { D.asData with nregs := D.nregs + 29, prog := D.prog ++ D.extOps }

@[expose] def SecData.extData (D : SecData) : Data :=
  { D.asData with
    nregs := D.nregs + 1 + 3 * D.outs.length + 3 * D.outs.length * D.outs.length,
    prog := D.prog ++ D.extOps }

end CFSG.SectionRank.Native

namespace CFSG.KC.LocalComp.CubParts

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KC.LocalComp.ElemParts CFSG.KC.LocalComp.Replay

@[expose] noncomputable def powIs (P : Nat → Nat) (N a t e : Nat) : Bool :=
  andB (Nat.blt t N) (andB (Nat.blt e expoFail) (Nat.beq (expoK P a (nat_lit 64) t) e))

@[expose] noncomputable def cubPartsOK (c : Lay) (V P : Nat → Nat) (N ix iy ih : Nat)
    (I : Nat → Nat) (r oh a b cc dd k l μ t : Nat) : Bool :=
  andB (Nat.ble N (nat_lit 1048576)) (andB (Nat.blt ix N) (andB (Nat.blt iy N) (andB (Nat.blt ih N)
  (andB (Nat.blt (nat_lit 0) r) (andB (Nat.blt (nat_lit 0) oh) (andB (Nat.blt t c.d)
  (andB (powIs P N ix (I 0) r) (andB (Nat.beq (V (I 0)) c.ONE)
  (andB (powIs P N iy (I 1) r) (andB (Nat.beq (V (I 1)) c.ONE)
  (andB (powIs P N ih (I 2) oh) (andB (Nat.beq (V (I 2)) c.ONE)
  (andB (stepIs P N (I 3) ix iy) (andB (powIs P N ix (I 4) (Nat.sub r 1))
  (andB (powIs P N iy (I 5) (Nat.sub r 1)) (andB (stepIs P N (I 6) (I 3) (I 4))
  (andB (stepIs P N (I 7) (I 6) (I 5))
  (andB (notB (Nat.beq (c.vec (c.unit t) (V (I 7))) (c.unit t)))
  (andB (stepIs P N (I 8) (I 7) ix) (andB (stepIs P N (I 9) ix (I 7))
  (andB (Nat.beq (V (I 8)) (V (I 9)))
  (andB (stepIs P N (I 10) (I 7) iy) (andB (stepIs P N (I 11) iy (I 7))
  (andB (Nat.beq (V (I 10)) (V (I 11)))
  (andB (stepIs P N (I 12) ih ix) (andB (powIs P N ix (I 13) a) (andB (powIs P N iy (I 14) b)
  (andB (powIs P N (I 7) (I 15) k) (andB (stepIs P N (I 16) (I 13) (I 14))
  (andB (stepIs P N (I 17) (I 16) (I 15)) (andB (stepIs P N (I 18) (I 17) ih)
  (andB (Nat.beq (V (I 12)) (V (I 18)))
  (andB (stepIs P N (I 19) ih iy) (andB (powIs P N ix (I 20) cc) (andB (powIs P N iy (I 21) dd)
  (andB (powIs P N (I 7) (I 22) l) (andB (stepIs P N (I 23) (I 20) (I 21))
  (andB (stepIs P N (I 24) (I 23) (I 22)) (andB (stepIs P N (I 25) (I 24) ih)
  (andB (Nat.beq (V (I 19)) (V (I 25)))
  (andB (stepIs P N (I 26) ih (I 7)) (andB (powIs P N (I 7) (I 27) μ)
  (andB (stepIs P N (I 28) (I 27) ih)
    (Nat.beq (V (I 26)) (V (I 28))))))))))))))))))))))))))))))))))))))))))))))

@[expose] noncomputable def secPartsOK (c : Lay) (V P : Nat → Nat) (N : Nat) (O : Nat → Nat)
    (r : Nat) (J : Nat → Nat) : Bool :=
  strictB (O r) fun iT => strictB (Nat.add (nat_lit 1) (Nat.mul (nat_lit 3) r)) fun B =>
  andB (Nat.ble N (nat_lit 1048576)) (andB (Nat.blt iT N) (andB (allLt r fun i => Nat.blt (O i) N)
  (andB (stepIs P N (J 0) iT iT) (andB (Nat.beq (V (J 0)) c.ONE)
  (andB (allLt r fun i =>
      andB (stepIs P N (J (Nat.add (nat_lit 1) (Nat.mul (nat_lit 3) i))) (O i) iT)
      (andB (stepIs P N (J (Nat.add (nat_lit 2) (Nat.mul (nat_lit 3) i))) iT (O i))
      (andB (Nat.beq (V (J (Nat.add (nat_lit 1) (Nat.mul (nat_lit 3) i))))
        (V (J (Nat.add (nat_lit 2) (Nat.mul (nat_lit 3) i)))))
      (andB (stepIs P N (J (Nat.add (nat_lit 3) (Nat.mul (nat_lit 3) i))) (O i) (O i))
        (orB (Nat.beq (V (J (Nat.add (nat_lit 3) (Nat.mul (nat_lit 3) i)))) c.ONE)
          (Nat.beq (V (J (Nat.add (nat_lit 3) (Nat.mul (nat_lit 3) i)))) (V iT)))))))
    (allLt r fun i => allLt r fun j =>
      Bool.rec (motive := fun _ => Bool) true
        (strictB (Nat.add B (Nat.mul (nat_lit 3) (Nat.add (Nat.mul r i) j))) fun q =>
          andB (stepIs P N (J q) (O i) (O j))
          (andB (stepIs P N (J (Nat.succ q)) (O j) (O i))
          (andB (stepIs P N (J (Nat.add q (nat_lit 2))) iT (J (Nat.succ q)))
            (orB (Nat.beq (V (J q)) (V (J (Nat.succ q))))
              (Nat.beq (V (J q)) (V (J (Nat.add q (nat_lit 2)))))))))
        (Nat.blt i j)))))))

@[expose] noncomputable def vt0 (c : Lay) (t : Nat) (U : Nat → Nat) : Bool :=
  andB (Nat.blt t c.d) (Nat.beq (U (nat_lit 0)) (c.unit t))

@[expose] noncomputable def vtabK (c : Lay) (b : Nat) (X : Nat → Nat) (m : Nat) (U HI : Nat → Nat)
    (lo cnt : Nat) : Bool :=
  allLt cnt fun j => strictB (Nat.succ (Nat.add lo j)) fun n =>
    Bool.rec (motive := fun _ => Bool) true
      (strictB (HI n) fun h => strictB (Nat.pow b h) fun q =>
        andB (Nat.blt h m) (andB (Nat.ble q n) (andB (Nat.blt n (Nat.mul q b))
          (Nat.beq (U n) (c.vec (U (Nat.sub n q)) (X h))))))
      (Nat.blt n (Nat.pow b m))

@[expose] noncomputable def kmodK (c : Lay) (U : Nat → Nat) (T t r : Nat) : Bool :=
  strictB (c.vec (c.unit t) T) fun w =>
    allLt (Nat.sub (Nat.pow (nat_lit 2) r) (nat_lit 1)) fun n => strictB (U (Nat.succ n)) fun u =>
      andB (notB (Nat.beq u (c.unit t))) (notB (Nat.beq u w))

theorem stepOK_of_vals (c : Lay) (V P : Nat → Nat) (n a b q x y z : Nat) (hP : P n = q)
    (hq : Nat.beq q (Nat.add a (Nat.shiftLeft b 20)) = true)
    (hab : andB (Nat.blt a 1048576) (andB (Nat.blt a n) (Nat.blt b n)) = true)
    (hVn : V n = x) (hVa : V a = y) (hVb : V b = z) (hm : Nat.beq x (c.mul y z) = true) :
    stepOK c V P n = true := by
  have hq' : q = a + b * 2 ^ 20 := by
    rw [Nat.eq_of_beq_eq_true hq]
    change a + (b <<< 20) = _
    rw [Nat.shiftLeft_eq]
  have ha20 : a < 2 ^ 20 := by
    have := hab
    simp only [andB] at this
    cases h1 : Nat.blt a 1048576 <;> simp_all
  have han : a < n ∧ b < n := by
    have := hab
    simp only [andB] at this
    cases h1 : Nat.blt a 1048576 <;> cases h2 : Nat.blt a n <;> cases h3 : Nat.blt b n <;>
      simp_all [Nat.blt_eq]
  have hA : Nat.land q 1048575 = a := by
    change q &&& (2 ^ 20 - 1) = a
    rw [Nat.and_two_pow_sub_one_eq_mod, hq', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha20]
  have hB : Nat.shiftRight q 20 = b := by
    change q >>> 20 = b
    rw [Nat.shiftRight_eq_div_pow, hq', Nat.add_mul_div_right _ _ (Nat.two_pow_pos 20),
      Nat.div_eq_of_lt ha20, Nat.zero_add]
  have hs : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
  unfold stepOK
  rw [hs, hs, hs, hP, hA, hB, hVn, hVa, hVb, Nat.eq_of_beq_eq_true hm]
  have h1 : Nat.blt a n = true := Nat.blt_eq.mpr han.1
  have h2 : Nat.blt b n = true := Nat.blt_eq.mpr han.2
  rw [h1, h2, Nat.beq_refl]
  rfl

def ChunksTo (f : Nat → Bool) (n : Nat) : Prop := ∀ s, s < n → f s = true

theorem chunks_zero (f : Nat → Bool) : ChunksTo f 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem chunks_succ (f : Nat → Bool) (n : Nat) (h : ChunksTo f n) (hn : f n = true) :
    ChunksTo f (Nat.succ n) := fun s hs => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
  · exact h s hs
  · exact hn

end CFSG.KC.LocalComp.CubParts

end
