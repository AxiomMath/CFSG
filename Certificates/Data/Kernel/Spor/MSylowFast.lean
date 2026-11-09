module

public meta import Lean
public import Certificates.Data.Kernel.Spor.MSylowCent
public import CFSG.Certificates.Kernel.Common.NatBuckets

public section

namespace CFSG.KS.MSylF

open CFSG.KC.Enum CFSG.KS.PCnt CFSG.KS.MSyl

local notation "NBmem" => CFSG.KC.NatBuckets.memB
local notation "NBins" => CFSG.KC.NatBuckets.insB

theorem memB_eq_memN (x : Nat) : ∀ l : List Nat, memB x l = CFSG.KC.NatBuckets.memN l x
  | [] => rfl
  | a :: l => by
    change Bool.rec (motive := fun _ => Bool) (memB x l) true (Nat.beq x a) =
      (Nat.beq x a || CFSG.KC.NatBuckets.memN l x)
    rw [memB_eq_memN x l]
    cases Nat.beq x a <;> rfl

@[expose] noncomputable def letQ {α : Sort _} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem letQ_eq {α : Sort _} (y : Nat) (k : Nat → α) : letQ y k = k y := by
  cases y <;> rfl

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def bucketsAcc (l : List Nat) : List (List Nat) → List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun B => B)
    (fun a _ ih B => letQ (List.length (NBins B a)) fun _ =>
      letQ (List.length ((NBins B a).getD (Nat.mod a 37) [])) fun _ => ih (NBins B a)) l

@[expose] noncomputable def bucketsOfS (l : List Nat) : List (List Nat) :=
  bucketsAcc l (List.replicate 37 [])

theorem bucketsAcc_eq : ∀ (l : List Nat) (B : List (List Nat)),
    bucketsAcc l B = l.foldl CFSG.KC.NatBuckets.insB B
  | [], _ => rfl
  | a :: l, B => by
    change letQ _ (fun _ => letQ _ fun _ => bucketsAcc l (NBins B a)) = _
    rw [letQ_eq, letQ_eq, bucketsAcc_eq l, List.foldl_cons]

theorem bucketsOfS_eq (l : List Nat) : bucketsOfS l = CFSG.KC.NatBuckets.bucketsOf l :=
  bucketsAcc_eq l _

theorem closedP_of {n w m : Nat} {E gs : List Nat}
    (h : allL (fun e => allL (fun g => NBmem (bucketsOfS E) (pcomp n w m e g)) gs) E = true) :
    closedP n w m E gs = true := by
  unfold closedP
  simp only [memB_eq_memN, CFSG.KC.NatBuckets.memN_eq_memB]
  rw [bucketsOfS_eq] at h
  exact h

def Inv (E : List Nat) (B : List (List Nat)) : Prop :=
  B.length = 37 ∧ ∀ z, NBmem B z = CFSG.KC.NatBuckets.memN E z

theorem inv_snoc {E : List Nat} {B : List (List Nat)} (h : Inv E B) (z : Nat) :
    Inv (E ++ [z]) (NBins B z) := by
  refine ⟨(CFSG.KC.NatBuckets.insB_length _ _).trans h.1, fun x => ?_⟩
  rw [CFSG.KC.NatBuckets.memB_insB h.1, h.2]
  simp only [CFSG.KC.NatBuckets.memN, List.any_append, List.any_cons, List.any_nil]
  cases Nat.beq x z <;> cases E.any (fun a => Nat.beq x a) <;> rfl

@[expose] noncomputable def eqNL (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (ih ys) (Nat.beq x y)) m) l

theorem eq_of_eqNL : ∀ {l m : List Nat}, eqNL l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    cases h
  | _ :: _, [], h => by
    change false = true at h
    cases h
  | x :: l, y :: m, h => by
    change Bool.rec (motive := fun _ => Bool) false (eqNL l m) (Nat.beq x y) = true at h
    cases hb : Nat.beq x y
    · rw [hb] at h
      change false = true at h
      cases h
    · rw [hb] at h
      change eqNL l m = true at h
      rw [Nat.eq_of_beq_eq_true hb, eq_of_eqNL h]

theorem bucketsOf_length : ∀ (l : List Nat) (B : List (List Nat)),
    (l.foldl CFSG.KC.NatBuckets.insB B).length = B.length
  | [], _ => rfl
  | a :: l, B => by
    rw [List.foldl_cons, bucketsOf_length l, CFSG.KC.NatBuckets.insB_length]

theorem inv_bucketsOf (E : List Nat) : Inv E (CFSG.KC.NatBuckets.bucketsOf E) :=
  ⟨(bucketsOf_length E _).trans (List.length_replicate ..),
    fun z => (CFSG.KC.NatBuckets.memN_eq_memB E z).symm⟩

abbrev StQ := List Nat × List (List Nat) × List Nat × List Nat

@[expose] noncomputable def clAddQ (n w m y : Nat) (gs : List Nat) : StQ → StQ :=
  List.rec (motive := fun _ => StQ → StQ) (fun s => s)
    (fun g _ ih s => letQ (pcomp n w m y g) (fun z =>
      Bool.rec (motive := fun _ => StQ)
        (letQ (List.length (NBins s.2.1 z)) fun _ =>
          letQ (List.length ((NBins s.2.1 z).getD (Nat.mod z 37) [])) fun _ =>
            ih (z :: s.1, NBins s.2.1 z, s.2.2.1, z :: s.2.2.2)) (ih s)
        (NBmem s.2.1 z))) gs

@[expose] noncomputable def frontQ (F Q : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) Q.reverse (fun a l _ => a :: l) F

@[expose] noncomputable def rearQ (F Q : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ _ _ => Q) F

@[expose] noncomputable def clRunQ (n w m : Nat) (gs : List Nat) (fuel : Nat) :
    Nat → StQ → StQ :=
  Nat.rec (motive := fun _ => Nat → StQ → StQ) (fun _ s => s)
    (fun _ ih h s => List.rec (motive := fun _ => StQ) (ih (Nat.succ h) s)
      (fun y F _ => ih (Nat.succ h)
        (clAddQ n w m y gs (s.1, s.2.1, F, rearQ s.2.2.1 s.2.2.2)))
      (frontQ s.2.2.1 s.2.2.2)) fuel

def RelQ (k : Nat) (E : List Nat) (s : StQ) : Prop :=
  s.1.reverse = E ∧ Inv E s.2.1 ∧ s.2.2.1 ++ s.2.2.2.reverse = E.drop k

theorem front_rear (F Q : List Nat) : frontQ F Q ++ (rearQ F Q).reverse = F ++ Q.reverse := by
  cases F <;> simp [frontQ, rearQ]

theorem clAddQ_eq {n w m y : Nat} : ∀ (gs E : List Nat) (k : Nat) (s : StQ), RelQ k E s →
    k ≤ E.length → clAdd n w m y gs E = (clAddQ n w m y gs s).1.reverse ∧
      RelQ k (clAdd n w m y gs E) (clAddQ n w m y gs s) ∧ k ≤ (clAdd n w m y gs E).length
  | [], E, k, s, h, hk => ⟨h.1.symm, h, hk⟩
  | g :: gs, E, k, s, h, hk => by
    have e1 : clAdd n w m y (g :: gs) E = Bool.rec (motive := fun _ => List Nat)
        (clAdd n w m y gs (E ++ [pcomp n w m y g])) (clAdd n w m y gs E)
        (memB (pcomp n w m y g) E) := by
      change strictL (pcomp n w m y g) (fun z => Bool.rec (motive := fun _ => List Nat)
        (clAdd n w m y gs (E ++ [z])) (clAdd n w m y gs E) (memB z E)) = _
      rw [strictL_eq]
    have e2 : clAddQ n w m y (g :: gs) s = Bool.rec (motive := fun _ => StQ)
        (clAddQ n w m y gs (pcomp n w m y g :: s.1, NBins s.2.1 (pcomp n w m y g), s.2.2.1,
          pcomp n w m y g :: s.2.2.2)) (clAddQ n w m y gs s) (NBmem s.2.1 (pcomp n w m y g)) := by
      change letQ (pcomp n w m y g) (fun z => Bool.rec (motive := fun _ => StQ)
        (letQ (List.length (NBins s.2.1 z)) fun _ =>
          letQ (List.length ((NBins s.2.1 z).getD (Nat.mod z 37) [])) fun _ =>
            clAddQ n w m y gs (z :: s.1, NBins s.2.1 z, s.2.2.1, z :: s.2.2.2))
        (clAddQ n w m y gs s) (NBmem s.2.1 z)) = _
      simp only [letQ_eq]
    rw [e1, e2, memB_eq_memN, h.2.1.2]
    cases CFSG.KC.NatBuckets.memN E (pcomp n w m y g)
    · apply clAddQ_eq gs _ k _ _ (by simp only [List.length_append]; omega)
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.reverse_cons, h.1]
      · rw [← h.1]
        have := inv_snoc h.2.1 (pcomp n w m y g)
        rw [h.1]
        exact this
      · simp only [List.reverse_cons, ← List.append_assoc, h.2.2]
        rw [List.drop_append_of_le_length hk]
    · exact clAddQ_eq gs E k s h hk

theorem getN_of_drop : ∀ (E : List Nat) (h y : Nat) (t : List Nat), E.drop h = y :: t →
    getN E h = y
  | [], h, y, t, e => by simp at e
  | a :: E, 0, y, t, e => by
    simp only [List.drop_zero, List.cons.injEq] at e
    rw [← e.1]
    rfl
  | a :: E, h + 1, y, t, e => by
    rw [List.drop_succ_cons] at e
    exact getN_of_drop E h y t e

theorem clRunQ_eq {n w m : Nat} {gs : List Nat} : ∀ (fuel h : Nat) (E : List Nat) (s : StQ),
    RelQ h E s → clRun n w m gs fuel h E = (clRunQ n w m gs fuel h s).1.reverse
  | 0, _, _, s, hr => hr.1.symm
  | fuel + 1, h, E, s, hr => by
    change Bool.rec (motive := fun _ => List Nat) (clRun n w m gs fuel (Nat.succ h) E)
        (clRun n w m gs fuel (Nat.succ h) (clAdd n w m (getN E h) gs E)) (Nat.blt h E.length) =
      (List.rec (motive := fun _ => StQ) (clRunQ n w m gs fuel (Nat.succ h) s)
        (fun y F _ => clRunQ n w m gs fuel (Nat.succ h)
          (clAddQ n w m y gs (s.1, s.2.1, F, rearQ s.2.2.1 s.2.2.2)))
        (frontQ s.2.2.1 s.2.2.2)).1.reverse
    have hq := front_rear s.2.2.1 s.2.2.2
    rw [hr.2.2] at hq
    cases hf : frontQ s.2.2.1 s.2.2.2 with
    | nil =>
      have hd : E.drop h = [] := by
        rw [← hq, hf]
        cases hF : s.2.2.1 <;> simp_all [frontQ, rearQ]
      have hle : E.length ≤ h := List.drop_eq_nil_iff.mp hd
      have hlt : Nat.blt h E.length = false := by
        cases hb : Nat.blt h E.length
        · rfl
        · have := Nat.blt_eq.mp hb
          omega
      rw [hlt]
      dsimp only
      apply clRunQ_eq fuel _ E s
      refine ⟨hr.1, hr.2.1, ?_⟩
      rw [hr.2.2, hd, eq_comm, List.drop_eq_nil_iff]
      omega
    | cons y F =>
      rw [hf] at hq
      have hlt : h < E.length := by
        have : E.drop h ≠ [] := by rw [← hq]; simp
        simpa [List.drop_eq_nil_iff] using this
      have hb : Nat.blt h E.length = true := Nat.blt_eq.mpr hlt
      rw [hb]
      dsimp only
      have hy : getN E h = y := getN_of_drop E h y _ hq.symm
      rw [hy]
      have hr' : RelQ (h + 1) E (s.1, s.2.1, F, rearQ s.2.2.1 s.2.2.2) := by
        refine ⟨hr.1, hr.2.1, ?_⟩
        rw [← List.drop_drop, ← hq]
        simp
      obtain ⟨_, e2, _⟩ := clAddQ_eq (n := n) (w := w) (m := m) (y := y) gs E (h + 1) _ hr' hlt
      exact clRunQ_eq fuel _ _ _ e2

theorem closP_eqQ (n w m I : Nat) (gs : List Nat) (cap : Nat) :
    closP n w m I gs cap =
      (clRunQ n w m gs cap (nat_lit 0) ([I], bucketsOfS [I], [I], [])).1.reverse := by
  apply clRunQ_eq
  refine ⟨rfl, bucketsOfS_eq [I] ▸ inv_bucketsOf [I], ?_⟩
  rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sylowAutP_of {n w m I a ai b bi : Nat} {ds es : List (List Int)} {z zi cap N k : Nat}
    {pT pTi E : List Nat}
    (hpT : exprsV n w m I (slpP n w m I a ai b bi ds) es = pT)
    (hpTi : exprsI n w m I (slpP n w m I a ai b bi ds) es = pTi)
    (hE : closP n w m I pT cap = E)
    (h1 : Nat.beq (pcomp n w m a ai) I = true) (h2 : Nat.beq (pcomp n w m b bi) I = true)
    (h3 : Nat.beq (pcomp n w m z zi) I = true)
    (h4 : closedP n w m E pT = true) (h5 : closedP n w m E pTi = true) (h6 : distB E = true)
    (h7 : Nat.beq E.length (Nat.shiftLeft (nat_lit 1) k) = true)
    (h8 : Nat.beq (Nat.mod N (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 0) = true)
    (h9 : Nat.beq (Nat.mod (Nat.div N (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 2)) (nat_lit 1) =
      true)
    (h10 : memB a E = true) (h11 : memB z E = true) (h12 : commAllP n w m z pT = true) :
    sylowAutP n w m I a ai b bi ds es z zi cap N k = true := by
  unfold sylowAutP
  rw [strictB_eq]
  simp only []
  rw [hpT, hpTi, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

@[expose] noncomputable def packW (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

open Lean in
meta def kwNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) {} e with
  | .ok (.lit (.natVal v)) => return v
  | .ok r => throwError "#kw_list: not a literal: {r}"
  | .error _ => throwError "#kw_list: kernel exception while reducing {e}"

end CFSG.KS.MSylF

open Lean Elab Command Meta CFSG.KS.MSylF in
elab "#kw_list " nm:ident t:term:max w:num : command => do
  let w := w.getNat
  let el (s : Term) : CommandElabM Expr := liftTermElabM do
    let e ← Term.elabTerm s (some (Lean.mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let n ← liftTermElabM <| kwNat (← el (← `(List.length $t)))
  let wl := Syntax.mkNumLit (toString w)
  let v ← liftTermElabM <| kwNat (← el (← `(CFSG.KS.MSylF.packW $wl $t)))
  let msk := (1 <<< w) - 1
  let xs := (List.range n).map fun i => (v >>> (w * i)) &&& msk
  unless v >>> (w * n) == 0 do throwError "#kw_list: entries do not fit in {w} bits"
  let nT := Lean.mkConst ``Nat
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := nm.getId, levelParams := [], type := mkApp (Lean.mkConst ``List [0]) nT,
        value := xs.foldr
          (fun x acc => mkApp3 (Lean.mkConst ``List.cons [0]) nT (mkRawNatLit x) acc)
          (mkApp (Lean.mkConst ``List.nil [0]) nT),
        hints := .regular 0, safety := .safe }

end
