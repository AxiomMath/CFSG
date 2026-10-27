module

public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1BSpin

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT

@[expose] noncomputable def leqK : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun a _ ih l => List.rec (motive := fun _ => Bool) false (fun b t _ => andB (Nat.beq a b) (ih t)) l)

@[expose] noncomputable def packL : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v _ acc => Nat.add v (Nat.shiftLeft acc (nat_lit 24)))

@[expose] noncomputable def rowK (N r : Nat) : Nat := nIf(Nat.blt r (nat_lit 24), rowF (nat_lit 24) N r, nat_lit 0)

@[expose] noncomputable def sumAK (AK : List Nat) (c : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k _ ih acc => ih (nIf(bit c k, Nat.xor acc (getL (nat_lit 0) AK k), acc)))

@[expose] noncomputable def annK (RS AK bK : List Nat) (CP j i : Nat) : Nat :=
  strictN (getL oneK RS j) fun s =>
  strictN (vmF (nat_lit 24) CP (vmF (nat_lit 24) (trK (nat_lit 24) s) (getL (nat_lit 0) bK i))) fun c =>
    Nat.xor (sumAK AK c (List.range 24) (nat_lit 0)) (mulWK s (getL (nat_lit 0) AK i))

@[expose] noncomputable def selK (RS AK bK : List Nat) (CP v0 : Nat) (sel : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => andB (Nat.beq (vmF (nat_lit 24) (trK (nat_lit 24) (annK RS AK bK CP t.1 t.2.1)) v0) (nat_lit 0)) ih) sel

@[expose] noncomputable def eselK (RS AK bK : List Nat) (CP : Nat) (sel : List (Nat × Nat × Nat)) : List Nat :=
  sel.map fun t => rowK (annK RS AK bK CP t.1 t.2.1) t.2.2

@[expose] noncomputable def mtK (ATK : List Nat) (CP w : Nat) : Nat :=
  trK (nat_lit 24) (trK (nat_lit 24) (mulWK CP (packL (ATK.map fun T => vmF (nat_lit 24) T w))))

@[expose] noncomputable def candK (ATK bK : List Nat) (CP WC x : Nat) : Bool :=
  strictB (vmF (nat_lit 24) WC x) fun w => strictB (mtK ATK CP w) fun Mt =>
    allN (nat_lit 24) fun i => Nat.beq (vmF (nat_lit 24) Mt (getL (nat_lit 0) bK i))
      (vmF (nat_lit 24) (getL (nat_lit 0) ATK i) w)

@[expose] noncomputable def spinK (RS RIS : List Nat) (bw : List (List Int)) (v0 : Nat)
    (sel : List (Nat × Nat × Nat)) (m : Nat) (AK ATK bK : List Nat) (CP LP WC PP : Nat) : Bool :=
  andB (invsK RS RIS) (andB (Nat.beq bw.length (nat_lit 24)) (andB (leqK AK (bw.map (wordK RS RIS)))
  (andB (leqK ATK (AK.map (trK (nat_lit 24)))) (andB (leqK bK (ATK.map fun T => vmF (nat_lit 24) T v0))
  (andB (eqK (mulWK CP (packL bK)) oneK) (andB (Nat.beq sel.length (nat_lit 24))
  (andB (selK RS AK bK CP v0 sel) (andB (Nat.ble m (nat_lit 24))
  (andB (eqK (Nat.xor oneK (mulWK (trK (nat_lit 24) WC) PP)) (mulWK LP (packL (eselK RS AK bK CP sel))))
    (allN (Nat.pow (nat_lit 2) m) (candK ATK bK CP WC)))))))))))

@[expose] noncomputable def mxK (ATK : List Nat) (CP WC x : Nat) : Nat :=
  trK (nat_lit 24) (mulWK CP (packL (ATK.map fun T => vmF (nat_lit 24) T (vmF (nat_lit 24) WC x))))

@[expose] noncomputable def invK (P : Nat) : Nat := strictN (mulWK P P) fun Q => nIf(eqK Q oneK, P, Q)

@[expose] noncomputable def triK (T : Nat) (L : List (Nat × Nat)) : Bool :=
  L.all fun p => strictB (vmF (nat_lit 24) T p.1) fun a => orB (Nat.beq a p.1) (orB (Nat.beq a p.2) (Nat.beq a (Nat.xor p.1 p.2)))

@[expose] noncomputable def singK (G u : Nat) : Bool :=
  decide (u ≠ 0) && decide (u < 2 ^ 24) && vmF 24 (trK 24 G) u == 0

@[expose] noncomputable def exclK (X PA : Nat) (L : List (Nat × Nat)) (G e u : Nat) : Bool :=
  let c := powWK G e
  eqK (mulWK c PA) (mulWK PA c) && triK (trK 24 c) L &&
    decide (vmF 24 (trK 24 X) (vmF 24 (trK 24 c) u) < 2 ^ 24) &&
    decide (vmF 24 (trK 24 c) (vmF 24 (trK 24 X) u) < 2 ^ 24) &&
    vmF 24 (trK 24 X) (vmF 24 (trK 24 c) u) != vmF 24 (trK 24 c) (vmF 24 (trK 24 X) u)

@[expose] noncomputable def classK (ATK CX : List Nat) (CP WC X PA : Nat) (L : List (Nat × Nat)) (gdX : List Nat)
    (singRecs : List (Nat × Nat)) (exclRecs : List (Nat × Nat × Nat)) : Bool :=
  let g := fun x => getL 0 CX x
  allN 64 (fun x => eqK (g x) (mxK ATK CP WC x)) &&
    gdX.all (fun x => Nat.beq (mulK (g x) (invK (g x))) oneK) &&
    gdX.all (fun x => eqK (mulWK (g x) (g x)) oneK || eqK (mulWK (mulWK (g x) (g x)) (g x)) oneK) &&
    gdX.all (fun x => gdX.all fun y =>
      !(eqK (mulWK (g x) (g x)) oneK && eqK (mulWK (g y) (g y)) oneK) ||
        eqK (mulWK (g x) (g y)) (mulWK (g y) (g x))) &&
    decide ((gdX.filter fun x => eqK (mulWK (g x) (g x)) oneK).length ≤ 4) &&
    gdX.all (fun x => gdX.all fun y =>
      let c := mulWK (mulWK (mulWK (g x) (g y)) (invK (g x))) (invK (g y))
      eqK (mulWK c c) oneK) &&
    (List.range 64).all (fun x => gdX.contains x ||
      singRecs.any (fun r => r.1 == x && singK (g x) r.2) ||
      exclRecs.any (fun r => r.1 == x && exclK X PA L (g x) r.2.1 r.2.2))

end CFSG.KC.Co1BSpin

end
