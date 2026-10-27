module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefData
public import CFSG.Quasithin.Vol2.KGFactC31RuData
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

@[expose] def wsA (ws : List (List ℤ)) : List (Array ℕ) := ws.map wA

@[expose] def bEA : List (Array ℕ) := wsA basisEW
@[expose] def b64A : List (Array ℕ) := wsA basis64W
@[expose] def b3A : List (Array ℕ) := wsA basis3W
@[expose] def b16A : List (Array ℕ) := wsA basis16W
@[expose] def b32A : List (Array ℕ) := wsA basis32W
@[expose] def bV32EA : List (Array ℕ) := wsA basisV32EW
@[expose] def bV32pA : List (Array ℕ) := wsA basisV32pW

@[expose] def spE : List (Array ℕ) := spanA bEA
@[expose] def sp64 : List (Array ℕ) := spanA b64A
@[expose] def sp3 : List (Array ℕ) := spanA b3A
@[expose] def sp16 : List (Array ℕ) := spanA b16A
@[expose] def sp32 : List (Array ℕ) := spanA b32A
@[expose] def spV32E : List (Array ℕ) := spanA bV32EA
@[expose] def spV32p : List (Array ℕ) := spanA bV32pA

@[expose] def xEA : Array ℕ := wA xEW
@[expose] def x16A : Array ℕ := wA x16W
@[expose] def x32A : Array ℕ := wA x32W
@[expose] def g16A : Array ℕ := wA g16W
@[expose] def k16A : Array ℕ := wA k16W
@[expose] def cQA : Array ℕ := wA cQW
@[expose] def nEA : Array ℕ := wA nEW

@[expose] def pA : ℕ → Array ℕ → Array ℕ
  | 0, _ => idA 4060
  | k + 1, t => compA 4060 t (pA k t)

@[expose] def ebasisA (bs : List (Array ℕ)) : Bool :=
  (bs.all fun b => isInvA 4060 b b) && (bs.all fun b => bs.all fun c => commA b c) &&
    (List.range (2 ^ bs.length)).all fun m => m == 0 || !eqA 4060 (maskA bs m) (idA 4060)

@[expose] def normsA (t ti : Array ℕ) (bs sp : List (Array ℕ)) : Bool :=
  bs.all fun b => inA sp (cjA t ti b)

@[expose] def centA (bs : List (Array ℕ)) (c : Array ℕ) : Bool := bs.all fun b => commA c b

@[expose] def orbCommA (x xi : Array ℕ) (m : ℕ) (c : Array ℕ) : Bool :=
  (List.range m).all fun j => commA c (cjA (pA (j + 1) x) (pA (j + 1) xi) c)

@[expose] def twoElt (k : ℕ) (t : Array ℕ) : Bool := eqA 4060 (sqIterA k t) (idA 4060)

@[expose] def normPre (c : Array ℕ) (bs sp : List (Array ℕ)) : Bool :=
  (bs.all fun b => sp.any fun u => u.getD (c.getD 0 0) 0 == c.getD (b.getD 0 0) 0) &&
    normsA c (ruInv c) bs sp

@[expose] def bigZ (c : Array ℕ) : Bool :=
  (!(centA bEA c && isInvA 4060 c c && orbCommA xEA (ruInv xEA) 3 c) || inA spV32E c) &&
  (!(centA b64A c) || inA sp64 c) &&
  (!(centA b3A c) || inA sp64 c) &&
  (!(centA b16A c) || (twoElt 7 c && centA b16A (cjA g16A (ruInv g16A) c) &&
    (!(isInvA 4060 c c && orbCommA x16A (ruInv x16A) 2 c) || inA spV32p c))) &&
  (!(normPre c b16A sp16) || twoElt 10 c) &&
  (!(centA b32A c) || (twoElt 7 c &&
    (!(isInvA 4060 c c && orbCommA x32A (ruInv x32A) 2 c) || inA sp32 c)))

@[expose] def conjSp64 : List (List (Array ℕ)) :=
  conj64W.map fun w => spanA (b64A.map (cjA (wA w) (ruInv (wA w))))

@[expose] def spansDistinct (sps : List (List (Array ℕ))) : Bool :=
  (List.range sps.length).all fun i => (List.range sps.length).all fun j =>
    i == j || ((sps.getD i []).any fun u => !inA (sps.getD j []) u)

@[expose] def commutA (a b : Array ℕ) : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 a b) (ruInv a)) (ruInv b)

@[expose] def xWordA (w : List ℤ) : Array ℕ :=
  wordA 4060 #[xEA, cjA nEA (ruInv nEA) xEA] #[ruInv xEA, ruInv (cjA nEA (ruInv nEA) xEA)] w

@[expose] def root30A : Array ℕ := conjA (abA (hWordsZ.getD 0 [])) ruZA

@[expose] def refChecks : Bool :=
  ebasisA bEA && ebasisA b64A && ebasisA b3A && ebasisA b16A && ebasisA b32A &&
  ebasisA bV32EA && ebasisA bV32pA &&
  inA spE ruZA && inA sp64 ruZA && inA sp3 ruZA && inA sp16 ruZA && inA sp32 ruZA &&
  (bEA.all fun b => inA spV32E b) &&
  (bEA.all fun b => (List.range 7).any fun i => eqA 4060 b ruEArr[i]!) &&
  (spE.all fun v => eqA 4060 v (idA 4060) || (fixedList 4060 v).length == 92) &&
  (spV32E.all fun v => inA spE v || (fixedList 4060 v).length == 0) &&
  normsA x16A (ruInv x16A) b16A sp16 &&
  normsA ruC0A (ruInv ruC0A) b32A sp32 && normsA ruC1A (ruInv ruC1A) b32A sp32 &&
  eqA 4060 (pA 7 xEA) (idA 4060) && !eqA 4060 xEA (idA 4060) &&
  eqA 4060 (pA 5 x16A) (idA 4060) && !eqA 4060 x16A (idA 4060) &&
  eqA 4060 (pA 5 x32A) (idA 4060) && !eqA 4060 x32A (idA 4060) &&
  !normsA (cjA g16A (ruInv g16A) x16A) (ruInv (cjA g16A (ruInv g16A) x16A)) b16A sp16 &&
  (b32A.all fun b => inA spV32p (cjA k16A (ruInv k16A) b)) &&
  spansDistinct conjSp64 &&
  (ruKGensA.toList.all fun a => inA spE (compA 4060 a a) &&
    ruKGensA.toList.all fun b => inA spE (commutA a b)) &&
  eqA 4060 (commutA ruKGensA[3]! ruKGensA[4]!) (bEA.getD 0 #[]) &&
  eqA 4060 (commutA ruKGensA[3]! ruKGensA[1]!) (bEA.getD 1 #[]) &&
  eqA 4060 (commutA ruKGensA[4]! ruKGensA[0]!) (bEA.getD 2 #[]) &&
  eqA 4060 (xWordA (nsInXW.getD 0 [])) ruNs0A && eqA 4060 (xWordA (nsInXW.getD 1 [])) ruNs1A &&
  ruSift 1920 (ruField1920 3) ruJBase (resA ruF ruFPos cQA) &&
  !centA b32A (commutA x32A cQA) &&
  (sp32.all fun v => eqA 4060 v (idA 4060) || eqA 4060 v ruZA ||
    conj30W.any fun w => eqA 4060 (cjA (wA w) (ruInv (wA w)) root30A) v)

end CFSG.Quasithin.KGC31.Ru

end
