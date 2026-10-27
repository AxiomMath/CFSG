module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec4G2Mat
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

@[expose] def nq (c : ℕ) : ℕ := if c.testBit 0 then c ^^^ 129 else c

@[expose] def sqL (c : ℕ) : ℕ := if zornNorm (decodeZ c) = 0 then c else c ^^^ 129

@[expose] def collC (c d : ℕ) : Bool :=
  c != d && encodeZ (quasithinZornMul (decodeZ (sqL c)) (decodeZ (sqL d))) == 0

@[expose] def ptsQ : List ℕ := (List.range 63).map fun k => 2 * (k + 1)

@[expose] def collTabQ : List ℕ := [
  0, 844437815230464, 5519032976640, 648518385147052032,
  286331136, 2377936887137501184, 4702039485951525120, 36452111159918592,
  21588, 9241395249175068672, 88304527606020, 4620695434162077696,
  1145307408, 4613942766078001152, 1446781380292772160, 162134122339762176,
  3276850, 13511005040607234, 9225659030704230400, 2307039286723117056,
  570499600, 1297056483892068384, 2306415305083064320, 288828785623566336,
  2550136984, 324329576275648512, 153263159182888960, 10376294159953690632,
  25724944, 577727664577577472, 612491885784862720, 6781787736899712,
  60129542158, 3377704016281602, 10999411247620, 432345568623198216,
  9232449604988044288, 580968751051210752, 577041294988149760, 1153488852745199616,
  180319906955428, 1188950319881521152, 1786706436100, 2310346628172612096,
  146367264917029888, 9511603512526766112, 2341871874986214400, 10134199277191296,
  54606145481867458, 282299623014402, 1153062251222548480, 4611703621351120896,
  288239311831318528, 4611826824702461952, 9367768699907375680, 354043851440256,
  7493989779944505448, 18032025124503552, 4538818401157120, 72058007965401096,
  1128648822243328, 72136758879846432, 83316593106364480, 18049651735527936]

@[expose] def collT (c d : ℕ) : Bool := (collTabQ.getD (c / 2) 0).testBit (d / 2)

theorem collTabQ_spec : ∀ c ∈ ptsQ, ∀ d ∈ ptsQ, collC c d = collT c d := by
  decide +kernel

theorem collT_symm : ∀ c ∈ ptsQ, ∀ d ∈ ptsQ, collT c d = collT d c := by
  decide +kernel

theorem collT_xor : ∀ c ∈ ptsQ, ∀ d ∈ ptsQ, collT c d = true →
    (c ^^^ d) ∈ ptsQ ∧ collT c (c ^^^ d) = true ∧ collT d (c ^^^ d) = true := by
  decide +kernel

theorem collT_common : ∀ c ∈ ptsQ, ∀ d ∈ ptsQ, c ≠ d →
    (ptsQ.filter fun e => collT c e && collT d e).length ≤ 1 := by
  decide +kernel

end CFSG.Quasithin.H13.L32A.M755
