module

public import Certificates.Data.RudvalisFF81Sp8Torus

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U

@[expose] def czGens : List (List ℕ) :=
  [[16, 2, 4, 8, 17, 32, 64, 128], [1, 32, 4, 8, 16, 34, 64, 128], [2, 1, 4, 8, 32, 16, 64, 128],
    [1, 2, 64, 8, 16, 32, 68, 128], [1, 2, 64, 8, 16, 32, 4, 128], [1, 2, 8, 4, 16, 32, 128, 64],
    [1, 2, 4, 12, 16, 32, 192, 128]]

@[expose] def f1S : List ℕ := [1, 32, 4, 8, 16, 2, 64, 128]

@[expose] def yS (v : ℕ) : ℕ := mv8 zzS v

@[expose] def condW (a b : ℕ) : Bool :=
  (a ^^^ yS a == yS (yS a)) && (b ^^^ yS b == yS (yS b)) && b4N a (yS a) && b4N b (yS b) &&
    !b4N a b && !b4N a (yS b) && !b4N (yS a) b && !b4N (yS a) (yS b)

@[expose] def fixW : Finset ℕ := (Finset.range 256).filter fun v => yS v = v

@[expose] def condW' (p q r s : ℕ) : Bool :=
  b4N p r && b4N q s && !b4N p q && !b4N p s && !b4N r q && !b4N r s

@[expose] def cWS : Finset (ℕ × ℕ) :=
  ((Finset.range 256) ×ˢ (Finset.range 256)).filter fun x => condW x.1 x.2 = true

@[expose] def cW'S : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (fixW ×ˢ fixW ×ˢ fixW ×ˢ fixW).filter fun x => condW' x.1 x.2.1 x.2.2.1 x.2.2.2 = true

@[expose] def czChk899105 : Bool :=
  tabOK czGens (tabS czGens 12960) 12960 && czGens.all (commS zzS)

@[expose] def colChk899105 : Bool :=
  cWS.card == 18 && cW'S.card == 720

@[expose] def e0cChk899105 : Bool :=
  let E := tabS e0Gens 81
  let mE := indexMap E
  allCheck (fun x => !(e0Gens.all (commS x)) || found E mE x) (tabS czGens 12960)

@[expose] def w2S (i j : ℕ) : List (List ℕ) :=
  [mulS (l1S.getD (2 * i) []) (l1S.getD (2 * j) []),
    mulS (l1S.getD (2 * i) []) (l1S.getD (2 * j + 1) []),
    mulS (l1S.getD (2 * i + 1) []) (l1S.getD (2 * j) []),
    mulS (l1S.getD (2 * i + 1) []) (l1S.getD (2 * j + 1) [])]

@[expose] def hypChk899105 : Bool :=
  let E := tabS e0Gens 81
  let mE := indexMap E
  allCheck (fun x => (w2S 2 3).all fun a => (w2S 0 3).all fun b =>
    !(commS x a && commS x b) || found E mE x) (tabS czGens 12960)

@[expose] def f1Chk899105 : Bool :=
  spS f1S && mulS f1S f1S == one8 && commS f1S z0S && commS f1S z2S && commS f1S z3S &&
    mulS (mulS f1S z1S) f1S == mulS z1S z1S

@[expose] def e9Chk899105 : Bool :=
  [(0, 1), (2, 3), (0, 3)].all fun ij =>
    let gens := [e0Gens.getD ij.1 [], e0Gens.getD ij.2 []]
    let T := tabS gens 9
    tabOK gens T 9 &&
      allCheck (fun x => x == one8 || l1S.contains x || (w2S ij.1 ij.2).contains x) T

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
