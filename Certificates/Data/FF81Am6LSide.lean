module

public import Certificates.Data.Item434SmallTwoIII

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def lsSig : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def lsX2p : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def lsV : List ℕ := vecCode 1 2 0

@[expose] def lsVInv : List ℕ := vecCode 2 1 0

@[expose] def lsSigK (k : ℕ) : List ℕ :=
  mul6 (mul6 (powCode (zCode 0) k) lsSig) (powCode (zCode 0) (3 - k))

@[expose] def lsAdm (t : List ℕ) : Bool :=
  mul6 t t == one6 && commutes6 t (zCode 2) && mul6 t lsV == mul6 lsVInv t

@[expose] def admCheck : Bool :=
  allCheck (fun t => !lsAdm t || t == lsSigK 0 || t == lsSigK 1 || t == lsSigK 2)
    (closureT ((centGens 3).map Prod.fst))

@[expose] def countP (p : List ℕ → Bool) (es : Array (List ℕ)) : ℕ :=
  (Finset.univ.filter fun t : Fin es.size => p (es.getD t [])).card

@[expose] def countCheck : Bool :=
  countP (fun t => commutes6 t lsSig) (closureT ((centGens 4).map Prod.fst)) == 36 &&
    countP (fun t => commutes6 t lsSig && commutes6 t (zCode 2) && commutes6 t lsX2p)
      (closureT ((centGens 4).map Prod.fst)) == 6

@[expose] def rhoImg (p₁ p₂ p₃ a₁ a₂ a₃ i : ℕ) : ℕ :=
  if i % 3 == p₁ then 2 + 3 * ((i / 3 + a₁ + 1) % 2)
  else if i % 3 == p₂ then 0 + 3 * ((i / 3 + a₂ + 1) % 2)
  else 1 + 3 * ((i / 3 + a₃ + 1) % 2)

@[expose] def rhoC (p₁ p₂ p₃ a₁ a₂ a₃ : ℕ) : List ℕ :=
  (List.range 36).map fun t => if rhoImg p₁ p₂ p₃ a₁ a₂ a₃ (t % 6) == t / 6 then 1 else 0

@[expose] def rhoIC (p₁ p₂ p₃ a₁ a₂ a₃ : ℕ) : List ℕ :=
  (List.range 36).map fun t => if rhoImg p₁ p₂ p₃ a₁ a₂ a₃ (t / 6) == t % 6 then 1 else 0

@[expose] def frameOne (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : ℕ) : Bool :=
  pairCheck (rhoC p₁ p₂ p₃ a₁ a₂ a₃, rhoIC p₁ p₂ p₃ a₁ a₂ a₃) &&
    mul6 (mul6 (rhoC p₁ p₂ p₃ a₁ a₂ a₃) (powCode (zCode p₁) a₁)) (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) ==
      zCode 2 &&
    mul6 (mul6 (rhoC p₁ p₂ p₃ a₁ a₂ a₃) (powCode (zCode p₂) a₂)) (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) ==
      zCode 0 &&
    mul6 (mul6 (rhoC p₁ p₂ p₃ a₁ a₂ a₃) (powCode (zCode p₃) a₃)) (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) ==
      zCode 1

@[expose] def frameCheck : Bool :=
  (List.finRange 3).all fun p₁ => (List.finRange 3).all fun p₂ => (List.finRange 3).all fun p₃ =>
    [1, 2].all fun a₁ => [1, 2].all fun a₂ => [1, 2].all fun a₃ =>
      !(p₁ != p₂ && p₂ != p₃ && p₁ != p₃) || frameOne p₁ p₂ p₃ a₁ a₂ a₃

@[expose] def lsideCheck : Bool :=
  admCheck && countCheck && frameCheck

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData
