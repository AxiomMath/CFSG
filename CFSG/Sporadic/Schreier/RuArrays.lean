module

public import CFSG.Sporadic.Schreier.RuDefs
public import CFSG.Sporadic.Schreier.RuOrbit

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruInv (t : Array ℕ) : Array ℕ := invCand 4060 t

@[expose] def ruA0A : Array ℕ := ruArr4060 0

@[expose] def ruA1A : Array ℕ := ruArr4060 1

@[expose] def ruCRunA : Array ℕ × Array ℕ × Bool := slotRunA 4060 ruCProg ruA0A ruA1A

@[expose] def ruNRunA : Array ℕ × Array ℕ × Bool := slotRunA 4060 ruNProg ruA0A ruA1A

@[expose] def ruC0A : Array ℕ := ruCRunA.1

@[expose] def ruC1A : Array ℕ := ruCRunA.2.1

@[expose] def ruN0A : Array ℕ := ruNRunA.1

@[expose] def ruN1A : Array ℕ := ruNRunA.2.1

@[expose] def ruZA : Array ℕ := powA 4060 ruC0A 10

@[expose] def ruZ0A : Array ℕ :=
  wordA 4060 #[ruN0A, ruN1A] #[ruInv ruN0A, ruInv ruN1A] ruNCenterWord

@[expose] def ruWA : Array ℕ := wordA 4060 #[ruA0A, ruA1A] #[ruInv ruA0A, ruInv ruA1A] ruSeedWord

@[expose] def ruUA : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 ruWA ruZ0A) (ruInv ruWA)) ruZA

@[expose] def ruHA : Array ℕ := compA 4060 (powA 4060 ruUA 3) ruWA

@[expose] def ruNs0A : Array ℕ := compA 4060 (compA 4060 ruHA ruN0A) (ruInv ruHA)

@[expose] def ruNs1A : Array ℕ := compA 4060 (compA 4060 ruHA ruN1A) (ruInv ruHA)

@[expose] def ruSGensA : Array (Array ℕ) :=
  (ruSWords.map (wordA 4060 #[ruNs0A, ruNs1A] #[ruInv ruNs0A, ruInv ruNs1A])).toArray

@[expose] def ruKGensA : Array (Array ℕ) :=
  (ruKWords.map (wordA 4060 #[ruNs0A, ruNs1A] #[ruInv ruNs0A, ruInv ruNs1A])).toArray

@[expose] def ruJGensA : Array (Array ℕ) :=
  (ruJWords.map (wordA 4060 #[ruC0A, ruC1A] #[ruInv ruC0A, ruInv ruC1A])).toArray

@[expose] def ruRGensA : Array (Array ℕ) :=
  (ruRWords.map (wordA 4060 ruSGensA (ruSGensA.map ruInv))).toArray

@[expose] def ruPosTab (n : ℕ) (Fl : Array ℕ) : Array ℕ :=
  (List.range Fl.size).foldl (fun r i => r.set! Fl[i]! i) (Array.replicate n n)

@[expose] def ptPosOK (n : ℕ) (Fl pos : Array ℕ) : Bool :=
  allLt Fl.size fun i => decide (Fl[i]! < n) && pos[Fl[i]!]! == i

@[expose] def ruFPos : Array ℕ := ruPosTab 4060 ruF

@[expose] def ruYPos : Array ℕ := ruPosTab 4060 ruY

@[expose] def ruLabTab (n : ℕ) (Ls : List (Array ℕ)) : Array ℕ :=
  (List.range Ls.length).foldl (fun r k =>
    (List.range (Ls.getD k #[]).size).foldl (fun r i => r.set! (Ls.getD k #[])[i]! k) r)
    (Array.replicate n 0)

@[expose] def labListsOK (n : ℕ) (Ls : List (Array ℕ)) (lab : Array ℕ) (pos : List (Array ℕ)) :
    Bool :=
  (allLt Ls.length fun k => allLt (Ls.getD k #[]).size fun i =>
    decide ((Ls.getD k #[])[i]! < n) && lab[(Ls.getD k #[])[i]!]! == k) &&
  allLt n fun x => decide (lab[x]! < Ls.length) &&
    decide ((pos.getD lab[x]! #[])[x]! < (Ls.getD lab[x]! #[]).size) &&
    (Ls.getD lab[x]! #[])[(pos.getD lab[x]! #[])[x]!]! == x

@[expose] def ruCOrbits : List (Array ℕ) := (List.range 4).map ruCOrbit

@[expose] def ruNOrbits : List (Array ℕ) := (List.range 3).map ruNOrbit

@[expose] def ruCLab : Array ℕ := ruLabTab 4060 ruCOrbits

@[expose] def ruNLab : Array ℕ := ruLabTab 4060 ruNOrbits

@[expose] def ruCOrbitPos : List (Array ℕ) := ruCOrbits.map (ruPosTab 4060)

@[expose] def ruNOrbitPos : List (Array ℕ) := ruNOrbits.map (ruPosTab 4060)

@[expose] def ruCRoots : Array ℕ := (ruCOrbits.map fun L => L[0]!).toArray

@[expose] def ruNRoots : Array ℕ := (ruNOrbits.map fun L => L[0]!).toArray

@[expose] def ruCForest : Array ℕ × Array ℕ × Array ℕ := orbitForest 4060 #[ruC0A, ruC1A] ruCRoots

@[expose] def ruNForest : Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 4060 #[ruNs0A, ruNs1A] ruNRoots

@[expose] def ruCBlockPerms : List (Array ℕ) := [#[5, 3, 0, 2, 4, 1], #[2, 5, 0, 4, 3, 1]]

@[expose] def ruNBlockPerms : List (Array ℕ) :=
  [#[0, 2, 1, 4, 3, 5, 6], #[5, 6, 2, 1, 0, 4, 3]]

@[expose] def ruCBlockStrong : Array (Array ℕ) :=
  #[#[5, 3, 0, 2, 4, 1], #[2, 5, 0, 4, 3, 1], #[0, 1, 4, 5, 3, 2], #[0, 4, 1, 3, 5, 2],
    #[0, 4, 2, 5, 1, 3], #[0, 3, 2, 4, 5, 1]]

@[expose] def ruNBlockStrong : Array (Array ℕ) :=
  #[#[0, 2, 1, 4, 3, 5, 6], #[5, 6, 2, 1, 0, 4, 3], #[5, 1, 6, 0, 2, 3, 4],
    #[0, 1, 3, 2, 4, 6, 5], #[0, 1, 5, 6, 4, 2, 3]]

@[expose] def ruChainCBlock : RawSchreierDatum 6 :=
  RawSchreierDatum.ofArrays 6 (by decide) ruCBlockStrong 2 (by decide)
    (ruFinList 6 (by decide) [0, 2, 1]) (by decide)
    (ruWordsArr 2 6 [[-2, -1], [-1, -1, 2, 1], [3, -4], [3, 4, 3]])

@[expose] def ruChainNBlock : RawSchreierDatum 7 :=
  RawSchreierDatum.ofArrays 7 (by decide) ruNBlockStrong 2 (by decide)
    (ruFinList 7 (by decide) [1, 0, 2]) (by decide)
    (ruWordsArr 2 5 [[-1, 2, 1], [-2, 3, 1], [3, -4, -3, 4, 3]])

end CFSG.Sporadic.RuSchreier
