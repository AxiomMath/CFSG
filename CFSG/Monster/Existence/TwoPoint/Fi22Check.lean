module

public import CFSG.Monster.Existence.TwoPoint.Fi23Check
public import CFSG.Monster.Existence.TwoPoint.Fi22Data
public import Certificates.Data.CFSGNative.Fi23.Classes

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (imgWords)
open CFSG.Sporadic.Fi23.Native (dLetters)

@[expose] def fiWDelta : List Native.Gen := fiWBeta ++ fiWU[0]!

@[expose, noinline] def fiConj22Check : Bool :=
  fiEqP (fiRhoT ++ fiCGamma) (fiCGamma ++ fiWU[0]!) (HS.pw fiRhoT ++ HS.pw fiCGamma)
      (HS.pw fiCGamma ++ fiPU[0]!) &&
    fiEqP (fiRhoT ++ fiCDelta) (fiCDelta ++ fiWDelta) (HS.pw fiRhoT ++ HS.pw fiCDelta)
      (HS.pw fiCDelta ++ HS.pw fiWDelta)

theorem fiConj22Check_parts
    (h : wordLin (fiRhoT ++ fiCGamma) = wordLin (fiCGamma ++ fiWU[0]!) ∧
      wordLin (fiRhoT ++ fiCDelta) = wordLin (fiCDelta ++ fiWDelta)) :
    wordLin fiCGamma * wordLin fiRhoT = wordLin fiWU[0]! * wordLin fiCGamma ∧
      wordLin fiCDelta * wordLin fiRhoT = wordLin fiWDelta * wordLin fiCDelta := by
  obtain ⟨h1, h2⟩ := h
  rw [wordLin_append, wordLin_append] at h1 h2
  exact ⟨h1, h2⟩

@[expose] def fiInvWord (u : List Int) : List Int := u.reverse.map fun z => -z

@[expose] def fiDPowWord : List Int := (List.replicate 7 dLetters).flatten

@[expose, noinline] def fiImgConjCheck (k m : ℕ) : Bool :=
  imgWords[k]! == imgWords[k]!.take m ++ fiDPowWord ++ fiInvWord (imgWords[k]!.take m) &&
    (imgWords[k]!.take m).all fun z => z == 1 || z == -1 || z == 2 || z == -2

@[expose, noinline] def fi22Check : Bool := fiConj22Check && fiImgConjCheck 0 27

end CFSG.Monster.Existence
