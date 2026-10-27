module

public import Certificates.Data.HePresCheck
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] noncomputable def heSeedMat (l : ℤ) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  if l = 1 ∨ l = -1 then CFSG.Sporadic.He.mA else if l = 2 then CFSG.Sporadic.He.mB
  else CFSG.Sporadic.He.mB⁻¹

@[expose] noncomputable def heWordMat (w : List ℤ) : Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  (w.map heSeedMat).prod

@[expose] noncomputable def hePiLetMat (gw : List (List ℤ)) (l : Fin 8 × Bool) :
    Matrix (Fin 50) (Fin 50) (ZMod 7) :=
  if l.2 then heWordMat (gw.getD l.1.val []) else (heWordMat (gw.getD l.1.val []))⁻¹

abbrev HePiImageFacts : Prop :=
  hePiHeWords.length = 8 ∧ (∀ w ∈ hePiHeWords, lettersOK 2 w = true) ∧
    (∀ r ∈ hePiRels, (r.map (hePiLetMat hePiHeWords)).prod = 1) ∧
    (hePiAWord.map (hePiLetMat hePiHeWords)).prod = CFSG.Sporadic.He.mA ∧
    (hePiBWord.map (hePiLetMat hePiHeWords)).prod = CFSG.Sporadic.He.mB ∧
    (hePiZWord.map (hePiLetMat hePiHeWords)).prod = heWordMat heT1Letters

end CFSG.ComponentClassification.AS81.HePres.Native

end
