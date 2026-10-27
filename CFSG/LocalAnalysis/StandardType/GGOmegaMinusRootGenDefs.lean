module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesLevi
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot

variable {K : Type} [Field K] {m p : ℕ} {ζ : Kˣ}

variable (m) in
@[expose] noncomputable def omMinusTorusParam (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* (Fin m → Kˣ) :=
  MonoidHom.compLeft (TableBSymp.zmodPowHom hζ) (Fin m)

@[simp] theorem omMinusTorusParam_apply (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p))
    (j : Fin m) : omMinusTorusParam m hζ f j = TableBSymp.zmodPowHom hζ (f j) :=
  rfl

@[expose] noncomputable def omMinusTorusGL (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K :=
  (kOmMDiag K m).comp (omMinusTorusParam m hζ)

theorem omMinusTorusGL_apply (hζ : ζ ^ p = 1) (f : Fin m → Multiplicative (ZMod p)) :
    omMinusTorusGL hζ f = kOmMDiag K m (omMinusTorusParam m hζ f) :=
  rfl

theorem omMinusTorusGL_mem [Finite K] [CharP K 2] (b c : K) (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    omMinusTorusGL hζ f ∈ StatedOmega (StatedQuadMinus (m + 1) K b c) :=
  kOmMDiag_mem b c _

@[expose] noncomputable def omMinusTorus [Finite K] [CharP K 2] (b c : K) (hζ : ζ ^ p = 1) :
    (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadMinus (m + 1) K b c) :=
  (omMinusTorusGL hζ).codRestrict _ (omMinusTorusGL_mem b c hζ)

@[simp] theorem coe_omMinusTorus [Finite K] [CharP K 2] (b c : K) (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    (omMinusTorus b c hζ f : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) =
      omMinusTorusGL hζ f :=
  rfl

variable (K) in
@[expose] noncomputable def omMinusLongBlock (b c : K) (l : Fin m) :
    Subgroup (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :=
  (StatedOmega (StatedQuadMinus 2 K b c)).map
    (F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l))

variable (K) in
@[expose] noncomputable def omMinusShortBlock (i j : Fin m) :
    Subgroup (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :=
  (OmegaPilot.siegelBlockGL K {i, j}).map (F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective)

end CFSG.StandardType

end
