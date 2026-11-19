module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs

@[expose] public section

open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.Quasithin

namespace CFSG.Quasithin.A312He

def HeHatFacts (Y : Subgroup CFSG.Sporadic.He.J) : Prop :=
  ∃ (ol : List CFSG.Sporadic.He.J) (t : CFSG.Sporadic.He.J), A312Words.IdxTwoData Y ol t ∧
    ∃ pf : Fin 6 → Fin 8330, Function.Injective pf ∧
      (∀ g ∈ ol ++ [t], ∀ i, ∃ k, g • pf i = pf k) ∧
      ∃ y1 y2 : CFSG.Sporadic.He.J, y1 ∈ Y ∧ y2 ∈ Y ∧
      (∀ i : Fin 6, y1 • pf i = pf (i + 1)) ∧ (∀ i : Fin 6, y2 • pf i = pf (Equiv.swap 0 1 i)) ∧
      ∃ vl : List CFSG.Sporadic.He.J, (∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ ol}) ∧
        (∀ g ∈ ol ++ [t], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
          g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl}) ∧
        (∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) ∧ (∀ a ∈ vl, a * a = 1) ∧
        (∀ a ∈ vl, ∀ i, a • pf i = pf i) ∧ Nat.card (Subgroup.closure {v | v ∈ vl}) = 64

def HeExtFacts (Y : Subgroup CFSG.Sporadic.He.J) : Prop :=
  ∃ (ol : List CFSG.Sporadic.He.J) (W : Subgroup CFSG.Sporadic.He.J),
    A312Words.IdxTwoData Y ol 1 ∧ W ≤ Y ∧ (∀ g ∈ ol, ∀ v ∈ W, g⁻¹ * v * g ∈ W) ∧
    Nat.card W = 2 ^ 7 ∧ IsExtraspecial2 3 W

end CFSG.Quasithin.A312He

public section

namespace Certificates

end Certificates
