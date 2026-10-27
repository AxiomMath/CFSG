module

public import CFSG.Sporadic.Co2I301.Spec
public import CFSG.Sporadic.Co2I301.SpecSixAux

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271


theorem six_facts (c₁ c₂ c₃ : locC) (h₁ : (c₁ : Equiv.Perm (Fin 2300)) = k1P)
    (h₂ : (c₂ : Equiv.Perm (Fin 2300)) = k2P) (h₃ : (c₃ : Equiv.Perm (Fin 2300)) = dP) :
    ∀ g ∈ Subgroup.closure {π | ∃ i < 2, sixPi i = π}, g * g = 1 → g ≠ 1 →
      ∃ w ∈ hlWords, ¬ Commute g
        (wordVal [toPerm63 (sixAction c₁), toPerm63 (sixAction c₂), toPerm63 (sixAction c₃)] w *
          g * (wordVal [toPerm63 (sixAction c₁), toPerm63 (sixAction c₂),
            toPerm63 (sixAction c₃)] w)⁻¹) :=
  six_facts_of_cols c₁ c₂ c₃ h₁ h₂ h₃

end CFSG.Sporadic.Co2I301
