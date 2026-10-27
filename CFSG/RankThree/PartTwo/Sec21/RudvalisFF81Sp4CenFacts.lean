module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenDefs
public import Certificates.Data.RudvalisFF81Sp4CenGL6
public import CFSG.Quasithin.H13.L32NMatNGen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open CFSG.Quasithin.H13.MatNCert Matrix

@[expose] def Sp4CenFacts : Prop :=
  Nat.card (genSubN 4 sbGens4) = 720 ∧
  (∀ g : GL4, g ∈ genSubN 4 sbGens4 ↔ (g : M4)ᵀ * decN 4 w0c4 * (g : M4) = decN 4 w0c4) ∧
  (∀ Z : Subgroup GL4, genSubN 4 sbGens4 ≤ Z → Z = genSubN 4 sbGens4 ∨ Z = ⊤) ∧
  (∀ ψ : Equiv.Perm (Fin 6) →* GL4, ψ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 →
    ∃ c : GL4, ψ.range = (genSubN 4 sbGens4).map (MulAut.conj c).toMonoidHom) ∧
  ∃ F X : GL4, orderOf F = 5 ∧ orderOf X = 3 ∧ F * X = X * F

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
