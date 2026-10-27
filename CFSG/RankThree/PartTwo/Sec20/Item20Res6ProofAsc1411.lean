module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res6

@[expose] noncomputable def su3 (p f : ℕ) [Fact p.Prime] :
    Subgroup (GL (Fin 3) (GaloisField p (2 * f))) :=
  Subgroup.closure {A : GL (Fin 3) (GaloisField p (2 * f)) |
    Matrix.GeneralLinearGroup.det A = 1 ∧
    Matrix.transpose ((A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))).map (· ^ (p ^ f))) *
      (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))) = 1}

end Res6

@[expose] def Hyp1411 (X : Type) [Group X] [Finite X] (L S : Subgroup X) : Prop :=
  CFSG.generalizedFitting X = CFSG.pCore 2 X ∧ L.Normal ∧ ⁅L, L⁆ = L ∧
    CFSG.generalizedFitting (X ⧸ CFSG.pPrimeCore 3 X) =
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ∧
    IsPGroup 2 S ∧ CFSG.pCore 2 X ≤ S ∧ S ⊔ L = ⊤ ∧
    ∀ H : Subgroup X, CFSG.pCore 2 X ≤ H → H ⊔ CFSG.pPrimeCore 3 X = ⊤ → H = ⊤

theorem Res6.exists_mem_inter_of_ne {i₁ i₂ i j : Fin 4} (h12 : i₁ ≠ i₂) (h1 : i₁ ≠ 3)
    (h2 : i₂ ≠ 3) (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3) :
    ∃ k : Fin 4, (k = i₁ ∨ k = i₂) ∧ (k = i ∨ k = j) := by
  revert i₁ i₂ i j
  decide

end CFSG.RankThree.PartTwo.Sec20
