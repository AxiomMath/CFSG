module

public import CFSG.RankThree.PartTwo.KFacts.KS21U58
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48DescentGen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open Matrix
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK)

theorem exists_fixed_orthonormal_eigenbasis
    {g₀ : Matrix (Fin 4) (Fin 4) K} (hg₀ : (g₀.map hK.bar)ᵀ * g₀ = 1)
    {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1)
    (hN : g₀ * g₀.map φ * (g₀.map φ).map φ = 1)
    {p : Matrix (Fin 4) (Fin 4) K} (hp : (p.map hK.bar)ᵀ * p = 1) (hp3 : p ^ 3 = 1)
    (hfix : g₀ * p.map φ = p * g₀) :
    ∃ H : Matrix (Fin 4) (Fin 4) K, (H.map hK.bar)ᵀ * H = 1 ∧ g₀ * H.map φ = H ∧
      ∃ d : Fin 4 → K, (∀ i, d i ^ 3 = 1) ∧ p * H = H * diagonal d :=
  Descent.exists_fixed_orthonormal_eigenbasis_gen hK hg₀ hφ3 hφ1 hN hp hp3 hfix

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
