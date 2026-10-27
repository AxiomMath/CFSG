module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFieldFixedLinear
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFieldFixedUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

theorem fixed_equiv {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq2 : 2 < p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (F : Subgroup (slPi π 3 (p ^ f) K))
    (hF : ∀ s : slPi π 3 (p ^ f) K,
      s ∈ F ↔ frobGL σ (s : GL (Fin 3) K) = (s : GL (Fin 3) K)) :
    ∃ (f₀ : ℕ) (K₀ : Type) (_ : Field K₀), f = 3 * f₀ ∧ PiField π p f₀ K₀ ∧
      Nonempty (↥F ≃* slPi π 3 (p ^ f₀) K₀) := by
  cases π
  · exact fixed_equiv_unitary hK hq2 hσ F hF
  · exact fixed_equiv_linear hK hσ F hF

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
