module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj

public section

open CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.RF4 CFSG.RankThree.QuadraticSL2
  CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec8.HeringD4

theorem g2ThreeConjSL2Minus_all
    (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K ∨
      g * z * g⁻¹ ∈ KS11Lie4Proof.g2LongSL2 K := by
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  have : Finite K₂ := (quadratic_frobenius hdeg σ hσ).1
  obtain ⟨M⟩ := KS11Lie7Proof.nonempty_qPlusModel hdeg hσ
  exact KS11Lie7Proof.exists_conj_short_or_long M hdeg hσ h3 hz3 hz1

end CFSG.RankThree.PartTwo.Sec8.HeringD4
