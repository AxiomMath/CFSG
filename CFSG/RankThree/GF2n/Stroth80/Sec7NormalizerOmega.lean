module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.RankThree.GF2n.Stroth80.Hom24Omega
public import CFSG.RankThree.GF2n.Stroth80.Hom24Minus

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.LieType.Universal.Spin
open CFSG.RankThree.GF2n.Smith81.Smith23E1
open CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin

theorem normalizerOmegaFor_plus (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 2 ≤ m) :
    NormalizerOmegaFor K (StatedQuadPlus m K) := by
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  exact normalizerOmegaFor_of_form (coe_quadPlus m K) (nondegenerate_polarBilin_quadPlus m K)
    (natIrredFor_of_form (coe_quadPlus m K) (nondegenerate_polarBilin_quadPlus m K)
      (commutant_scalar_of_linear fun f hf => stroth_2_4_omegaPlus K hK m hm f hf))

theorem normalizerOmegaFor_minus (K : Type) [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NormalizerOmegaFor K (StatedQuadMinus m K b c) := by
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  exact normalizerOmegaFor_of_form (coe_quadMinus m K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (natIrredFor_of_form (coe_quadMinus m K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
      (commutant_scalar_of_linear fun f hf => stroth_2_4_omegaMinus K hm hirr f hf))

end CFSG.RankThree.GF2n.Stroth80
