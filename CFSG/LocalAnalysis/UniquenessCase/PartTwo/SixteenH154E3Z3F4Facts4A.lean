module

public import CFSG.LinearAlgebra.PrimeOrderIrreducible
public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.RepresentationTheory

private theorem s16h_e3_z3_card_omegaField : Nat.card OmegaField = 4 := by
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
  norm_num

theorem s16h_e3_z3_card_gl :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) OmegaField) = 181440 := by
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  haveI : Fintype OmegaField := Fintype.ofFinite OmegaField
  rw [Matrix.card_GL_field]
  have hcardFieldF : Fintype.card OmegaField = 4 := by
    rw [← Nat.card_eq_fintype_card, s16h_e3_z3_card_omegaField]
  rw [hcardFieldF, Fin.prod_univ_three]
  norm_num

theorem s16h_e3_z3_irreducible_of_card_seven
    (Q : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField)) (hQ : Nat.card Q = 7) :
    IsIrreducibleMatrixRep Q.subtype := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 7 (by rw [hQ])
  have huord : orderOf (q : Matrix.GeneralLinearGroup (Fin 3) OmegaField) = 7 := by
    rw [Subgroup.orderOf_coe, hq]
  have hgen : Subgroup.zpowers (q : Matrix.GeneralLinearGroup (Fin 3) OmegaField) ≤ Q :=
    Subgroup.zpowers_le.mpr q.2
  intro W hW
  refine isIrreducibleMatrixRep_zpowers_of_orderOf_eq_seven s16h_e3_z3_card_omegaField huord W ?_
  intro g w hw
  simpa using hW ⟨g, hgen g.2⟩ w hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
