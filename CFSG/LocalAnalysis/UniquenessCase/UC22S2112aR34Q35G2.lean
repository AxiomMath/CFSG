module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35G2Fitting
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35G2Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35G2Parabolic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel CFSG.GroupTheory


theorem adjoint_g2_five_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 5) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hodd : Nat.card K % 2 = 1 := by rw [hK]
  have hn : (Nat.card K ^ 2 - 1).factorization 2 = 2 + 1 := by
    rw [hK, show (5 ^ 2 - 1 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  obtain ⟨T, A, a, t, y, hT⟩ := exists_sylow_shapeConds_adjointG2 K hodd 2 hn
  obtain ⟨eT⟩ := ShapeConds.nonempty_mulEquiv_shapeGrp hT
  intro P H hPH hH
  have hcardP : Nat.card P = 64 := by
    calc Nat.card P = Nat.card T := Nat.card_congr (Sylow.equiv P T).toEquiv
      _ = Nat.card (ShapeGrp 2) := (Nat.card_congr eT.toEquiv).symm
      _ = 64 := by rw [card_shapeGrp]; norm_num
  refine isPGroup_of_sylow_le_of_normal_mulAut (p := 2) (q := 5) (by norm_num) P H hPH hH
    ?_ ?_
  · intro E hE
    let eP : P ≃* ShapeGrp 2 := (Sylow.equiv P T).trans eT.symm
    let E' : Subgroup (ShapeGrp 2) := E.map eP.toMonoidHom
    have hE' : E'.Normal := hE.map eP.toMonoidHom eP.surjective
    have h5 := normal_mulAut_five_free_shape E' hE'
    have hcard : Nat.card (MulAut E) = Nat.card (MulAut E') :=
      Nat.card_congr (MulAut.congr (Subgroup.equivMapOfInjective E eP.toMonoidHom
        eP.injective)).toEquiv
    rwa [hcard]
  · intro U hU hU5 hPU
    have hdvd : 64 ∣ Nat.card (Subgroup.normalizer (U : Set (adjointGroup .G2 K))) := by
      rw [← hcardP]
      exact Subgroup.card_dvd_of_le hPU
    exact normalizer_five_not_dvd_sixtyFour hK U hU hU5 hdvd

theorem g2_five_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 5) :
    CFSG.GroupTheory.SylowPQMaximal 2 5 (CFSG.Blueprint.AdjointQuotient .G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcen := center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let e : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) ≃*
      CFSG.Blueprint.AdjointQuotient .G2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  exact SylowPQMaximal.of_mulEquiv e (adjoint_g2_five_sylowPQMaximal hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2
