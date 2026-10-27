module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwo
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSL
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ZeroBlockCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.GroupTheory.WielandtProduct
open scoped commutatorElement

theorem ggHasLabel_of_mulEquiv_specialLinear {X : Type} [Group X] {J : Subgroup X}
    {K : Type} [Field K] [Finite K] {k f : ℕ}
    (hk : 2 ≤ k) (hK : Nat.card K = 2 ^ f)
    (hne2 : (k, 2 ^ f) ≠ (2, 2)) (hne3 : (k, 2 ^ f) ≠ (2, 3))
    (e : Matrix.SpecialLinearGroup (Fin k) K ≃* J) :
    GGHasLabel ⟨.A, k - 1, f⟩ (J ⧸ Subgroup.center J) := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have h1 := Finite.one_lt_card (α := K)
    omega
  have hkmodel : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
  let e'' : Matrix.SpecialLinearGroup (Fin ((k - 1) + 1)) K ≃* J := by
    rw [hkmodel]
    exact e
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin ((k - 1) + 1)) K ≃*
      (J ⧸ Subgroup.center J) :=
    QuotientGroup.congr _ _ e'' (Subgroup.map_center_eq e'')
  have hmodel : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL (k - 1 + 1) 2 f := by
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_, ?_⟩, K, inferInstance, inferInstance, ?_, ?_⟩
    · rw [hkmodel]
      exact hne2
    · rw [hkmodel]
      exact hne3
    · exact hK
    · exact ⟨e'.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj ((k - 1) + 1) K)⟩
  exact ggHasLabel_typeA (n := k - 1) (f := f) hmodel

end CFSG.StandardType
end
