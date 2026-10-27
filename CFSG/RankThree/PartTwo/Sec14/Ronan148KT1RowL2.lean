module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem rowOf143_psl2 (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    RowOf143 (CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p e)) := by
  intro S _ _ hS hnc hφ _
  obtain ⟨φ⟩ := hφ
  obtain ⟨ψ⟩ : Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p e)) :=
    ⟨φ.trans (Sec4.projSLEquivPSLn 2 (GaloisField p e))⟩
  refine row143_of_inner hS hnc ?_ ?_
  ·
    intro P _ hPperf _
    have hPP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hPperf
    have hle : ⁅P, P⁆ ≤ (MulAut.conj : S →* MulAut S).range :=
      Subgroup.commutator_le.mpr fun g _ h _ =>
        CFSG.RankThree.PartTwo.KFacts.isInnerAut_commutator_of_mulEquiv_psl2_all
          (K := GaloisField p e) ψ g h
    exact hPP.symm.le.trans hle
  ·
    intro β _ Y _ _ hYperf hY3
    have hYsol : Group.IsSolvable ↥Y := by
      have e' : Y ≃* Y.map ψ.toMonoidHom := Y.equivMapOfInjective ψ.toMonoidHom ψ.injective
      have hcard : Nat.card ↥(Y.map ψ.toMonoidHom) = Nat.card ↥Y :=
        (Nat.card_congr e'.toEquiv).symm
      have hsolH : Group.IsSolvable ↥(Y.map ψ.toMonoidHom) :=
        CFSG.RankThree.PartTwo.Sec6.BThreeCensus.isSolvable_of_not_three_dvd_psl2
          (GaloisField.card p e (by omega)) _ (by rw [hcard]; exact hY3)
      exact Group.isSolvable_of_surjective (f := e'.symm.toMonoidHom) e'.symm.surjective
    exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable hYperf hYsol

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
