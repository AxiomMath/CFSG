module

public import CFSG.LocalAnalysis.UniqueFourCatalog.ClosureTop
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureLinear
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem closureTop_of_SL_quotient {G : Type} [Group G] {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (φ : Matrix.SpecialLinearGroup (Fin n) K →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) : ClosureTop G :=
  closureTop_of_lift φ hφ hc
    (fun z hz h2 => CFSG.LocalAnalysis.RankThreeUC.center_noInvolution z (hc hz) h2)
    (fun E P hE hP hP2 hEP =>
      CFSG.LocalAnalysis.RankThreeUC.SLClosure.twoLocalClosure_eq_top_of_normalizes
        E P hE hP hP2 hEP)

theorem closureTop_of_PSL {G : Type} [Group G] {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K) : ClosureTop G :=
  closureTop_of_SL_quotient
    (e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) (by
      intro z hz
      have h1 : e.symm (QuotientGroup.mk z : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = 1 :=
        MonoidHom.mem_ker.mp hz
      have h2 : (QuotientGroup.mk z : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = 1 :=
        (map_eq_one_iff _ e.symm.injective).mp h1
      exact (QuotientGroup.eq_one_iff z).mp h2)

theorem not_uniqueFour_of_statedPSL {G : Type} [Group G] [Finite G] (hS : Standing4 G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n 2 f) : ¬ uniqueFourUnique G := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.RankThreeUC.charP_two_of_card hcard
  exact not_uniqueFour_of_closureTop hS
    (closureTop_of_PSL
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm))

end CFSG.LocalAnalysis.UniqueFourCatalog
