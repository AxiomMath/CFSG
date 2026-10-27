module

public import CFSG.Quasithin.H13.NQBlockCcommFittingCores
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_prime_pCore_bar2_not_isCyclic {M : Subgroup G}
    (hF : ¬ IsCyclic ↥(CFSG.fittingSubgroup (Bar2 M))) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ¬ IsCyclic ↥(CFSG.pCore q (Bar2 M)) := by
  classical
  obtain ⟨q, hq, P, hPnc⟩ :
      ∃ q : ℕ, q.Prime ∧
        ∃ P : Sylow q ↥(CFSG.fittingSubgroup (Bar2 M)), ¬ IsCyclic ↥P := by
    by_contra h
    push Not at h
    have hZ : IsZGroup ↥(CFSG.fittingSubgroup (Bar2 M)) :=
      IsZGroup.mk fun p hp P => h p hp P
    letI : IsZGroup ↥(CFSG.fittingSubgroup (Bar2 M)) := hZ
    letI : Group.IsNilpotent ↥(CFSG.fittingSubgroup (Bar2 M)) :=
      CFSG.fittingSubgroup_nilpotent
    exact hF (inferInstance : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 M)))
  haveI : Fact q.Prime := ⟨hq⟩
  have hP'nc : ¬ IsCyclic ↥((P : Subgroup ↥(CFSG.fittingSubgroup (Bar2 M))).map
      (CFSG.fittingSubgroup (Bar2 M)).subtype) := by
    intro hcyc
    exact hPnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥(CFSG.fittingSubgroup (Bar2 M)))
        (CFSG.fittingSubgroup (Bar2 M)).subtype
        (CFSG.fittingSubgroup (Bar2 M)).subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥(CFSG.fittingSubgroup (Bar2 M)))
        (CFSG.fittingSubgroup (Bar2 M)).subtype
        (CFSG.fittingSubgroup (Bar2 M)).subtype_injective).symm.surjective)
  have hP'eq : (P : Subgroup ↥(CFSG.fittingSubgroup (Bar2 M))).map
        (CFSG.fittingSubgroup (Bar2 M)).subtype = CFSG.pCore q (Bar2 M) :=
    CFSG.Quasithin.H13.NQBlock.sylow_fitting_map_eq_pCore P
  have hQnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 M)) := hP'eq ▸ hP'nc
  refine ⟨q, hq, ?_, hQnc⟩
  intro hq2
  exact hP'nc (by
    rw [hP'eq, hq2, uc22p20c_pCore_quotient_pCore (H := ↥M) (p := 2)]
    exact isCyclic_of_subsingleton)

end CFSG.LocalAnalysis.UniquenessCase.UC22
