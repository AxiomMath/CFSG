module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms

variable {G : Type} [Group G]

@[reducible, expose] def Qbar (p : ℕ) (X : Subgroup G) : Type :=
  (↥X ⧸ aschbacherSolvableCore p ↥X) ⧸ Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)

@[expose] noncomputable def qbarAction (p : ℕ) (X : Subgroup G) :
    ↥(Subgroup.normalizer (X : Set G)) →* MulAut (Qbar p X) :=
  (centerQuotientHom (↥X ⧸ aschbacherSolvableCore p ↥X)).comp (thetaQuotientConj p X)

theorem qbarAction_eq_one_iff (p : ℕ) (X : Subgroup G)
    (hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore p ↥X))
    (m : ↥(Subgroup.normalizer (X : Set G))) :
    qbarAction p X m = 1 ↔
      ∀ k ∈ X, (m : G) * k * (m : G)⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) X := by
  rw [← thetaQuotientConj_eq_one_iff]
  unfold qbarAction
  rw [MonoidHom.comp_apply]
  exact map_eq_one_iff _ (centerQuotientHom_injective _)

theorem thetaQuotientConj_of_mem (p : ℕ) (X : Subgroup G) (y : G) (hy : y ∈ X) :
    thetaQuotientConj p X ⟨y, Subgroup.le_normalizer hy⟩ =
      MulAut.conj ((QuotientGroup.mk (⟨y, hy⟩ : ↥X) : ↥X ⧸ aschbacherSolvableCore p ↥X)) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [thetaQuotientConj_mk, MulAut.conj_apply]
    apply congrArg (QuotientGroup.mk : ↥X → ↥X ⧸ aschbacherSolvableCore p ↥X)
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem qbarAction_of_mem (p : ℕ) (X : Subgroup G) (y : G) (hy : y ∈ X) :
    qbarAction p X ⟨y, Subgroup.le_normalizer hy⟩ =
      MulAut.conj ((QuotientGroup.mk' (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)))
        (QuotientGroup.mk (⟨y, hy⟩ : ↥X))) := by
  unfold qbarAction
  rw [MonoidHom.comp_apply, thetaQuotientConj_of_mem p X y hy]
  exact centerQuotient_conj _

theorem map_qbarAction_eq_inner (p : ℕ) (X : Subgroup G) :
    (X.subgroupOf (Subgroup.normalizer (X : Set G))).map (qbarAction p X) = inner (Qbar p X) := by
  ext φ
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmX : (m : G) ∈ X := hm
    have : m = ⟨(m : G), Subgroup.le_normalizer hmX⟩ := rfl
    rw [this, qbarAction_of_mem p X (m : G) hmX]
    exact ⟨_, rfl⟩
  · rintro ⟨qb, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ qb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨(y : G), Subgroup.le_normalizer y.2⟩, y.2, ?_⟩
    rw [qbarAction_of_mem p X (y : G) y.2]

end CFSG.RankThree.PartOne.K159F
