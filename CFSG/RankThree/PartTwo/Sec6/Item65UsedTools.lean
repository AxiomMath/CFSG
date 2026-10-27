module

public import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LieType.CurtisTits.Recognition
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

theorem subnormal_le_center_or_eq_top_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : IsQuasisimple Q) {N : Subgroup Q} (hN : N.IsSubnormal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  rcases hN.lt_normal with htop | ⟨K, hKn, hNK, hKlt⟩
  · exact Or.inr htop
  · have := hKn
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ K with hKc | hKtop
    · exact Or.inl (hNK.trans hKc)
    · exact absurd hKtop hKlt.ne

variable {G : Type} [Group G] [Finite G]

theorem commutator_theta_le_of_mem_thetaQuotCentralizer {X Y : Subgroup G} {b : G}
    (hXq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X)) (hb3 : b ^ 3 = 1)
    (hbC : b ∈ thetaQuotCentralizer X) (hYXC : Y ≤ X ⊓ Subgroup.centralizer {b})
    (hYsn : (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have hYX : Y ≤ X := hYXC.trans inf_le_left
  set θX := aschbacherSolvableCore 3 X with hθX
  set π := QuotientGroup.mk' θX with hπ
  set W := X ⊓ Subgroup.centralizer ({b} : Set G) with hW
  have hWX : W ≤ X := inf_le_left
  set ρ : W →* X ⧸ θX := π.comp (Subgroup.inclusion hWX) with hρ
  have hρs : Function.Surjective ρ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θX q
    have hx : (x : G) ∈ (W : Set G) * (inSubgroup (aschbacherSolvableCore 3) X : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right W _
        (hWX.trans (le_normalizer_theta X))]
      exact le_inf_centralizer_sup_theta hbC hb3 x.2
    obtain ⟨w, hw, t, ht, hwt⟩ := hx
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' θX (Subgroup.inclusion hWX ⟨w, hw⟩) = QuotientGroup.mk' θX x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hWX ⟨w, hw⟩)⁻¹ * x = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hwt]
      simp
    rw [this]
    exact ht'
  set Yb := (Y.subgroupOf W).map ρ with hYb
  have hYbsn : Yb.IsSubnormal := hYsn.map hρs
  have hθYX : inSubgroup (aschbacherSolvableCore 3) Y ≤ X := (theta_le Y).trans hYX
  have hcen : ∀ t : inSubgroup (aschbacherSolvableCore 3) Y,
      π (Subgroup.inclusion hθYX t) ∈ Subgroup.center (X ⧸ θX) := by
    rcases subnormal_le_center_or_eq_top_of_isQuasisimple hXq hYbsn with hc | htop
    · intro t
      apply hc
      exact ⟨⟨t, hYXC (theta_le Y t.2)⟩, Subgroup.mem_subgroupOf.mpr (theta_le Y t.2), rfl⟩
    · set f : inSubgroup (aschbacherSolvableCore 3) Y →* X ⧸ θX :=
        π.comp (Subgroup.inclusion hθYX) with hf
      have hn : f.range.Normal := ⟨fun n hn g => by
        obtain ⟨t, rfl⟩ := hn
        have hg : g ∈ Yb := by
          rw [htop]
          exact Subgroup.mem_top g
        obtain ⟨w, hwY, rfl⟩ := hg
        have hwY' : (w : G) ∈ Y := Subgroup.mem_subgroupOf.mp hwY
        have hmem : (w : G) * t * (w : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta Y hwY') t).mp t.2
        refine ⟨⟨_, hmem⟩, ?_⟩
        change π (Subgroup.inclusion hθYX ⟨_, hmem⟩) = π (Subgroup.inclusion hWX w) *
          π (Subgroup.inclusion hθYX t) * (π (Subgroup.inclusion hWX w))⁻¹
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl⟩
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hXq f.range with
        hc | htop'
      · intro t
        exact hc ⟨t, rfl⟩
      · exfalso
        have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp htop'
        have := (theta_solvable_and_not_dvd Y).1
        have hsol : Group.IsSolvable (X ⧸ θX) := Group.isSolvable_of_surjective hsurj
        have : Nontrivial (X ⧸ θX) := CFSG.LocalCores.isQuasisimple_nontrivial hXq
        have := hXq.1
        exact Group.IsPerfect.not_isSolvable (X ⧸ θX) hsol
  rw [Subgroup.commutator_le]
  intro t ht y hy
  have htX : t ∈ X := hθYX ht
  have hyX : y ∈ X := hYX hy
  refine ⟨⁅(⟨t, htX⟩ : X), (⟨y, hyX⟩ : X)⁆, ?_, rfl⟩
  rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
    map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (hcen ⟨t, ht⟩) _).symm

end CFSG.RankThree.PartTwo.Sec6
