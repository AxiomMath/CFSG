module

import CFSG.RankThree.PartOne.S10.HyperplaneObstructionPlaneVanishing
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionNormalization
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionTwoLocal
import CFSG.RankThree.GroupTheory.SteinbergBMCentralizerPerfectSupplement
import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergBYAschVanishing
public import CFSG.RankThree.GroupTheory.ThetaComponents

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

theorem ne_bot_of_coe_eq_theta_mul {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {b : G} {X K : Subgroup G} (hX : X ∈ thetaComponentsAt p b)
    (hXK : (X : Set G) = (inSubgroup (aschbacherSolvableCore p) X : Set G) * (K : Set G)) :
    K ≠ ⊥ := by
  rintro rfl
  obtain ⟨u, v, huv⟩ := CFSG.LocalCores.isQuasisimple_nontrivial
    (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hX)
  have h1 : ∀ x : X, x ∈ aschbacherSolvableCore p X := by
    intro x
    have hx : (x : G) ∈ (inSubgroup (aschbacherSolvableCore p) X : Set G) *
        ((⊥ : Subgroup G) : Set G) := hXK ▸ x.2
    obtain ⟨t, ⟨y, hy, hyt⟩, k, hk, htk⟩ := hx
    have hk1 : k = 1 := Subgroup.mem_bot.mp hk
    have htx : t = (x : G) := by simpa [hk1] using htk
    have : y = x := Subtype.ext (hyt.trans htx)
    exact this ▸ hy
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  exact huv (((QuotientGroup.eq_one_iff u').mpr (h1 u')).trans
    ((QuotientGroup.eq_one_iff v').mpr (h1 v')).symm)

theorem exists_perfect_supplement_centralizing_commutator {G : Type} [Group G] [Finite G]
    (he : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hvan : SteinbergBY.AschVanishing G p) {A B W X : Subgroup G} {b : G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) (hBA : B ≤ A)
    (hBcard : Nat.card B = p ^ 2) (hbB : b ∈ B) (hb1 : b ≠ 1) (hX : X ∈ thetaComponentsAt p b)
    (hBX : B ≤ normalizer (X : Set G)) (hXB : ⁅X, B⁆ ≤ inSubgroup (aschbacherSolvableCore p) X)
    (hW2 : IsPGroup 2 W) (hWb : W ≤ Subgroup.centralizer ({b} : Set G))
    (hBW : B ≤ normalizer (W : Set G)) :
    ∃ K : Subgroup G, ⁅K, K⁆ = K ∧ K ≠ ⊥ ∧ K ≤ X ∧
      K ≤ Subgroup.centralizer (⁅W, B⁆ : Subgroup G) ∧ K ≤ Subgroup.centralizer (B : Set G) ∧
      (X : Set G) = (inSubgroup (aschbacherSolvableCore p) X : Set G) * (K : Set G) := by
  have hp2 : p ≠ 2 := by omega
  have hBe : IsElementaryAbelian p B := SteinbergBM.isElementaryAbelian_of_le hAe hBA
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  set R := ⁅W, B⁆ with hR
  have hRW : R ≤ W := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing W B hBW
  have hR2 : IsPGroup 2 R := hW2.to_le hRW
  have hBR : B ≤ normalizer (R : Set G) := normalizer_commutator_ge_right W B
  have hRB : ⁅R, B⁆ = R :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp B W hBp hBW
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_card_of_isPGroup_two hp hp2 hW2))
  have hBb : B ≤ Subgroup.centralizer ({b} : Set G) := fun β hβ =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hBe.is_comm.comm ⟨β, hβ⟩ ⟨b, hbB⟩))
  have hRX : R ≤ normalizer (X : Set G) :=
    commutator_le_normalizer_of_mem_thetaComponentsAt he hp hp3 hX hWb hBb hBp
  have hRθ : ⁅R, X⁆ ≤ inSubgroup (aschbacherSolvableCore p) X :=
    commutator_le_theta_of_commutator_eq_self hBX hRX hRB hXB
  have hθX : inSubgroup (aschbacherSolvableCore p) X ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :=
    (theta_eq_inf_of_mem_thetaComponentsAt hp hX).le.trans inf_le_right
  have hBcent : ∀ T : Subgroup G, T ≤ inSubgroup (aschbacherSolvableCore p) X → IsPGroup 2 T →
      B ≤ normalizer (T : Set G) → T ≤ Subgroup.centralizer (B : Set G) := fun T hT hT2 hBT =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (vanishing_centralizes_plane_invariant_two_subgroups hp hvan hAe hAcard hBA hBcard
        (hBA hbB) hb1 (hT.trans hθX) hT2 hBT)
  have hXperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp (isPerfect_of_mem_thetaComponentsAt hX)
  obtain ⟨hKperf, hKR, hKB, hXK⟩ :=
    SteinbergBM.coprime_two_commutator_centralizer_perfect_supplement hp hp2 hBp hXperf hBX hXB
      hR2 hBR hRB hRX hRθ hBcent
  exact ⟨_, hKperf, ne_bot_of_coe_eq_theta_mul hp hX hXK,
    (Subgroup.map_subtype_le _).trans inf_le_left, hKR, hKB, hXK⟩

end CFSG.RankThree.PartOne.HyperplaneObstruction
