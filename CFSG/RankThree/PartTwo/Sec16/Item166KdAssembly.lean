module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdX
import CFSG.RankThree.PartTwo.Sec16.Item166KdSupp
import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_Kd_data
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} {d : G}
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (hΔ : delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ sSup 𝒳)
    (hinv : Sec14.Ronan148Q.Inv143Q A d d (sSup 𝒳))
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) :
    ∃ Kd ∈ thetaComponentsAt 3 d,
      Kd = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) Kd ∧
      Kd ∈ 𝒳 ∧
      (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
  have hJX : lB A (Subgroup.closure {c, d}) ≤ sSup 𝒳 :=
    lB_le_sSup_of_case2ii h hJ hdA hd1 hdc h𝒳 hΔ hinv htypes
  obtain ⟨Kd, hKd, hKdeq, hKdA6⟩ :=
    exists_Kd_isTripleCover h134 h48 h hΩ hJ hdA hd1 hdc
  have hJK : lB A (Subgroup.closure {c, d}) ≤ Kd := by
    rw [hKdeq]
    exact le_sup_left
  have hLBperf : Group.IsPerfect ↥(lB A (Subgroup.closure {c, d})) := by
    rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have hLBne : lB A (Subgroup.closure {c, d}) ≠ ⊥ := by
    intro hbot
    have hdJ : d ∈ lB A (Subgroup.closure {c, d}) :=
      Ctr166.mem_lB_closure h hJ hdA hd1 hdc
    exact hd1 (Subgroup.mem_bot.mp (hbot ▸ hdJ))
  have hKd𝒳 : Kd ∈ 𝒳 :=
    mem_of_perfect_le_sSup h𝒳 htypes hKd hJK hJX hLBperf hLBne
  exact ⟨Kd, hKd, hKdeq, hKd𝒳,
    htypes.resolve_left (not_isTripleCover_ON_of_mem h𝒳 htypes hKd𝒳 hKdA6)⟩

theorem le_pPrimeCoreOf_sup_of_case2ii {O X : Subgroup G}
    (hOX : O ≤ Subgroup.normalizer (X : Set G))
    (hON : O ⊔ X ≤ Subgroup.normalizer (O : Set G))
    (hO3 : Nat.Coprime 3 (Nat.card O)) :
    O ≤ pPrimeCoreOf 3 (O ⊔ X) ∧
      inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 (O ⊔ X) ∧
      O ⊔ X ≤ Subgroup.normalizer (pPrimeCoreOf 3 (O ⊔ X) : Set G) := by
  refine ⟨Sec14.le_pPrimeCoreOf le_sup_left hON hO3, ?_,
    Sec14.le_normalizer_pPrimeCoreOf 3 (O ⊔ X)⟩
  refine Sec14.le_pPrimeCoreOf ((Sec6.theta_le X).trans le_sup_right) ?_ ?_
  · exact sup_le (hOX.trans (Sec6.normalizer_le_normalizer_theta X))
      (Sec6.le_normalizer_theta X)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Sec6.theta_solvable_and_not_dvd X).2

theorem normalizer_centralizer_facts_of_case2ii {X W Z : Subgroup G}
    {A : Subgroup G} {c d : G} (hA : IsMulCommutative A) (hcA : c ∈ A) (hdA : d ∈ A)
    (hZle : Z ≤ Subgroup.zpowers c) (hWCA : W ≤ Subgroup.centralizer (A : Set G))
    (hinv : Sec14.Ronan148Q.Inv143Q A d d X) :
    Z ≤ Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G) ∧
      Z ≤ Subgroup.normalizer (pPrimeCoreOf 3
        (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X) : Set G) ∧
      W ≤ Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G) ∧
      W ≤ Subgroup.centralizer (Z : Set G) ∧
      lB A (Subgroup.closure {c, d}) ≤ Subgroup.centralizer (Z : Set G) := by
  have hZA : Z ≤ A := hZle.trans (Subgroup.zpowers_le.mpr hcA)
  have hZN : Z ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G) :=
    hZA.trans (hinv.le_normalizer hA hdA)
  refine ⟨hZN, hZN.trans (Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 _),
    hWCA.trans (hinv.centralizer_le hdA), hWCA.trans (Subgroup.centralizer_le hZA), ?_⟩
  have hZleB : Z ≤ Subgroup.closure ({c, d} : Set G) :=
    hZle.trans (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  exact (Sec14.lB_le_centralizer A (Subgroup.closure ({c, d} : Set G))).trans
    (Subgroup.centralizer_le hZleB)

theorem exists_supplement_mod_pPrimeCoreOf
    {J Ob Kd : Subgroup G} {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)))
    (hKd : Kd ∈ thetaComponentsAt 3 d)
    (hKdeq : Kd = J ⊔ inSubgroup (aschbacherSolvableCore 3) Kd)
    (hθOb : inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) ≤ Ob) :
    ∀ x ∈ sSup 𝒳, ∃ j ∈ J, ∃ s ∈ sSup 𝒳, x = j * s ∧
      ∀ l ∈ J, ⁅s, l⁆ ∈ Ob := by
  intro x hx
  obtain ⟨j, hj, s, hs, hxs, hsl⟩ :=
    supplement_of_mem_thetaComponentsAt h𝒳 htypes hKd hKdeq x hx
  exact ⟨j, hj, s, hs, hxs, fun l hl => hθOb (hsl l hl)⟩

end CFSG.RankThree.PartTwo.Sec16.Kd166
