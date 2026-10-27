module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Res
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Lift
import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Main
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Core

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def PZeroLiftData {G : Type} [Group G] [Finite G] (L : Subgroup G) (y : G) : Prop :=
  ∃ hyN : y ∈ Subgroup.normalizer (L : Set G),
    Ronan138P5.rho L ⟨y, hyN⟩ ≠ 1 ∧
    (∃ V : Subgroup (L ⧸ aschbacherSolvableCore 3 L), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ v ∈ V, Ronan138P5.rho L ⟨y, hyN⟩ v ∈ V) ∧
    ∃ d : L ⧸ aschbacherSolvableCore 3 L, d ^ 3 = 1 ∧ Ronan138P5.rho L ⟨y, hyN⟩ d = d ∧
      ∀ k : ℕ, Ronan138P5.rho L ⟨y, hyN⟩ ^ k ≠ MulAut.conj d

section Kinds

@[expose] def Step13PZeroEFLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L P₀ : Subgroup G) (n : ℕ),
    PZeroU3 G A c L P₀ n → ∀ x ∈ P₀, x ∉ Subgroup.zpowers c → ∀ Lx ∈ thetaComponentsAt 3 x,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Lx →
      c ∈ Subgroup.normalizer (Lx : Set G) →
      (KFacts.InducesStdKind Lx c .field ∨ KFacts.InducesStdKind Lx c .graphField) →
        ∃ y ∈ Lx ⊓ Subgroup.centralizer ({c} : Set G), y ^ 3 = 1 ∧ PZeroLiftData L y

end Kinds

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)
open Matrix
open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

section Core

theorem step13PZeroCore_of_lift (hK : K13PZeroElem) (hS : Step13PZeroS) (hLx : Step13PZeroLx)
    (h419 : Step13PZero419) (hEF : Step13PZeroEFLift) : Step13PZeroCore := by
  intro G _ _ A c L h hL3 P₀ hcP hP₀L hP₀e hP₀9
  have hEFeq : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hLc := h.le_centralizer
  have hc := h.orderOf_eq
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hZ := center_eq_bot_of_isLThreePi hLq hL3
  rcases hK _ hL3 hLq with ⟨j, d, hj3, hj1, hd3, hjd, hdj, V, hV, hV2, hjV⟩ |
      ⟨n, hn, hn1, hn3, hiso⟩
  · exact false_of_inner hEFeq hLc hc hcP hP₀L hP₀e hP₀9 hZ hj3 hj1 hd3 hjd hdj hV hV2 hjV
  · have hU : PZeroU3 G A c L P₀ n := ⟨h, hn, hn1, hn3, hiso, hcP, hP₀L, hP₀e, hP₀9⟩
    obtain ⟨S₀, hS₀, hS₀2, hS₀le, hS₀θ, x, hxP, hxc, hSne⟩ := hS G A c L P₀ n hU
    obtain ⟨Lx, hLxθ, hJ, hcN, hcC⟩ :=
      hLx G A c L P₀ n hU S₀ hS₀ hS₀2 hS₀le hS₀θ x hxP hxc hSne
    have hkind := h419 G A c L P₀ n hU x hxP hxc Lx hLxθ hJ hcN hcC
    obtain ⟨y, hy, hy3, hyN, hy1, ⟨W, hW, hW2, hyW⟩, d, hd3, hyd, hdn⟩ :=
      hEF G A c L P₀ n hU x hxP hxc Lx hLxθ hJ hcN hkind
    have hyx : y * x = x * y :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (Sec6.le_centralizer_of_mem_thetaComponentsAt hLxθ hy.1))
    have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyP : ∀ p ∈ P₀, p * y = y * p := fun p hp =>
      (forall_commute_of_commute hP₀e hP₀9 hc hcP hxP hxc hyc hyx p hp).symm
    exact false_of_lift hEFeq hLc hc hcP hP₀L hP₀e hP₀9 hyP hyN hy3 hy1 hW hW2 hyW hd3 hyd hdn

end Core

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
