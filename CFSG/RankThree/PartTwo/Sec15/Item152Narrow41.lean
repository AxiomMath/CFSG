module

public import CFSG.RankThree.PartTwo.Sec15.Item15No135
public import CFSG.RankThree.PartTwo.Sec4.Item44Narrow41
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_or_isSL25Case_narrow {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hG : TheoremFourHyp G) (h44 : Sec4.Item4_4OTwo) (hexcl : Step152Excl A LB)
    {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hM : M ∈ scriptY2 A) (hYM : Y ≤ M)
    (hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M) (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X)
    (hΔ : X = delta A LB X) :
    IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) ∨ IsSL25Case X := by
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h => hM.1.1 (top_le_iff.mp (h ▸ hXM))
  have hS4 : SectionFourHyp ↥X := hG.sectionFourHyp hXtop
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X
  set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have hKsimp : IsSimpleGroup (↥X ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (↥X ⧸ θ))).isSimpleGroup
  have hX1 : X ≠ ⊥ := fun h => ne_bot_of_mem_scriptY4 hY (le_bot_iff.mp (h ▸ hYX))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2 : CFSG.pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hX)
  rcases h44 ↥X hS4 hXp K hKs hKsimp hO2 with h1 | h2 | ⟨p, hp, hp3, hφ⟩ | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rcases Nat.lt_or_ge 5 p with hp5 | hp5
    · exact Or.inl (hexcl Y hY M hM hYM hF X hX hYX hΔ (Or.inl ⟨p, hp, hp5, hφ⟩))
    · obtain rfl : p = 5 := by
        have h45 : p = 4 ∨ p = 5 := by omega
        rcases h45 with rfl | rfl
        · exact absurd hp (by norm_num)
        · rfl
      exact Or.inr (Or.inr hφ)
  · exact Or.inl (hexcl Y hY M hM hYM hF X hX hYX hΔ (Or.inr h4))

theorem rank3II_15_2_narrow
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h1411 : Item1411_1 A (lB A))
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : StellmacherKP) (hcomp : Step152Comp A (lB A))
    (hexcl : Step152Excl A (lB A)) (hconf : Step152Conf A (lB A)) (hgen : KS152HJGen)
    (hend : Step152End A (lB A)) : Item152 A (lB A) := by
  intro Y hY M hM hYM hF
  obtain ⟨X, hX, hYX, hΔ⟩ := hcomp Y hY M hM hYM hF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  by_cases hq : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)
  · exact ⟨X, hX, hYX, mem_scriptY0_of_isQuasisimple hY hM hF hX hYX hAX hΔ hq⟩
  ·
    exfalso
    have hsl := (isQuasisimple_or_isSL25Case_narrow h.toTheoremFourHyp Sec4.item4_4OTwo_holds hexcl
      hY hM hYM hF hX hYX hΔ).resolve_left hq
    have hctx : Ctx152 A (lB A) Y M X := ⟨hY, hM, hYM, hF, hX, hYX, hAX, hΔ, hsl, hq⟩
    obtain ⟨c', hc', hdec, L', hL', hJ⟩ := exists_hj_of_sl25' h h148 h134 h48 h415 hctx
    obtain ⟨d, p, P, T, K, S, hD⟩ := hconf Y M X hctx c' L' hc' hL' hJ hdec
    have hSG := hD.mem_scriptQPiStar_top hst h.isSimpleGroup
    have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hD.norm_w h1411 hSG
    have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hD.omega, mem_lA := hD.mem_lA }
    exact hend Y M X hctx c' L' d p P T K S hD hSH
      (hgen G A c' L' h' Y M X hctx d p P T K S hD hSH)

theorem item152R_narrow
    (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : CFSG.RankThree.PartTwo.StellmacherKP) (hcomp : Step152CompR)
    (hexcl : Step152ExclR) (hconf : Step152ConfR) (hgen : KS152HJGen) (hend : Step152EndR) :
    Item152R :=
  fun G _ _ A c L hR => rank3II_15_2_narrow hR.toSec14Std (h148 G A c L hR) (h1411 G A c L hR)
    h134 h48 h415 hst (hcomp G A c L hR) (hexcl G A c L hR) (hconf G A c L hR) hgen
    (hend G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
