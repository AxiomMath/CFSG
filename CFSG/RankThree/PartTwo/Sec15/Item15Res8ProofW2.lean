module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofExcl
public import CFSG.RankThree.PartTwo.Sec15.Item152Res2ProofK
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofJ
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsRoute
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof15Res8

theorem mem_comp3In_of_le_delta {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X)
    (hΔ : X = delta A LB X) : X ∈ comp3In (delta A LB M) := by
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXD : X ≤ delta A LB M := hΔ.le.trans (delta_mono hXM)
  refine ⟨Y4Core.mem_thetaComponentsIn_mid hX hXD (delta_le M), ?_⟩
  exact eq_oPrimeResidualOf_of_le (isPerfect_of_mem_thetaComponentsIn hX)
    (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hYX hY.2.1 (isPerfect_of_mem_scriptY4 hY)
    (ne_bot_of_mem_scriptY4 hY)

theorem false_of_ctx152 (hE : Y4CoreMemExclR) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    {Y M X : Subgroup G} (hctx : Ctx152 A (lB A) Y M X) : False := by
  apply hctx.not_quasi
  refine hE G A c L h M hctx.mem_y2 hctx.fstar X
    (mem_comp3In_of_le_delta hctx.mem_y4 hctx.mem_comp hctx.le_x hctx.delta_x) hctx.norm_x
    hctx.mem_comp hctx.delta_x ?_
  rcases hctx.sl25 with h2 | h3
  · exact Or.inl h2
  · exact Or.inr (Or.inl ⟨5, by norm_num, by norm_num, h3⟩)

end Proof15Res8

open Proof15Res8

theorem step152ConfKNR_of_memExcl (hE : Y4CoreMemExclR) : Step152ConfKNR := by
  intro G _ _ A c L h Y M X c' L' p P T hpt
  exact (false_of_ctx152 hE h hpt.ctx).elim

theorem step152ConfWdR_of_memExcl (hE : Y4CoreMemExclR) : Step152ConfWdR := by
  intro G _ _ A c L h Y M X c' L' d p P T K S hpt
  exact (false_of_ctx152 hE h hpt.ctx).elim

section Excl

theorem step152ConfKNR_of_excl (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hSL25 : Y4CoreExclSL25HJR) : Step152ConfKNR :=
  step152ConfKNR_of_memExcl (y4CoreMemExclR_of h134 h48 h148 hSL25)

theorem step152ConfWdR_of_excl (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (hSL25 : Y4CoreExclSL25HJR) : Step152ConfWdR :=
  step152ConfWdR_of_memExcl (y4CoreMemExclR_of h134 h48 h148 hSL25)

end Excl

theorem rank3II_15_2_of_memExcl
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hcomp : Step152Comp A (lB A)) (hE : Y4CoreMemExclR) : Item152 A (lB A) := by
  intro Y hY M hM hYM hF
  obtain ⟨X, hX, hYX, hΔ⟩ := hcomp Y hY M hM hYM hF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  refine ⟨X, hX, hYX, mem_scriptY0_of_isQuasisimple hY hM hF hX hYX hAX hΔ ?_⟩
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h' => hM.1.1 (top_le_iff.mp (h' ▸ hXM))
  have hX1 : X ≠ ⊥ := fun h' => ne_bot_of_mem_scriptY4 hY (le_bot_iff.mp (h' ▸ hYX))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2 : CFSG.pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hX)
  have hS4 : SectionFourHyp ↥X := h.toTheoremFourHyp.sectionFourHyp hXtop
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X
  set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ)
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have hKsimp : IsSimpleGroup (↥X ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (↥X ⧸ θ))).isSimpleGroup
  have hex := hE G A c L h M hM hF X (mem_comp3In_of_le_delta hY hX hYX hΔ) hAX hX hΔ
  rcases Sec4.item4_4OTwo_holds ↥X hS4 hXp K hKs hKsimp hO2 with h1 | h2 | h3 | h4
  · exact h1
  · exact hex (Or.inl h2)
  · exact hex (Or.inr (Or.inl h3))
  · exact hex (Or.inr (Or.inr h4))

theorem item152R_of_memExcl
    (hcomp : Step152CompR) (hE : Y4CoreMemExclR) : Item152R :=
  fun G _ _ A c L hR => rank3II_15_2_of_memExcl hR (hcomp G A c L hR) hE

theorem item152R_of_compJ_excl
    (h149 : Sec16.Item149S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) (hJ : Step152CompJNTR)
    (hSL25 : Y4CoreExclSL25HJR) : Item152R :=
  item152R_of_memExcl (step152CompR_of' h149 h148 h134 h48 h415 hSz
    (step152CompJR_of h134 h48 h415 hJ)) (y4CoreMemExclR_of h134 h48 h148 hSL25)

end CFSG.RankThree.PartTwo.Sec15
