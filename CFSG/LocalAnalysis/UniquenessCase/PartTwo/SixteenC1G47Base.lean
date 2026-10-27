module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure G47Ctx (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (x : IntMod V hV) : Prop where
  sect : Sect16 D V₀ V L hV
  caseOne : Case167_1 D V₀ V hV L
  setup : Setup1645 D V hV x
  sing : ∀ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
    Q (mkTil V₀ V hV x) = 0
  sylow : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G))
  e16 : IsE16A5 ↥(barSub V₀ V hV (xInf L x.val))
  rank3 : CFSG.Open.pRank 3 (centralizer ({x.val} : Set G)) = 1
  rankq : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (centralizer ({x.val} : Set G)) ≤ 2

theorem G47Ctx.of_l45b {D : Data G} (h : R16_45b D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L)
    {x : IntMod V hV} (hx : Setup1645 D V hV x) : G47Ctx D V₀ V L hV x := by
  obtain ⟨hsing, hsyl, he16, h3, hq⟩ := h V₀ V L hV hS hc x hx
  exact ⟨hS, hc, hx, hsing, hsyl, he16, h3, hq⟩

theorem s16c1_cent_V0_le_pCore (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G))) :
    V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({x.val} : Set G)) := by
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hzV : x.val ∈ V := x.val_mem
  have hz2 : x.val ^ 2 = 1 := by simpa using hP.elemAbelian.2 x.val hzV
  have hchar : CFSG.QuasithinUnique.CharTwo (centralizer ({x.val} : Set G)) :=
    D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hx.ne_one hz2)
  have hQS : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤
      D.T ⊓ centralizer ({x.val} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  intro c hcmem
  obtain ⟨hcV₀, hcS⟩ := Subgroup.mem_inf.1 hcmem
  have hcH : c ∈ centralizer ({x.val} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact IsElemAbelian.comm hP.elemAbelian hzV (hP.le hcV₀)
  have hcent : c ∈ centralizer
      ((pCoreOf 2 (centralizer ({x.val} : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.1 hcS r (hQS hr)
  exact hchar (Subgroup.mem_inf.2 ⟨hcH, hcent⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
