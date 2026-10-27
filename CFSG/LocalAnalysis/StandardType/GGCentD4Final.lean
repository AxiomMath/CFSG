module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCentD4Kernel
public import CFSG.LocalAnalysis.StandardType.GGCentD4Layer
public import CFSG.LocalAnalysis.StandardType.GGCentD4Theta
public import CFSG.LocalAnalysis.StandardType.GGCentD4ThetaGraph
public import CFSG.LocalAnalysis.StandardType.GGCentD4ThetaTorus
public import CFSG.LocalAnalysis.StandardType.GGCentD4Alpha
public import CFSG.LocalAnalysis.StandardType.GGCentD4Frob
public import CFSG.LocalAnalysis.StandardType.GGCentD4Lang
public import CFSG.LocalAnalysis.StandardType.GGCentD4Outer
public import CFSG.LocalAnalysis.StandardType.GGCentD4NoTrans
public import CFSG.LocalAnalysis.StandardType.GGCentD4Descent
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatUntw
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatTw
public import CFSG.LocalAnalysis.StandardType.GGCentD4Fix
public import CFSG.LocalAnalysis.StandardType.GGCentD4RIdent
public import CFSG.LocalAnalysis.StandardType.GGCentD4Glue
public import CFSG.LocalAnalysis.StandardType.GGCentD4PartU
public import CFSG.LocalAnalysis.StandardType.GGCentD4PartT

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (d4Q)

theorem langNontoralD4Fixed_holds
    : LangNontoralD4Fixed := by
  unfold LangNontoralD4Fixed
  intro L hField hAlg hChar p₀ S a n hpair hker K hK
  haveI : CharP L 2 := hChar
  classical
  obtain ⟨ha3, hT, h1, hnM, hn3, hcommd, C, m, hm, hC, hCn, hCd, hW1, hW2⟩ := hpair
  have hpair0 : OrderThreeOutsideConnected S a n :=
    ⟨ha3, hT, h1, hnM, hn3, hcommd, C, m, hm, hC, hCn, hCd, hW1, hW2⟩
  obtain ⟨i, v, hi, hcomp, hrank⟩ := ntpD4_kernel a ha3 hker
  have hker_eq : rootCharKernel a =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    have hcomp_eq : componentRoots (rootCharHom a) i = rootCharKernel a := by
      ext α
      constructor
      · rintro ⟨hα, -⟩; exact hα
      · intro hα
        exact ⟨hα, hi (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a))⟩
    rw [← hcomp_eq]; exact hcomp
  let Y : Subgroup (ModGL Tag.E6 L) := d4KernelGroup L v
  have hY0 : Y = rootSpan Tag.E6 L
      ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := rfl
  have hY : Y = rootSpan Tag.E6 L (rootCharKernel a) := hY0.trans (by rw [hker_eq])
  set R : Subgroup (ModGL Tag.E6 L) := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
  have hlayer := ntpD4_layer S a n hpair0 hker i hi K hK
  obtain ⟨hρker, hKR, hRnorm, hRqs, hKcomp⟩ := hlayer
  obtain ⟨Θ, hΘ⟩ := ntpD4_theta (L := L) v
  obtain ⟨g, ε, hε, halpha⟩ :=
    ntpD4_alpha S a n hpair0 v hker_eq Y hY Θ
      (fun z ε' hz y hy hy' => ntpD4_theta_graph v Y hY0 Θ hΘ z ε' hz y hy hy')
      (fun τ hτ y hy hy' => ntpD4_theta_torus v Y hY0 Θ hΘ τ hτ y hy hy')
  have hstepY : ∀ y ∈ Y, S.D.step y ∈ Y := ntpD4_step_mem S a hT i hi Y hY
  have hnY : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y :=
    ntpD4_nconj_mem a n (S.D.mem_model.mp hnM).1 hcommd i hi Y hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r₀, f, hr₀, hchar, hf, hq₀⟩ := exists_char_pow S
  have hr2 : r₀ = 2 := by
    have h1 : ringChar L = r₀ := (ringChar.eq_iff).2 hchar
    have h2 : ringChar L = 2 := (ringChar.eq_iff).2 hChar
    exact h1.symm.trans h2
  clear hchar
  have hf1 : 1 ≤ f := hf
  have hq : S.D.q = 2 ^ f := by rw [hq₀, hr2]
  have hFr : ∀ c, iterateFrobenius L 2 f c = c ^ ((2 : ℕ) ^ f) :=
    fun c => iterateFrobenius_def 2 f c
  obtain ⟨r, s, c, hr3, hs2, hfrob⟩ :=
    ntpD4_frob_shape S a ha3 hT v hker_eq Y hY Θ hΘ hf1 hq (iterateFrobenius L 2 f) hFr
  have hcomm := ntpD4_comm S n hnM Y hstepY hnY Θ g ε halpha (iterateFrobenius L 2 f) r s c hfrob
  have hs0 : s = 0 := by
    by_contra hs
    have hs1 : s = 1 := by omega
    subst hs1
    exact ntpD4_no_transposition hf1 (iterateFrobenius L 2 f) hFr
      (fun ε' hε' h => ntpD4_graph_not_inner hε' h) r c g ε hε (by simpa only [pow_one] using hcomm)
  subst hs0
  simp only [pow_zero, one_mul, mul_one, inv_one] at hfrob hcomm
  obtain ⟨Ξ, g', hΞstep, hΞn, hcomm'⟩ :=
    ntpD4_xi n Y S.D.step Θ g ε halpha hf1 (iterateFrobenius L 2 f) hFr r c hfrob hcomm
  have hlab : NTPD4Labels (2 ^ f) K := by
    obtain rfl | hr12 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    · simp only [pow_zero, one_mul, mul_one, inv_one] at hΞstep hcomm'
      exact ntpD4_part_untw S a n hpair0 i hi hρker K hRnorm hRqs hKcomp Y hY hstepY Ξ g' ε hε hf1
        hq (iterateFrobenius L 2 f) hFr hΞstep hΞn hcomm'
    · exact ntpD4_part_tw S a n hpair0 i hi hρker K hRnorm hRqs hKcomp Y hY hstepY Ξ g' ε hε hf1 hq
        (iterateFrobenius L 2 f) hFr r hr12 hΞstep hΞn hcomm'
  rw [← hq] at hlab
  exact hlab

end CFSG.StandardType.NTPlane

end
