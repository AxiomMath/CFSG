module

public import CFSG.RankThree.GF2n.Smith81.S81YUPure
public import CFSG.RankThree.GF2n.Smith81.S81YUMove
public import CFSG.RankThree.GF2n.Smith81.S81YUCaseII
public import CFSG.RankThree.GF2n.Smith81.S81UInvolMain
public import CFSG.RankThree.GF2n.Smith81.S81UConj
public import CFSG.RankThree.GF2n.Smith81.S81UStmts
public import CFSG.RankThree.GF2n.Smith81.S81YGenMain

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.GF2n.Smith81.RootGen
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type} [Field K]


theorem u6_minRootFacts {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (e : K ≃+* Fσ (unitaryInvolution F 2 f)) :
    MinRootFacts (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e)
      (IsRtU (unitaryInvolution F 2 f) e) :=
  ⟨fun _ hr => isRtU_mul_self e hr, fun _ hr _ hp => u6_pure_sub hF e hr hp,
    fun r s hr hs => u6_odd_disj e r s hr hs,
    fun r s hr hs hB p hp hpr => u6_move hF e r s hr hs hB p hp hpr⟩

end CFSG.RankThree.GF2n.Smith81.RootGenU

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenU

theorem smith213E3U_of_inputs (hFE1 : Smith24E3UUniformStatement)
    (hFE2 : E3URootEltStatement) (hNF : Smith212ENonfusedE3UStatement) :
    Smith213E3UStatement := by
  intro G _ _ M Q Z B IH hSE hc3 z hz hz1
  have h28 : Smith28E3UStatement := smith28E3U_of_FE1 hFE1
  refine smith213_of_good (P := fun M Q Z B => SmithECfg M Q Z B ∧ InCaseE3U M Q Z B) ?_
    ⟨hSE, hc3⟩ hz hz1
  refine ⟨?_, ?_, ?_⟩
  · rintro M Q Z B ⟨hS, hc⟩ h
    exact ⟨hS.conj h, hc.conj h⟩
  · rintro M Q Z B ⟨hS, hc⟩ z hz hz1
    have hrem : RemCfg M Q Z B := hS.toRemCfg
    have H : StrothHyp M Q Z := hrem.ctx.hyp
    obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
    obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G M Q Z B IH hrem hc K γ M₀ hD
    have hcardZ : Nat.card Z = 2 ^ f := by
      rw [← hD.card, ← card_Fσ_eq hF]
      exact Nat.card_congr e.toEquiv
    have h4 : 4 ≤ 2 ^ f := hcardZ ▸ H.q4
    refine ⟨K, inferInstance, inferInstance, hK2, γ, M₀, _, inferInstance, inferInstance, ψ, φ, _, _, _,
      IsRtU (unitaryInvolution F 2 f) e, hrem.ctx, hD, d, hz, hz1, ?_, ?_, u6_minRootFacts hF e, ?_⟩
    · intro y hyc hyM hyQ w hw hw1
      exact hNF G M Q Z B IH hS hc z hz hz1 y hyM hyQ hyc w hw hw1
    · intro y hyc hyM hyQ
      exact hFE2 G M Q Z B IH hrem hc K γ M₀ hD F f hF e ψ φ d z hz hz1 y hyc hyM hyQ
    · intro x hxc hxM hxQ r hxr hr
      obtain ⟨hxL, hφ⟩ := hxr
      obtain ⟨g, hg, rfl⟩ := hr
      obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hxc
      have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z hz1 hxc, hxM, hxQ⟩
      exact u6_caseII hF h4 e hrem.ctx hD d hs hxL hg hφ
        (fun w hw hw1 => hNF G M Q Z B IH hS hc z hz hz1 x hxM hxQ hxc w hw hw1)
  · rintro M Q Z B ⟨hS, hc⟩ X x hs
    exact h28 G M Q Z B IH hS hc X x hs

end CFSG.RankThree.GF2n.Smith81
