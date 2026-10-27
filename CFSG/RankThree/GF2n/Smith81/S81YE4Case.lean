module

public import CFSG.RankThree.GF2n.Smith81.S81YGenSpan
public import CFSG.RankThree.GF2n.Smith81.S81WConjE45
public import CFSG.RankThree.GF2n.Smith81.S81YE4Pure
public import CFSG.RankThree.GF2n.Smith81.S81YE4Move
public import CFSG.RankThree.GF2n.Smith81.S81YE4Span
public import CFSG.RankThree.GF2n.Smith81.S81D6Model
public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81YGenMain

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]

theorem e4_minRootFacts [Finite K] [CharP K 2] :
    MinRootFacts (EAut0 K) (p0 K) IsRt4 :=
  ⟨fun _ hr => isRt4_mul_self hr, fun _ hr _ hp => e4_pure_sub hr hp,
    fun _ _ hr hs hodd hne => e4_odd_disj hr hs hodd hne,
    fun _ _ hr hs hB _ hp hpr => e4_move hr hs hB hp hpr⟩

end CFSG.RankThree.GF2n.Smith81.RootGenE4

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.RootGen
  CFSG.RankThree.GF2n.Smith81.RootGenE4

theorem smith213E4_of_inputs
    (hFE1 : Smith24E4UniformStatement) (hFE2 : E4RootEltStatement)
    (hNF : Smith212ENonfusedE4Statement) (h28 : Smith28E4Statement) :
    Smith213E4Statement := by
  intro G _ _ M Q Z B IH hSE hc4 z hz hz1
  refine smith213_of_good (P := fun M Q Z B => SmithECfg M Q Z B ∧ InCaseE4 M Q Z B) ?_
    ⟨hSE, hc4⟩ hz hz1
  refine ⟨?_, ?_, ?_⟩
  · rintro M Q Z B ⟨hS, hc⟩ h
    exact ⟨hS.conj h, hc.conj h⟩
  · rintro M Q Z B ⟨hS, hc⟩ z hz hz1
    have hrem : RemCfg M Q Z B := hS.toRemCfg
    have H : StrothHyp M Q Z := hrem.ctx.hyp
    obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
    obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hrem hc K γ M₀ hD
    refine ⟨K, inferInstance, inferInstance, hK2, γ, M₀, W K, inferInstance, inferInstance, ψ, φ,
      EAut0 K, p0 K, rootRad0 K, IsRt4, hrem.ctx, hD, d, hz, hz1, ?_, ?_, e4_minRootFacts, ?_⟩
    · intro y hyc hyM hyQ w hw hw1
      exact hNF G M Q Z B IH hS hc z hz hz1 y hyM hyQ hyc w hw hw1
    · intro y hyc hyM hyQ
      exact hFE2 G M Q Z B IH hrem hc K γ M₀ hD ψ φ d z hz hz1 y hyc hyM hyQ
    · intro x hxc hxM hxQ r hxr hr
      obtain ⟨hxL, hφ⟩ := hxr
      obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hxc
      have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z hz1 hxc, hxM, hxQ⟩
      exact caseII_of_spanC d hD H hs hxL hφ (fun c hc' => e4_spanC hr c hc')
        (fun w hw hw1 => hNF G M Q Z B IH hS hc z hz hz1 x hxM hxQ hxc w hw hw1)
  · rintro M Q Z B ⟨hS, hc⟩ X x hs
    exact h28 G M Q Z B IH hS hc X x hs

end CFSG.RankThree.GF2n.Smith81
