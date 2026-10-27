module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightLemE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Layer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs11G
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD556
public import CFSG.Quasithin.Vol2.Ch11SecD556I
public import CFSG.Quasithin.Vol2.Ch11SecD557A
public import CFSG.Quasithin.Vol2.Ch11SecFCase2
public import CFSG.Quasithin.Vol2.Ch11SecFKL1b
public import CFSG.Quasithin.Vol2.Ch11SecFQ3
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartTwo.KFacts.KS116Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
public import CFSG.RankThree.PartTwo.Sec11.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Walter.J1Props

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure S16gStd (D : Data G) : Prop where
  hx : DataExt D
  h4 : 3 < CFSG.Open.evenRank G
  hSg : UC6S846.SigmaStd D
  h61 : UC6.R6_1 D
  h127 : R127 D
  h1214 : F12.R1214 D
  h638 : UC6.R6_38 D
  h1110 : R1110Core D
  h164 : R16_4 D
  h63 : UC6.R6_3 D
  h126 : R126 D
  h1211 : R1211_1 D
  h111 : W3Thm111 G
  h6161ii : W3Lem616_1ii G
  h77 : F07.R77Eq D
  h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1
  h119 : F11.R119 D

theorem S16gStd.h1217 {D : Data G} (h : S16gStd D) : R1217 D :=
  r1217_of_twelve_seventeen D h.hx h.h61 h.h127 h.h1214

theorem s16g_le_stabTil {D : Data G} {V₀ V L : Subgroup G} (hset : Setting16 D V₀ V L) :
    D.M ≤ stabTil V₀ V :=
  le_stabTil hset.hyp16.hyp125.pairFacts.le_normalizer
    hset.hyp16.hyp125.pairFacts.le_normalizer₀

theorem s16g_false_of_fix_M (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ D.sig) (hMst : D.M ≤ stabTil V₀ V)
    (hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup ↥D.M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, barHom V₀ V hV hMst b x = x) : False := by
  have h16 : Hyp16 D V₀ V := hset.hyp16
  have hp3 : 3 ≤ p := by
    have h2 := (D.sig_prime p hpσ).2
    have h1 := hp.two_le
    omega
  obtain ⟨E, hEM, hEel, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hp
    (by rw [UC6.groupPRank_eq_pRank]; exact hS.hx.three_le p hpσ)
  exact s16c1610_false_of_fix_noncyclic D hS.h61 hS.h127 (hV := hV) h16 hMst hp hp3 hpσ hEM
    hEel hEcard hfix

theorem s16g_false_of_fix (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ D.sig)
    (hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
      B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x) : False := by
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  refine s16g_false_of_fix_M D hS (hV := hV) hset hp hpσ hMst ?_
  intro x hx1
  obtain ⟨B', hB'M, hB'p, hB'c, hB'fix⟩ := hfix x hx1
  obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_map_le (barHom V₀ V hV hMst) hp
    (Eb := B') (by rw [range_barHom]; exact hB'M) hB'p hB'c
  exact ⟨B, hBp, hBc, fun b hb => hB'fix _ (hB b hb)⟩

theorem s16g_apply_eq_of_odd {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {Z : Subgroup W} {y : MulAut W} {n : ℕ} (hn : Odd n) (hyn : y ^ n = 1)
    (hZ : ∀ z ∈ Z, y z = z) {x : W} (hx : y x * x⁻¹ ∈ Z) : y x = x := by
  set u : W := y x * x⁻¹ with hu
  have hyu : y u = u := hZ u hx
  have hyx : y x = u * x := by rw [hu]; group
  have hk : ∀ k : ℕ, (y ^ k) x = x * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' y k, MulAut.mul_apply, ih, map_mul, map_pow, hyu, hyx, pow_succ' u k,
        mul_comm u x, mul_assoc]
  have h1 : x * u ^ n = x := by
    rw [← hk n, hyn]
    rfl
  have h2 : u ^ n = 1 := by simpa using h1
  obtain ⟨m, rfl⟩ := hn
  have h3 : u = 1 := by
    have : u ^ (2 * m + 1) = u := by
      rw [pow_succ, pow_mul, hW u, one_pow, one_mul]
    rw [← this]
    exact h2
  rw [hyx, h3, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
