module

public import CFSG.Yardstones.Md8ed6d263d89.Definitions
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Joint
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ExcRankProofs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLayerLemma
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFiveEndpoints
import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Abelian

public section

namespace CFSG.Yardstones.Md8ed6d263d89

@[expose] def NonemptyExceptional : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p → CFSG.AGLEmbedding.D1Local p P M →
      (∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
        ∃ P₀ : Subgroup G, CFSG.Open.GLBClauseTwo M P P₀ p

@[expose] def NonemptyConfinement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p → CFSG.AGLEmbedding.D1Local p P M →
      (∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M

@[expose] def EmptyStrong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
    CFSG.Open.GLBPreuniqueness G →
    CFSG.AGLEmbeddingD2.D1For G → CFSG.LocalAnalysis.RankFourTheoremC.D2For G →
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G →
    (∀ (f : ℕ) (F : Sylow f G) (N : Subgroup G), CFSG.AGLEmbedding.D1Local f F N →
      (∃ y : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement f N y) → TheoremCAt G f N) →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), 5 ≤ p →
      (∀ (q : ℕ) (Q : Sylow q G) (N : Subgroup G), p < q → CFSG.AGLEmbedding.D1Local q Q N →
        TheoremCAt G q N) →
      CFSG.AGLEmbedding.D1Local p P M →
      (¬ ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x) →
      CFSG.Open.GLBStronglyEmbedded p M

theorem nonemptyConfinement_of_yardstones (h49 : YSPNonemptyConfinement)
    (h41 : YSPPointTypeLinTwoOrUnitary) : NonemptyConfinement :=
  fun G _ _ _ hn hK hc he hpre hD1 hD2 hFC p P M hp5 hloc hx =>
    (h49 G hn hK hc he hpre hD1 hD2 hFC p P M hp5 hloc hx
      fun y R K i hd => h41 G hn hK hc he hpre hD1 hFC p P M y R K i hp5 hloc hd).1

theorem emptyStrong_of_yardstones (h614 : YSPEmptyPlaneLocals)
    (hrest : YSPEmptyStrongOfPlaneLocals) : EmptyStrong :=
  fun G _ _ _ hn hK hc he hpre hD1 hD2 hFC h57 p P M hp5 hIH hloc hPM =>
    hrest G hn hK hc he hpre hD1 hD2 hFC h57 p P M hp5 hIH hloc hPM
      (h614 G hn hK hc he hpre hD1 hD2 hFC h57 p P M hp5 hIH hloc hPM)

section Prime

variable {G : Type} [Group G] [Finite G]

theorem theoremCAt_of_thmCAt [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD2 : CFSG.LocalAnalysis.RankFourTheoremC.D2For G)
    (hFC : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G) {q : ℕ} (hq5 : 5 ≤ q)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ThmCAt G q) {Q : Sylow q G}
    {N : Subgroup G} (hloc : CFSG.AGLEmbedding.D1Local q Q N) : TheoremCAt G q N := by
  have hcore : CFSG.Open.GLBCore q 2 (Q : Subgroup G) ≤ N := hFC q Q N hloc
  refine ⟨⟨hloc.beta, CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hnonab hloc.maxLocal.1,
    hloc.maxLocal.1, Q, CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hloc, hcore,
    (h.1 Q N hloc hcore).imp id fun h' => ⟨hq5, h'⟩⟩, fun H hH h2 => ?_⟩
  by_cases hs : CFSG.Open.GLBStronglyEmbedded q N
  · exact CFSG.LocalAnalysis.RankFourTheoremC.le_of_stronglyEmbedded hD2 hloc.beta Q
      hloc.maxLocal hcore hs hH h2
  · exact h.2 Q N hloc hs H hH h2

theorem theoremCAt_of_pNonempty [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Open.IsKProper G) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 4 ≤ CFSG.Open.evenRank G) (hpre : CFSG.Open.GLBPreuniqueness G)
    (hD1 : CFSG.AGLEmbeddingD2.D1For G) (hD2 : CFSG.LocalAnalysis.RankFourTheoremC.D2For G)
    (hFC : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G)
    (hP5 : CFSG.LocalAnalysis.RankFourTheoremC.PElementPrimeFive G)
    (hconf : NonemptyConfinement) (hexc : NonemptyExceptional) {f : ℕ} {F : Sylow f G}
    {N : Subgroup G} (hloc : CFSG.AGLEmbedding.D1Local f F N)
    (hy : ∃ y : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement f N y) : TheoremCAt G f N := by
  obtain ⟨y, hy'⟩ := hy
  have hf5 : 5 ≤ f := hP5 ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩ hD1 hFC f F N hloc y hy'
  have hc := hconf G hnonab hK hchar he hpre hD1 hD2 hFC f F N hf5 hloc ⟨y, hy'⟩
  obtain ⟨hsolv, hab, P₀, hcl⟩ :=
    hexc G hnonab hK hchar he hpre hD1 hD2 hFC f F N hf5 hloc ⟨y, hy'⟩
  exact ⟨⟨hloc.beta, CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hnonab hloc.maxLocal.1,
    hloc.maxLocal.1, F, CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hloc,
    hFC f F N hloc, Or.inr ⟨hf5, hsolv, hab, P₀, hcl⟩⟩, hc⟩

end Prime

theorem thmCStepFive_of_yardstones (hD1 : CFSG.LocalAnalysis.RankFourTheoremC.D1Rank4)
    (hD2 : CFSG.LocalAnalysis.RankFourTheoremC.D2Rank4)
    (hFC : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreRank4)
    (hP5 : ∀ (X : Type) [Group X] [Finite X],
      CFSG.LocalAnalysis.RankFourTheoremC.PElementPrimeFive X)
    (h313 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NormalElementaryRankFour)
    (hconf : NonemptyConfinement) (hexc : NonemptyExceptional) (hstrong : EmptyStrong) :
    CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ThmCStepFive := by
  intro G _ _ _ hnonab hK hchar he hpre p hp5 IH
  have hD1G : CFSG.AGLEmbeddingD2.D1For G := hD1 G hnonab hK hchar he hpre
  have hFCG : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G :=
    hFC G hnonab hK hchar he hpre
  have hδ₂ : CFSG.Open.GLBDeltaTwo G :=
    CFSG.LocalAnalysis.RankFourTheoremC.deltaTwoRank4_of_pElement hD1 hFC hP5 h313 G hnonab hK
      hchar he hpre
  have hD2G : CFSG.LocalAnalysis.RankFourTheoremC.D2For G :=
    hD2 G hnonab hK hchar he (CFSG.LocalAnalysis.RankFourTheoremC.deltaOne_of_fullCore hpre hFCG)
      hδ₂
  have h57 : ∀ (f : ℕ) (F : Sylow f G) (N : Subgroup G), CFSG.AGLEmbedding.D1Local f F N →
      (∃ y : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement f N y) → TheoremCAt G f N :=
    fun _ _ _ hloc hy =>
      theoremCAt_of_pNonempty hnonab hK hchar he hpre hD1G hD2G hFCG (hP5 G) hconf hexc hloc hy
  have hIH : ∀ (q : ℕ) (Q : Sylow q G) (N : Subgroup G), p < q →
      CFSG.AGLEmbedding.D1Local q Q N → TheoremCAt G q N := fun q _ _ hpq hloc =>
    theoremCAt_of_thmCAt hnonab hD2G hFCG (by omega) (IH q hpq) hloc
  refine ⟨fun P M hloc _ => ?_, fun P M hloc hns H hH h2 => ?_⟩
  · by_cases hPM : ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x
    · exact Or.inr (hexc G hnonab hK hchar he hpre hD1G hD2G hFCG p P M hp5 hloc hPM)
    · exact Or.inl (hstrong G hnonab hK hchar he hpre hD1G hD2G hFCG h57 p P M hp5 hIH hloc
        hPM).2
  · by_cases hPM : ∃ x : G, CFSG.LocalAnalysis.RankFourTheoremC.IsPElement p M x
    · exact hconf G hnonab hK hchar he hpre hD1G hD2G hFCG p P M hp5 hloc hPM H hH h2
    · exact absurd (hstrong G hnonab hK hchar he hpre hD1G hD2G hFCG h57 p P M hp5 hIH hloc
        hPM) hns

section Certificates


theorem nonemptyExceptional_of_yardstones
    (h243 : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h244 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NongenerationList)
    (hsig : CFSG.LocalAnalysis.RankFourTheoremC.GL83SignalizerAut)
    (h49 : YSPNonemptyConfinement) (h41 : YSPPointTypeLinTwoOrUnitary)
    (hcent : YSPPointCentralizers) (hfrob : YSPPointFrobenius) : NonemptyExceptional := by
  intro G _ _ _ hnonab hK hchar he hpre hD1 hD2 hFC p P M hp5 hloc hx
  obtain ⟨hconf, htype⟩ := h49 G hnonab hK hchar he hpre hD1 hD2 hFC p P M hp5 hloc hx
    fun y R K i hd => h41 G hnonab hK hchar he hpre hD1 hFC p P M y R K i hp5 hloc hd
  obtain ⟨x, hx⟩ := hx
  obtain ⟨m, -, hpt⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_isPPoint hFC hloc hx
  have : Fact p.Prime := ⟨hloc.beta.1⟩
  have hp2 : p ≠ 2 := hloc.beta.2.1
  have hS : CFSG.AGLEmbedding.D1Global G := ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
  obtain ⟨R, K, i, hf, hReq⟩ := hpt.exists_pPointFacts hp2 h243 h244
    (fun _ => CFSG.LocalAnalysis.RankFourTheoremC.PPointP.pPointExclusionFive_of_partI h243 h244
      hsig)
    CFSG.AGLEmbedding.kFactUnitaryBorelMaximal CFSG.AGLEmbedding.kFactUnitaryInvolution
    CFSG.AGLEmbedding.kFactReeBorelMaximal CFSG.AGLEmbedding.kFactReeInvolution hS hD1 hFC hloc
  obtain ⟨d, n, hn, rfl, hd⟩ := htype _ R K i ⟨hpt, hf, hReq⟩
  have hab : IsMulCommutative (P : Subgroup G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PPointP.IsPPoint.isMulCommutative_sylow_p hp5 h243 h244
      hsig hS hD1 hFC hloc hpt hn hf hd hReq
  have hwc : ∀ g : G, CFSG.Open.GLBConj g (Subgroup.zpowers (m * x * m⁻¹)) ≤ (P : Subgroup G) →
      CFSG.Open.GLBConj g (Subgroup.zpowers (m * x * m⁻¹)) = Subgroup.zpowers (m * x * m⁻¹) :=
    fun g hg =>
      CFSG.LocalAnalysis.RankFourTheoremC.PPointP.IsPPoint.weaklyClosed_p hp5 h243 h244 hsig hS
        hD1 hFC hloc hpt hn hf hd hReq g⁻¹ hg
  obtain ⟨⟨hlayer, hnot, hcyc⟩, hlines⟩ :=
    hcent G hnonab hK hchar he hpre hD1 hFC p P M _ hp5 hloc hpt hconf hab hwc
  obtain ⟨hsolv, hfr⟩ := hfrob G hnonab hK hchar he hpre hD1 hFC p P M _ hp5 hloc hpt hconf hab
    hwc hlines hlayer hnot hcyc
  refine ⟨hsolv, hab, Subgroup.zpowers (m * x * m⁻¹), ?_⟩
  exact ⟨Subgroup.zpowers_le.mpr hpt.mem, by rw [Nat.card_zpowers, hpt.elem.2.1], hwc, hlayer,
    hnot, hcyc, hfr, hlines⟩

section Milestone


theorem lc_gl_theorem_c_rank_four_of_yardstones
    (hD1 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (_hnonab : ∃ a b : G, a * b ≠ b * a)
      (_hK : CFSG.Open.IsKProper G) (_hchar : CFSG.Open.IsCharTwoType G)
      (_he : 4 ≤ CFSG.Open.evenRank G) (_hpre : CFSG.Open.GLBPreuniqueness G)
      (p : ℕ) (_hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
      (M : Subgroup G) (_hM : CFSG.Open.GLBIsMaxTwoLocal M)
      (_hWM : CFSG.Open.GLBWeakCore p (P : Subgroup G) ≤ M)
      (H : Subgroup G) (_hH : CFSG.Open.IsTwoLocal H) (_hHM : 3 ≤ CFSG.Open.pRank p (H ⊓ M)),
      H ≤ M)
    (hD2 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (_hnonab : ∃ a b : G, a * b ≠ b * a)
      (_hK : CFSG.Open.IsKProper G) (_hchar : CFSG.Open.IsCharTwoType G)
      (_he : 4 ≤ CFSG.Open.evenRank G)
      (_hδ₁ : CFSG.Open.GLBDeltaOne G) (_hδ₂ : CFSG.Open.GLBDeltaTwo G)
      (p : ℕ) (_hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
      (M : Subgroup G) (_hM : CFSG.Open.GLBIsMaxTwoLocal M)
      (_hPM : CFSG.Open.GLBCore p 2 (P : Subgroup G) ≤ M)
      (Q : Subgroup G) (_hQ : IsPGroup p Q) (_hQrank : CFSG.Open.pRank p Q = 2)
      (_hQM : CFSG.Open.GLBCore p 1 Q ≤ M)
      (H : Subgroup G) (_hH : CFSG.Open.IsTwoLocal H) (_hQH : Q ≤ H),
      H ≤ M)
    (y01 : YSFischerRankFourPending)
    (y02 : CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwoSylowOfD1Rank4)
    (y03 : CFSG.LocalAnalysis.RankFourTheoremC.RelativePairExclusionOfD1Rank4)
    (y04 : YSPNonemptyConfinement) (y05 : YSPPointTypeLinTwoOrUnitary)
    (y06 : YSPPointCentralizers) (y07 : YSPPointFrobenius) (y08 : YSPEmptyPlaneLocals)
    (y09 : YSPEmptyStrongOfPlaneLocals)
    (y10 : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (y11 : CFSG.LocalAnalysis.RankFourTheoremC.GL83NongenerationList)
    (y12 : CFSG.LocalAnalysis.RankFourTheoremC.GL83SignalizerAut)
    (y13 : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (y14 : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure)
    (y15 : GL83.I_7_13_1) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G → 4 ≤ CFSG.Open.evenRank G →
      CFSG.Open.GLBPreuniqueness G → CFSG.Open.GLBUniqueFour G := by
  intro G _ _ _ hnonab hK hchar he hpre
  have hD1' : CFSG.LocalAnalysis.RankFourTheoremC.D1Rank4 := hD1
  have hD2' : CFSG.LocalAnalysis.RankFourTheoremC.D2Rank4 := hD2
  have hFC : CFSG.LocalAnalysis.RankFourTheoremC.FullCoreRank4 :=
    CFSG.LocalAnalysis.RankFourTheoremC.fullCoreRank4_of_componentPCoreTrivial hD1' y01 y10 y02
      y03
  have hP5 : ∀ (X : Type) [Group X] [Finite X],
      CFSG.LocalAnalysis.RankFourTheoremC.PElementPrimeFive X := fun _ _ _ =>
    CFSG.LocalAnalysis.RankFourTheoremC.pElementPrimeFive_holds y10 y11 y12
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds
      CFSG.AGLEmbedding.kFactReeBorelMaximal CFSG.AGLEmbedding.kFactReeInvolution y13 y14 y15
  have hstep : CFSG.LocalAnalysis.RankFourTheoremC.PPointP.ThmCStepFive :=
    thmCStepFive_of_yardstones hD1' hD2' hFC hP5
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds
      (nonemptyConfinement_of_yardstones y04 y05)
      (nonemptyExceptional_of_yardstones y10 y11 y12 y04 y05 y06 y07)
      (emptyStrong_of_yardstones y08 y09)
  exact CFSG.LocalAnalysis.RankFourTheoremC.theoremCRankFour_of_five_endpoints' hD1' hD2' hFC
    (CFSG.LocalAnalysis.RankFourTheoremC.PPointP.dichotomyRank4Five_of_step hstep)
    (CFSG.LocalAnalysis.RankFourTheoremC.PPointP.e2NonstrongRank4Five_of_step hstep)
    y10 y11 y12 y13 y14 y15 G hnonab hK hchar he hpre

end Milestone

end Certificates

end CFSG.Yardstones.Md8ed6d263d89
