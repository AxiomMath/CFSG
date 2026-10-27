module

public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
public import CFSG.LocalAnalysis.StandardType.GGResTwDInverter
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
import CFSG.Quasithin.EmptyFaithful.E111RFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggInnerDiagOnLabel_twD_qPlus_qGeFour
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel ggTwoCellTwD p Bs L) :
    GGInnerDiagOnLabel (fun p lab => ggTwoCellTwD p lab ∧ 2 ≤ lab.n) p Bs L := by
  refine hM.mono_label_of_hasLabel fun lab hΛ _ hS => ⟨hS, ?_⟩
  have hp : p.Prime := Fact.out
  have hn : 1 ≤ lab.n := hΛ.1
  have hn1 : lab.n ≠ 1 := by
    intro h1
    have h3 : p ∣ 3 := by simpa [h1] using hS.2.2.1
    have hp3 : p = 3 := ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one
    exact hS.2.2.2 ⟨hp3, h1⟩
  omega

theorem ggTBJOrthLeft_twD_qPlus_with_fixed_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel ggTwoCellTwD p Bs L) :
    (GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hrows : GGInnerDiagOnLabel (fun p lab =>
      (1 ≤ lab.n ∧ GGTBRowR5O1 p lab) ∨ (1 ≤ lab.n ∧ GGTBRowR5O2 p lab)) p Bs L := by
    refine (ggInnerDiagOnLabel_twD_qPlus_qGeFour hM).mono_label fun lab h => ?_
    rcases Nat.even_or_odd lab.rank with he | ho
    · exact Or.inl ⟨by omega, h.1.1, h.1.2.1, Or.inr ⟨he, h.1.2.2.1⟩⟩
    · exact Or.inr ⟨by omega, h.1.1, h.1.2.1, ho, h.1.2.2.1⟩
  rcases hrows.elim_or with hrow | hrow
  · exact ggTBJOrthLeft_rowR5O1_with_fixed_centralizer hH hrow
  · exact ggTBJOrthLeft_rowR5O2_with_fixed_centralizer hH hrow

theorem GGResHyp.bstar_eq_of_twD_even_qPlus
    (hNC : GGLNoncyclicInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun p lab =>
      lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs L) :
    B = Bs := by
  have hp : p.Prime := Fact.out
  have hM' := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)
    (P' := fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I)
    (fun lab hΛ hS => largeEvenLabelAll_iRank_orthMinus_even_nonsplit hp hΛ hS)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hL, lab, _, hraw⟩ := hM'
  obtain ⟨R, _, I, F, _, _, θ, ⟨_, hBN, h3⟩, r, hlift, hrank⟩ := largeEvenRawDatum_exists hraw
  exact bstar_eq_of_inner_rank hH.1.1 hH.1.2.1
    (hNC G p B x L hH.1.1) hL θ
    (hH.1.2.1.1.trans hBN) h3 hlift hrank

theorem GGResHyp.false_of_exact2_L_twD_qPlus_of_iOne
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel ggTwoCellTwD p Bs L)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hfwd := (ggTBJOrthLeft_twD_qPlus_with_fixed_centralizer hH hM).2
  have hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L := by
    refine hM.mono_label fun lab h => ⟨?_, ?_⟩
    · rcases Nat.even_or_odd lab.rank with he | ho
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr
          ⟨h.1, Or.inr ⟨h.2.2.1, he⟩⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨h.1, h.2.2.1, ho⟩)⟩
    · simp [ggSingularBaseLabel, h.1]
  exact hH.false_of_exact2_nonsingular_L hT hLift hfwd hL hI1 h2

theorem GGResHyp.false_of_exact2_L_twD_even_qPlus
    (hNC : GGLNoncyclicInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun p lab => ggTwoCellTwD p lab ∧ Even lab.rank) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hbase : GGInnerDiagOnLabel ggTwoCellTwD p Bs L := hM.mono_label fun _ h => h.1
  have hEq : B = Bs := hH.bstar_eq_of_twD_even_qPlus hNC
    (hM.mono_label fun _ h => ⟨h.1.1, h.1.2.1, h.2, h.1.2.2.1⟩)
  have hI1 := hH.iOne_of_eq_bstar hEq
  exact hH.false_of_exact2_L_twD_qPlus_of_iOne hT hLift hbase hI1 h2

theorem GGResHyp.twD_qPlus_exact2_survivor
    (hNC : GGLNoncyclicInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel ggTwoCellTwD p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGInnerDiagOnLabel (fun p lab => ggTwoCellTwD p lab ∧ Odd lab.rank ∧ 2 ≤ lab.n) p Bs L ∧
      Bs ⊓ Subgroup.centralizer (J : Set G) ≠ D ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧
      ∃ r : ℕ, Nat.card Bs = p ^ r ∧ 5 ≤ r ∧
        Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ (r - 3) ∧ B < Bs := by
  have hodd : GGInnerDiagOnLabel (fun p lab => ggTwoCellTwD p lab ∧ Odd lab.rank ∧
      2 ≤ lab.n) p Bs L := by
    have hpar : GGInnerDiagOnLabel (fun p lab =>
        (ggTwoCellTwD p lab ∧ Even lab.rank) ∨
          (ggTwoCellTwD p lab ∧ Odd lab.rank ∧ 2 ≤ lab.n)) p Bs L := by
      refine (ggInnerDiagOnLabel_twD_qPlus_qGeFour hM).mono_label fun lab h => ?_
      rcases Nat.even_or_odd lab.rank with he | ho
      · exact Or.inl ⟨h.1, he⟩
      · exact Or.inr ⟨h.1, ho, h.2⟩
    rcases hpar.elim_or with he | ho
    · exact (hH.false_of_exact2_L_twD_even_qPlus hNC hT hLift he h2).elim
    · exact ho
  have hne : Bs ⊓ Subgroup.centralizer (J : Set G) ≠ D := fun hI1 =>
    hH.false_of_exact2_L_twD_qPlus_of_iOne hT hLift hM hI1 h2
  exact ⟨hodd, hne, hH.card_eq_p3_of_ne hne, hH.exactThree_data_of_iOne_ne hne⟩

section Suppliers

theorem GGConfig.rootTwo_of_slTwo_centralizing
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G}
    (hC : GGConfig p B Bs x L D J) (hp2 : p ≠ 2)
    (hM : GGInnerDiagOn Bs L) (hZ : Subgroup.center ↥L = ⊥)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hθ : Function.Injective θ)
    (hθL : θ.range ≤ L) (hθB : θ.range ≤ Subgroup.centralizer (B : Set G)) :
    GGResHigherFieldRootTwo p B Bs J := by
  classical
  have hp : p.Prime := Fact.out
  have hLq := isQuasisimple_of_largeEvenMarking hM
  haveI := hLq.2
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hLs : IsSimpleGroup ↥L := e.symm.isSimpleGroup
  haveI := hLs
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hb : commutator ↥L = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact h a b
    rw [hM.1] at hb
    exact top_ne_bot hb
  have hchev := isChevSimple_two_of_largeEvenMarking_of_isSimpleGroup hLs hM
  have hD : D ≤ B := hC.2.2.1.1
  have hDN : D ≤ Subgroup.normalizer (L : Set G) :=
    hD.trans (hC.2.1.1.trans hM.le_normalizer)
  let γ := ggGamma L hDN
  let E := γ.range
  let C := (Subgroup.centralizer (D : Set G)).subgroupOf L
  have hEp : IsPGroup p E :=
    (CFSG.Open.IsElemAbelian.isPGroup hC.2.2.1.2.1).of_surjective
      γ.rangeRestrict (by rintro ⟨a, d, rfl⟩; exact ⟨d, rfl⟩)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact CFSG.Open.IsElemAbelian.comm hC.2.2.1.2.1 a.2 b.2
  have hfix : CFSG.LocalAnalysis.GLTheoremA.I142.centFix E = C := by
    ext l
    rw [CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hl d hd
      have hh := congrArg Subtype.val (hl (γ ⟨d, hd⟩) ⟨⟨d, hd⟩, rfl⟩)
      change d * (l : G) * d⁻¹ = (l : G) at hh
      calc d * (l : G) = (d * (l : G) * d⁻¹) * d := by group
        _ = (l : G) * d := by rw [hh]
    · rintro hl _ ⟨d, rfl⟩
      apply Subtype.ext
      change (d : G) * (l : G) * (d : G)⁻¹ = (l : G)
      rw [hl d d.2]
      group
  let θL := θ.codRestrict L fun g => hθL ⟨g, rfl⟩
  let P := θL.range
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
  have hPperf : ⁅P, P⁆ = P := by
    change ⁅θL.range, θL.range⁆ = θL.range
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hPC : P ≤ C := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_iff.mp (hθB ⟨g, rfl⟩) d (hD hd)
  have hPfix : P ≤ CFSG.LocalAnalysis.GLTheoremA.I142.centFix E := by rwa [hfix]
  have hPl := LayerAbelian.lieSemisimpleCentAbelian ↥L hLs hnc hchev p hp hp2
    E hEp hEc P hPfix hPperf
  have hPly : P ≤ LargeEvenLayer C := by
    rw [LargeEven.largeEvenLayer_eq_glaLayer, ← hfix]
    exact hPl
  have hmapC : C.map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hmapP : P.map L.subtype = θ.range := by
    rw [← MonoidHom.range_comp]
    rfl
  have hθJ : θ.range ≤ J := by
    rw [← hmapP, hC.2.2.1.2.2.2.2.1, ← hmapC,
      largeEvenLayer_map_of_injective L.subtype L.subtype_injective]
    exact Subgroup.map_mono hPly
  obtain ⟨u, hu1, hu2⟩ := CFSG.Quasithin.E2.E22N.exists_involution_sl2 (K := F)
  have hv1 : θ u ≠ 1 := fun h => hu1 (hθ (h.trans θ.map_one.symm))
  have hv2 : θ u ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  refine ⟨Subgroup.zpowers (θ u), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hv1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (θ u)))
  · apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, pow_one]
  · exact Subgroup.zpowers_le.mpr (hθJ ⟨u, rfl⟩)
  · have hle : Subgroup.zpowers (θ u) ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.zpowers_le.mpr (hθB ⟨u, rfl⟩)
    exact (Subgroup.le_centralizer_iff.mp hle).trans (Subgroup.centralizer_le_normalizer _)

theorem GGResHyp.iOne_of_twD_odd_qPlus
    (hRig : GGLabelRigidInput) (hNC : GGLNoncyclicInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel (fun p lab =>
      ggTwoCellTwD p lab ∧ Odd lab.rank ∧ 2 ≤ lab.n) p Bs L) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  classical
  by_cases heq : B = Bs
  · exact hH.iOne_of_eq_bstar heq
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hbase : GGInnerDiagOnLabel ggTwoCellTwD p Bs L := hM.mono_label fun _ h => h.1
  have hrow : ∀ lab, (ggTwoCellTwD p lab ∧ Odd lab.rank ∧ 2 ≤ lab.n) →
      ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab := by
    intro lab h
    right
    refine ⟨h.1.1, ?_, h.2.1, h.1.2.2.1⟩
    have h4 := h.1.2.1
    obtain ⟨k, hk⟩ := h.2.1
    omega
  haveI : Group.IsPerfect ↥L := Group.IsPerfect.mk hM.1
  have hZ : ∀ lab, (ggTwoCellTwD p lab ∧ Odd lab.rank ∧ 2 ≤ lab.n) →
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → Subgroup.center ↥L = ⊥ := by
    intro lab h hhas
    exact OrthTorus.center_eq_bot_of_hasLabel_orth (Or.inr h.1.1) h.1.2.1 h.2.2 hhas
  obtain ⟨lab, hlab, hhas, Φ, _, hfield, hQ, _, _⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hH.1.2.1.2.1
      hH.1.2.1.2.2.2 hrow hM hZ (ggGamma_L_exists_ne_one hH.1)
  have hZL := hZ lab hlab hhas
  have hq : 4 ≤ Nat.card Φ.F := by
    rw [hfield]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by omega) hlab.2.2
  obtain ⟨U, hUL, hU1, hU2, hBU⟩ := hH.1.innLocal_of_twD_marking
    (hNC G p B x L hH.1.1) (hM.mono_label fun _ h => ⟨h.1.1, h.1.2.1⟩) heq
  have hOrth := ggInnerDiagOnLabel_orthTorus_of_twD
    (hbase.mono_label fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have hpZ := (hH.exists_twD_inverter hp2 hOrth).1
  obtain ⟨θ, hθ, hθL, hθB⟩ := Φ.exists_slTwo_centralizing_B hpZ hp2 hQ hq
    hH.1 heq hUL hU1 hU2 hBU
  exact hH.iOne_of_rootTwo (hH.1.rootTwo_of_slTwo_centralizing hp2
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hbase) hZL hq θ hθ hθL hθB)

theorem ggResMultiNodeRestTwoCellInput_twD_qPlus :
    GGResMultiNodeRestTwoCellInput ggTwoCellTwD := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hM h2
  have hT := ggTBTorAll_of_remaining trivial
  have hLift := ggTBTorLiftRows_holds
  have hs := hH.twD_qPlus_exact2_survivor ggLNoncyclicInput_holds hT hLift hM h2
  have hI1 := hH.iOne_of_twD_odd_qPlus ggLabelRigidInput_holds ggLNoncyclicInput_holds hs.1
  exact hH.false_of_exact2_L_twD_qPlus_of_iOne hT hLift hM hI1 h2

end Suppliers

end CFSG.StandardType

end
