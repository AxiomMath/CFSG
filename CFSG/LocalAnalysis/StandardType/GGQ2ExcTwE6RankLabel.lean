module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent
import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType


theorem excTwE6_L_label
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs (ggG0 3 B x L D J))
    (hN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) (hx : x ∈ Bs)
    (hcomp : IsComponentOf (L.subgroupOf (ggG0 3 B x L D J))
      (ggAutFixedSubgroup (ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩)))
    (huniq : ∀ Q : Subgroup ↥(ggG0 3 B x L D J),
      IsComponentOf Q (ggAutFixedSubgroup (ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩)) →
        Q = L.subgroupOf (ggG0 3 B x L D J)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      TablePThreeKG.E6TwoCompLabelT lab := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hI : GGThmIHyp 3 B x L := hcfg.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  let δ : MulAut ↥(ggG0 3 B x L D J) := ggGamma (ggG0 3 B x L D J) hN ⟨x, hx⟩
  have hx3 : x ^ 3 = 1 := by
    rw [← hcfg.orderOf_x]
    exact pow_orderOf_eq_one x
  have hb3 : (⟨x, hx⟩ : ↥Bs) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hδ3 : δ ^ 3 = 1 := by
    dsimp [δ]
    rw [← map_pow, hb3, map_one]
  have hδ1 : δ ≠ 1 := by
    intro h
    apply not_mem_centralizer_ggG0_of_stdSub hst hDJ
    have h' := (ggGamma_eq_one_iff (L := ggG0 3 B x L D J) (hBN := hN)
      (b := ⟨x, hx⟩)).mp h
    simpa using h'
  unfold GGInnerDiagOnLabel at hM
  have hmark : LargeEvenMarking ↥(ggG0 3 B x L D J)
      (fun lab _ _ I _ θ => lab = ⟨.twE6, 0, 1⟩ ∧ ggInducedAut θ δ ∈ I) := by
    refine largeEvenMarking_mono ?_ hM
    rintro lab R _ I F θ ⟨hlab, -, hact⟩
    obtain ⟨φ, hφI, hφ⟩ := hact x⁻¹ (Subgroup.inv_mem Bs hx)
    have hφeq : φ = ggInducedAut θ δ := by
      ext r
      obtain ⟨z, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      have hrel : ((δ l : ↥(ggG0 3 B x L D J)) : G) = (x⁻¹)⁻¹ * (l : G) * x⁻¹ := by
        dsimp [δ]
        rw [ggGamma_coe]
        simp
      rw [hφ l (δ l) hrel, ggInducedAut_apply]
    exact ⟨hlab, by rw [← hφeq]; exact hφI⟩
  obtain ⟨hXc, labL, hlabL, hraw⟩ := hmark
  have hlabEq : labL = ⟨.twE6, 0, 1⟩ := by
    obtain ⟨R0, _, I0, F0, hP0⟩ := largeEvenRawDatum_exists hraw
    exact hP0.2.2.choose_spec.1
  have htagL : labL.tag = .twE6 := by rw [hlabEq]
  have hn1 : labL.n = 1 := by rw [hlabEq]
  have hrawMM : LargeEvenRawDatumLegacy labL
      (fun R _ I F => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃* R,
          labL = ⟨.twE6, 0, 1⟩ ∧ ggInducedAut θ δ ∈ I) ∧ MarkedModel labL R) :=
    largeEvenRawDatum_markedModel hlabL (fun R _ I F h => h.2.1) hraw
  have hinndiag : LargeEvenLabelAll labL (LargeEvenSimpleGuard GGInndiagCommEq) :=
    largeEvenLabelAll_inndiagComm_twE6 hlabL htagL
  have hrawAll := hinndiag _ hrawMM
  obtain ⟨R, hR, I, F', hbase, hGuard⟩ := largeEvenRawDatum_exists hrawAll
  obtain ⟨⟨hs, hna, θ, -, hδI⟩, hm⟩ := hbase
  have hEq : GGInndiagCommEq R I F' := hGuard hs hna
  have ht_mem : markTag labL ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, htagL]
  have hchev0 : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag labL) 2 labL.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag labL) (markRank labL) (markChar labL)
        (markDeg labL) := hm
    have h := hm0.chevalleyExceptionalModel ht_mem
    have hchar : markChar labL = 2 := by simp [markChar, htagL]
    have hdeg : markDeg labL = labL.n := by simp [markDeg, htagL]
    rw [hchar, hdeg] at h
    exact h
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R .twistedE6 2 labL.n :=
    TablePThreeKG.e6TwoLeaf_chevTwE6 hchev0 htagL
  obtain ⟨d, hdchar, hk, huntw, he⟩ :=
    TablePThreeKG.e6TwoLeaf_index_twE6 (p := 2) (f := labL.n) hchev
  obtain ⟨e⟩ := he
  have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
    rw [hk, hn1, pow_one]
  have hnotE6 : ¬ (∃ q : TauCeti.PrimePower, d.1 = .E6 q) := by
    rintro ⟨q1, hq1⟩
    obtain ⟨q2, hq2⟩ := huntw
    rw [hq1] at hq2
    cases hq2
  obtain ⟨lab', hlab', hhas', -, hpairT⟩ :=
    TablePThreeKG.e6TwoLeaf_component (X := ↥(ggG0 3 B x L D J)) (δ := δ)
      (J := L.subgroupOf (ggG0 3 B x L D J)) θ hXc hδ3 hδ1 hcomp huniq hδI hEq
      d hdchar hdfield (Or.inr huntw) e
  have hLG₀ : L ≤ ggG0 3 B x L D J := le_sup_left
  have hhas : GGHasLabel lab' (↥L ⧸ Subgroup.center ↥L) :=
    ggHasLabel_of_mulEquiv (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hLG₀)) hhas'
  exact ⟨lab', hlab', hhas, hpairT hnotE6⟩

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
