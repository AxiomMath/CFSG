module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixPZ
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerNormal
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcChev
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedG
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRedT
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcFixE6All
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwE6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

theorem largeEvenRawDatumLegacy_of_canonical_of_tag {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (hG2 : lab.tag ≠ .G2der) (hF4 : lab.tag ≠ .twF4) (hF4' : lab.tag ≠ .twF4der)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) : LargeEvenRawDatumLegacy lab Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals first
    | exact absurd rfl hG2
    | exact absurd rfl hF4
    | exact absurd rfl hF4'
    | exact h

section InnDiag

theorem ggPsiInnerDiag_of_innDiagKind {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    {G₀ : Subgroup G} (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) {x : G}
    (hxN : x ∈ Subgroup.normalizer (G₀ : Set G))
    (hcen : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥)
    (α : MulAut (↥G₀ ⧸ Subgroup.center ↥G₀))
    (hα : ∀ l l' : ↥G₀, (l' : G) = x⁻¹ * l * x →
      α (QuotientGroup.mk l) = QuotientGroup.mk l')
    {labK : GLALabel} (hG2 : labK.tag ≠ .G2der) (hF4 : labK.tag ≠ .twF4)
    (hF4' : labK.tag ≠ .twF4der) (h : Y10GField.InnDiagKind (↥G₀ ⧸ Subgroup.center ↥G₀) labK α) :
    GGPsiInnerDiag (ggU t n f).D ψ x := by
  let e : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃*
      (↥G₀ ⧸ Subgroup.center ↥G₀) ⧸ Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  have he : ∀ s, e s = QuotientGroup.mk s := fun s => by
    rw [MulEquiv.symm_apply_eq, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  obtain ⟨-, lab, hlab, hraw⟩ := h
  have hlabK : lab = labK := by
    obtain ⟨_, _, _, _, -, -, -, hl, -⟩ := Canonical.largeEvenRawDatum_exists hraw
    exact hl
  replace hraw := largeEvenRawDatumLegacy_of_canonical_of_tag (hlabK ▸ hG2) (hlabK ▸ hF4)
    (hlabK ▸ hF4') hraw
  have hmark : LargeEvenMarking ↥G₀ (fun lab' R _ I _ θ₀ => lab' = labK ∧
      ∃ u ∈ I, LargeEvenInduces θ₀ (fun l l' => (l' : G) = x⁻¹ * l * x) u) := by
    refine ⟨hpres.2.2.1, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hlabK, u, hu, hind⟩
    refine ⟨hs, hna, e.trans θ, hlabK, u, hu, fun l l' hll' => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, he, he]
    exact hind _ _ (hα l l' hll').symm
  have hup : LargeEvenMarking ↥G₀ (fun lab' R _ I _ θ₀ =>
      (lab' = labK ∧ ∃ u ∈ I, LargeEvenInduces θ₀ (fun l l' => (l' : G) = x⁻¹ * l * x) u) ∧
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
          (∃ φ ∈ I, LargeEvenInduces θ₀ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) →
            GGPsiInnerDiag (ggU t n f).D ψ c) :=
    ggInnerDiagMpInput_holds G t n f ψ hpres.1.1 hpres.1.2 hpres.2.1.2 G₀ hpres.2.1.1 _ hmark
  obtain ⟨-, lab', -, hraw'⟩ := hup
  obtain ⟨R, _, I, F, -, -, θ₀, ⟨-, u, hu, hind⟩, himp⟩ := largeEvenRawDatum_exists hraw'
  exact himp x hxN ⟨u, hu, hind⟩

end InnDiag

theorem tag_of_markTag_exc {lab : LargeEvenLabel} {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) (h : markTag lab = t) :
    lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6 := by
  obtain ⟨tag, rank, n⟩ := lab
  subst h
  cases tag
  all_goals dsimp only [markTag] at ht ⊢
  all_goals try split_ifs at ht
  all_goals simp_all

theorem canonLabel_tag_ne_twA_of_exc {lab : GLALabel}
    (h : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6)
    (r k : ℕ) : (canonLabel lab).tag ≠ (canonLabel ⟨.twA, r, k⟩).tag := by
  rcases h with h | h | h | h | h <;> simp [canonLabel, h]

section Exceptional

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem ggPsiInnerDiag_pz_exceptional {B Bs L D J : Subgroup G} {x : G} {m : ℕ} (hm : 5 ≤ m)
    (hcfg : GGConfig 3 B Bs x L D J) (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ) :
    GGPsiInnerDiag (ggU t n f).D ψ x := by
  set G₀ := ggG0 3 B x L D J
  have hxBs : x ∈ Bs := by
    rw [hPZ.2.2.1.1]
    exact (le_sup_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (G₀ : Set G) := hPZ.2.2.2.1 hxBs
  have hx3 : x ^ 3 = 1 := hcfg.2.1.2.1.2 x hxBs
  have hq : CFSG.Open.IsQuasisimple ↥G₀ := GGTwoSig.isQuasisimple_of_presents hpres
  have hcen := Y10F.center_centerQuot_eq_bot hq
  set α := Y10F.centerQuotAut ↥G₀ (Y10F.conjAut G₀ x hxN) with hαdef
  have hα : ∀ l l' : ↥G₀, (l' : G) = x⁻¹ * l * x →
      α (QuotientGroup.mk l) = QuotientGroup.mk l' := fun l l' h => by
    rw [hαdef, Y10F.centerQuotAut_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext ((Y10F.coe_conjAut G₀ hxN l).trans h.symm))
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, CanonInn.conjAut_pow G₀ hxN hx3, map_one]
  obtain ⟨labK, hlabKt, hlabS⟩ : ∃ labK : GLALabel, markTag labK = t ∧
      Y10F.HasLabel (↥G₀ ⧸ Subgroup.center ↥G₀) (· = labK) := by
    have hG0 : Y10F.HasLabel ↥G₀ (fun lab => markTag lab = t) :=
      Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1)
        (Canonical.largeEvenMarking_of_lieModel_centerQuot hpres.2.2.1 hpres.2.2.2)
    obtain ⟨hX, lab, hlam, hraw⟩ := Y10F.hasLabel_centerQuot hG0
    obtain ⟨_, _, _, _, -, -, -, hT⟩ := Canonical.largeEvenRawDatum_exists hraw
    exact ⟨lab, hT, hX, lab, hlam, Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have htag := tag_of_markTag_exc ht hlabKt
  have hLG : L ≤ G₀ := le_ggG0_left 3 B x L D J
  have hLx : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hLO : CFSG.Open.IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp (hLx.of_le_of_le (le_inf hLG hLx.1) inf_le_right)
  have hcomp := CanonInn.isComponentOf_fixSubgroup_conjAut G₀ hxN hLO
  have h3 : 3 ∣ Nat.card ↥(L.subgroupOf G₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv]
    have h1 : Nat.card ↥(Bs ⊓ L) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_right
    rw [hPZ.2.1.2] at h1
    exact (dvd_pow_self 3 (by omega : m - 1 ≠ 0)).trans h1
  have hJ : GLAPComponent 3 (fixSubgroup α)
      ((L.subgroupOf G₀).map (QuotientGroup.mk' (Subgroup.center ↥G₀))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup
      (QuotientGroup.mk' _) (by rw [QuotientGroup.ker_mk']) (Y10F.conjAut G₀ x hxN) α
      (fun k => (Y10F.centerQuotAut_mk _ _ k).symm) (QuotientGroup.mk'_surjective _)
      Nat.prime_three
      (T263.DX.glaPComponent_of_isComponentOf_of_dvd Nat.prime_three hcomp
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.cp_three_dvd_quotient_center _
          hcomp.2.2 h3))
  have hlabJ : Y10F.HasLabel ↥((L.subgroupOf G₀).map (QuotientGroup.mk' (Subgroup.center ↥G₀)))
      (· = (⟨.twA, m - 1, 1⟩ : GLALabel)) := by
    have hL1 : Y10F.HasLabel ↥L (· = (⟨.twA, m - 1, 1⟩ : GLALabel)) := by
      refine largeEvenMarkingLegacy_to_canonical_carrier
        (P := fun lab _ _ _ => lab = (⟨.twA, m - 1, 1⟩ : GLALabel)) ?_
      refine largeEvenMarking_mono ?_ hPZ.1
      rintro ⟨tag, rank, k⟩ R _ I F θ ⟨⟨h1, h2, h3⟩, -⟩
      dsimp only at h1 h2 h3
      subst h1 h2 h3
      rfl
    exact CanonInn.hasLabel_map_centerQuot
      ((Y10F.hasLabel_congr (Subgroup.subgroupOfEquivOfLe hLG) _).2 hL1)
  rcases Y10GClsExc.clsExc_holds _ 3 α labK
      (by rcases htag with h | h | h | h | h <;> simp [Y10GField.FamExc, h]) Nat.prime_three
      (by norm_num) hcen hlabS hα3 with hinn | hfld
  · exact ggPsiInnerDiag_of_innDiagKind hpres hxN hcen α hα
      (by rcases htag with h | h | h | h | h <;> simp [h])
      (by rcases htag with h | h | h | h | h <;> simp [h])
      (by rcases htag with h | h | h | h | h <;> simp [h]) hinn
  ·
    exfalso
    apply canonLabel_tag_ne_twA_of_exc htag (m - 1) 1
    rcases htag with h | h | h | h | h
    · exact (Y10GField.fldExc_F4 ggLabelRigidInput_holds 3 α _ labK _ h Nat.prime_three
        (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GField.fldExc_E6 Y10GField.fixGapE6_holds ggLabelRigidInput_holds 3 α _ labK _ h
        Nat.prime_three (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GField.fldExc_E7 ggLabelRigidInput_holds 3 α _ labK _ h Nat.prime_three
        (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GField.fldExc_E8 ggLabelRigidInput_holds 3 α _ labK _ h Nat.prime_three
        (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GField.fldExc_twE6 Y10GField.fixGapTwE6_holds ggLabelRigidInput_holds 3 α _ labK
        _ h Nat.prime_three (by norm_num) hcen hfld hα3 hlabJ hJ).2.1

end Exceptional

end CFSG.StandardType

end
