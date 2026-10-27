module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePZKnown
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZExc
import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
import CFSG.HardMathSupport.Dickson.Bal207.OrthFCArith
import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {G : Type} [Group G] [Finite G]

section SmallField

theorem false_of_pz_d4_two {B Bs L D J : Subgroup G} {x : G} {m : ℕ} (hm : 5 ≤ m)
    (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {ψ : (ggU .POmegaPlus 4 1).K →* G}
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 1).D .POmegaPlus 4 1 ψ) :
    False := by
  have hmark : CFSG.Assembly.LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab = (⟨.twA, m - 1, 1⟩ : LargeEvenLabel)) := by
    refine largeEvenMarkingLegacy_to_canonical_carrier
      (P := fun lab _ _ _ => lab = (⟨.twA, m - 1, 1⟩ : LargeEvenLabel)) ?_
    refine largeEvenMarking_mono ?_ hPZ.1
    rintro ⟨tag, rank, k⟩ R _ I F θ ⟨⟨ht, hr, hk⟩, -⟩
    dsimp only at ht hr hk
    subst ht hr hk
    rfl
  obtain ⟨lab, -, R, _, _, _, θ, -, -, hlab, hR⟩ :=
    Canonical.largeEvenMarking_exists_markedModel hmark
  subst hlab
  have hRM : LieModel R .PSU m 2 1 := by
    simpa only [MarkedModel, markTag, markRank, markChar, markDeg,
      Nat.sub_add_cancel (by omega : 1 ≤ m)] using hR
  have hLM := LieModel.of_mulEquiv θ.symm hRM
  have hLclass : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU m 2 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by omega) hLM
  have hGclass : StatedClassicalModel
      (↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J)) .POmegaPlus 4 2 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by decide) hpres.2.2.2
  have hcardL : Nat.card (↥L ⧸ Subgroup.center ↥L) = ordTwistedA (m - 1) 2 := by
    simpa only [pow_one] using (CFSG.Timmesfeld.card_statedClassicalModel_two hLclass).2.1 rfl
  have hcardG : Nat.card
      (↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J)) = ordD 4 (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hGclass).2.2.2.1 rfl
  have h11 : 11 ∣ ordTwistedA (m - 1) 2 := by
    by_cases hm5 : m = 5
    · subst m
      decide
    · exact CFSG.HardMathSupport.Dickson.Bal207.OrthFC.eleven_dvd_ordTwistedA
        (by omega) (Or.inl rfl)
  have hdvd := RCKU33.card_centerQuot_dvd (le_ggG0_left 3 B x L D J)
  rw [hcardL, hcardG] at hdvd
  exact (by decide : ¬ 11 ∣ ordD 4 (2 ^ 1)) (h11.trans hdvd)

end SmallField

section General

theorem ggPsiInnerDiag_pz_D4_of_two_le_degree {B Bs L D J : Subgroup G} {x : G} {m f : ℕ}
    (hm : 5 ≤ m) (hf : 2 ≤ f) (hcfg : GGConfig 3 B Bs x L D J)
    (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ) :
    GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ x := by
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
  obtain ⟨labK, hparams, hlabS⟩ : ∃ labK : GLALabel,
      (markTag labK = .POmegaPlus ∧ markRank labK = 4 ∧ markChar labK = 2 ∧ markDeg labK = f) ∧
      Y10F.HasLabel (↥G₀ ⧸ Subgroup.center ↥G₀) (· = labK) := by
    have hG0 : Y10F.HasLabel ↥G₀ (fun lab =>
        markTag lab = .POmegaPlus ∧ markRank lab = 4 ∧ markChar lab = 2 ∧ markDeg lab = f) :=
      Canonical.largeEvenMarking_of_lieModel_centerQuot hpres.2.2.1 hpres.2.2.2
    obtain ⟨hX, lab, hlam, hraw⟩ := Y10F.hasLabel_centerQuot hG0
    obtain ⟨_, _, _, _, -, -, -, hT⟩ := Canonical.largeEvenRawDatum_exists hraw
    exact ⟨lab, hT, hX, lab, hlam, Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hlabK : labK = (⟨.D, 4, f⟩ : GLALabel) := by
    rcases hparams with ⟨ht, hr, -, hd⟩
    rcases labK with ⟨tag, r, k⟩
    cases tag
    all_goals dsimp only [markTag] at ht
    all_goals try split_ifs at ht
    all_goals try cases ht
    all_goals
      have hr' : r = 4 := by
        simpa only [markRank, if_neg (by assumption)] using hr
      have hd' : k = f := hd
      subst r k
      rfl
  subst labK
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
  by_cases hinn : Y10GField.InnDiagKind (↥G₀ ⧸ Subgroup.center ↥G₀) ⟨.D, 4, f⟩ α
  · exact ggPsiInnerDiag_of_innDiagKind hpres hxN hcen α hα
      (by simp) (by simp) (by simp) hinn
  exfalso
  by_cases hfld : Y10GField.FieldKind (↥G₀ ⧸ Subgroup.center ↥G₀) ⟨.D, 4, f⟩ α
  · have htag := (Y10GFldOrth.fldOrth_holds _ 3 α _ ⟨.D, 4, f⟩ ⟨.twA, m - 1, 1⟩
      (by norm_num [Y10GField.FamOrth]) Nat.prime_three (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    simp [canonLabel] at htag
  · have htri := I167.triOuterD4_label ggLabelRigidInput_holds hcen hf hlabS hα3 hinn hfld hlabJ hJ
    rcases htri with h | ⟨-, h⟩ | h
    · simp [canonLabel] at h
    · have hm3 : m - 1 = 2 := by simpa [canonLabel] using h
      omega
    · simp [canonLabel] at h

theorem ggPsiInnerDiag_pz_D4 {B Bs L D J : Subgroup G} {x : G} {m : ℕ} (hm : 5 ≤ m)
    (_h3 : 3 ∣ m + 1) (hcfg : GGConfig 3 B Bs x L D J) (_hNT : GGNoTransvection 3 Bs)
    (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m) {f : ℕ}
    (ψ : (ggU .POmegaPlus 4 f).K →* G)
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ) :
    GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ x := by
  have hf : 1 ≤ f := hpres.1.1.2.1
  by_cases hf2 : 2 ≤ f
  · exact ggPsiInnerDiag_pz_D4_of_two_le_degree hm hf2 hcfg hPZ hpres
  · have hf1 : f = 1 := by omega
    subst f
    exact (false_of_pz_d4_two hm hPZ hpres).elim

end General

end CFSG.StandardType
