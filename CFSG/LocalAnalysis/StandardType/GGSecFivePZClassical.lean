module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePZKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.StandardType.GGSecFivePZExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympB
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSymp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
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
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem classical_family_of_markTag {lab : LargeEvenLabel}
    (hchar : markChar lab = 2)
    (ht : markTag lab = .PSL ∨ markTag lab = .PSp ∨ markTag lab = .POmegaMinus ∨
      (markTag lab = .POmegaPlus ∧ markRank lab ≠ 4)) :
    Y10GField.FamLin lab ∨ (lab.tag = .B ∨ lab.tag = .C) ∨
      (Y10GField.FamOrth lab ∧ (lab.tag = .D → lab.rank ≠ 4)) := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> by_cases h2 : rank = 2 <;> by_cases h3 : rank = 3 <;>
    by_cases h4 : rank = 4 <;>
    simp_all [markTag, markRank, markChar, Y10GField.FamLin, Y10GField.FamOrth]

private theorem canonLabel_tag_ne_twA_of_classical {lab : GLALabel}
    (h : Y10GField.FamLin lab ∨ (lab.tag = .B ∨ lab.tag = .C) ∨ Y10GField.FamOrth lab)
    (r k : ℕ) : (canonLabel lab).tag ≠ (canonLabel ⟨.twA, r, k⟩).tag := by
  rcases h with (h | ⟨h, hr⟩ | ⟨h, hr⟩) | (h | h) | (⟨h, hr⟩ | ⟨h, hr2, hr3⟩)
  all_goals simp_all [canonLabel]

variable {G : Type} [Group G] [Finite G]

theorem ggPsiInnerDiag_pz_classical {B Bs L D J : Subgroup G} {x : G} {m : ℕ}
    (hm : 5 ≤ m) (_h3 : 3 ∣ m + 1) (hcfg : GGConfig 3 B Bs x L D J)
    (_hNT : GGNoTransvection 3 Bs)
    (hPZ : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m)
    {t : StatedLieTag} {n f : ℕ} (ψ : (ggU t n f).K →* G)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaMinus ∨ (t = .POmegaPlus ∧ n ≠ 4))
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ) :
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
  obtain ⟨labK, hlabKt, hlabKn, hlabKc, hlabKf, hlabS⟩ : ∃ labK : GLALabel,
      markTag labK = t ∧ markRank labK = n ∧ markChar labK = 2 ∧ markDeg labK = f ∧
        Y10F.HasLabel (↥G₀ ⧸ Subgroup.center ↥G₀) (· = labK) := by
    obtain ⟨hX, lab, hlam, hraw⟩ := Y10F.hasLabel_centerQuot
      (Canonical.largeEvenMarking_of_lieModel_centerQuot hpres.2.2.1 hpres.2.2.2)
    obtain ⟨_, _, _, _, -, -, -, hT, hR, hC, hF⟩ := Canonical.largeEvenRawDatum_exists hraw
    exact ⟨lab, hT, hR, hC, hF, hX, lab, hlam, Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hfamily := classical_family_of_markTag hlabKc (by
    simpa only [hlabKt, hlabKn] using ht)
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
  have hdich : Y10GField.InnDiagKind (↥G₀ ⧸ Subgroup.center ↥G₀) labK α ∨
      Y10GField.FieldKind (↥G₀ ⧸ Subgroup.center ↥G₀) labK α := by
    rcases hfamily with hlin | hbc | ⟨horth, h4⟩
    · exact Y10GField.ClsLin_holds _ 3 α labK hlin Nat.prime_three (by norm_num)
        hcen hlabS hα3
    · exact Y10GField.clsSympBC 3 α labK hbc Nat.prime_three (by norm_num) hlabS hα3
    · rcases Y10GClsOrth.clsOrth_holds _ 3 α labK horth Nat.prime_three (by norm_num)
          hcen hlabS hα3 with h | h | ⟨hD, hr4, -⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (h4 hD hr4).elim
  rcases hdich with hinn | hfld
  · have htag : labK.tag ≠ .G2der ∧ labK.tag ≠ .twF4 ∧ labK.tag ≠ .twF4der := by
      rcases hfamily with (h | ⟨h, -⟩ | ⟨h, -⟩) | (h | h) | ⟨(⟨h, -⟩ | ⟨h, -, -⟩), -⟩
      all_goals simp [h]
    exact ggPsiInnerDiag_of_innDiagKind hpres hxN hcen α hα
      htag.1 htag.2.1 htag.2.2 hinn
  · exfalso
    have hfam : Y10GField.FamLin labK ∨ (labK.tag = .B ∨ labK.tag = .C) ∨
        Y10GField.FamOrth labK := hfamily.imp_right (Or.imp_right And.left)
    apply canonLabel_tag_ne_twA_of_classical hfam (m - 1) 1
    rcases hfamily with hlin | hbc | ⟨horth, -⟩
    · exact (Y10GField.fldLin_of_labelDict Y10GInnLin.linLabelDict_holds _ 3 α _ labK _
        hlin Nat.prime_three (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GField.fldSymp_holds _ 3 α _ labK _ (by
          rcases hbc with h | h <;> simp [Y10GField.FamSymp, h])
        Nat.prime_three (by norm_num) hcen hfld hα3 hlabJ hJ).2.1
    · exact (Y10GFldOrth.fldOrth_holds _ 3 α _ labK _ horth Nat.prime_three
        (by norm_num) hcen hfld hα3 hlabJ hJ).2.1

end CFSG.StandardType

end
