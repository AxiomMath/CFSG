module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Closure.MinCex

import CFSG.GroupTheory.SupZpowersIndexTwo
import CFSG.LocalAnalysis.GH72.OuterFacts
import CFSG.OddTranspositions.HypothesisC
import CFSG.OddTranspositions.PartThree.EightSix.AlmostSimpleSub
import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.ConnLemmas
import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Wreath
import CFSG.OddTranspositions.TheoremTwo.ImageConnected
import CFSG.OddTranspositions.WidthOne
import CFSG.Quasithin.Background.A3Structure314Radical
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.OddLocalBlock
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
import TauCeti.Algebra.Group.Subgroup.ZPowers
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.Fischer.NoF25.Local
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.WreathQuotient
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.Quasithin.Background.A3Structure313SL2
import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.Schreier.MathieuOddCoreWords
import CFSG.Sporadic.Th.Max3.Data
import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

structure LocalBender {Y : Type} [Group Y] (Λ : Set Y) (d : Y) : Prop where
  transitive : ∀ x ∈ commSet Λ d, ∀ y ∈ commSet Λ d,
    ∃ g ∈ Subgroup.closure (commSet Λ d), g * x * g⁻¹ = y
  bender : CFSG.BenderSuzuki.IsBenderGroup
    (Subgroup.closure (commSet Λ d) ⧸ Subgroup.center (Subgroup.closure (commSet Λ d)))

theorem LocalBender.of_injective {Y₀ Y : Type} [Group Y₀] [Group Y] {Λ₀ : Set Y₀} {Λ : Set Y}
    (φ : Y₀ →* Y) (hφ : Function.Injective φ) {d : Y₀}
    (himage : φ '' commSet Λ₀ d = commSet Λ (φ d)) (hL : LocalBender Λ (φ d)) :
    LocalBender Λ₀ d := by
  let L₀ : Subgroup Y₀ := Subgroup.closure (commSet Λ₀ d)
  let L : Subgroup Y := Subgroup.closure (commSet Λ (φ d))
  have hLmap : L₀.map φ = L := by
    change (Subgroup.closure (commSet Λ₀ d)).map φ = Subgroup.closure (commSet Λ (φ d))
    rw [MonoidHom.map_closure, himage]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have hx' : φ x ∈ commSet Λ (φ d) := by rw [← himage]; exact ⟨x, hx, rfl⟩
    have hy' : φ y ∈ commSet Λ (φ d) := by rw [← himage]; exact ⟨y, hy, rfl⟩
    obtain ⟨g, hg, hgxy⟩ := hL.transitive (φ x) hx' (φ y) hy'
    have hgL : g ∈ L₀.map φ := by rw [hLmap]; exact hg
    obtain ⟨g₀, hg₀, hg₀eq⟩ := hgL
    refine ⟨g₀, hg₀, ?_⟩
    apply hφ
    rw [map_mul, map_mul, map_inv, hg₀eq, hgxy]
  · let e : L₀ ≃* L :=
      (Subgroup.equivMapOfInjective L₀ φ hφ).trans (MulEquiv.subgroupCongr hLmap)
    have hcenter : (Subgroup.center L₀).map e.toMonoidHom = Subgroup.center L :=
      Subgroup.map_center_eq e
    exact OddLocal.isBenderGroup_of_mulEquiv'
      (QuotientGroup.congr (Subgroup.center L₀) (Subgroup.center L) e hcenter).symm hL.bender

theorem exists_hypC_of_localBender {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ)
    (hconn : ¬ Disconnected Λ) {d : Y} (hd : d ∈ Λ) (hL : LocalBender Λ d) :
    ∃ hC₁ : HypothesisC Λ, hC₁.d = d ∧
      Halpha Λ hC₁.alpha = Subgroup.closure (commSet Λ d) ∧
      CFSG.solvableRadical (Halpha Λ hC₁.alpha) = Subgroup.center (Halpha Λ hC₁.alpha) ∧
      CFSG.BenderSuzuki.IsBenderGroup
        (Halpha Λ hC₁.alpha ⧸ Subgroup.center (Halpha Λ hC₁.alpha)) := by
  classical
  have hne : (commSet Λ d).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hle : Subgroup.closure (commSet Λ d) ≤ ⊥ := by rw [h, Subgroup.closure_empty]
    have hsub : ∀ g : Subgroup.closure (commSet Λ d), g = 1 := fun g =>
      Subtype.ext (Subgroup.mem_bot.mp (hle g.2))
    obtain ⟨a, b, hab⟩ := Asc72.IsBenderGroup.exists_not_commute hL.bender
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) b
    rw [hsub a', hsub b'] at hab
    exact hab (Commute.refl _)
  obtain ⟨e, he⟩ := hne
  have hE : IsMaxOrbit Λ d (commSet Λ d) := by
    refine ⟨e, he, ?_, ?_⟩
    · apply Eq.symm
      exact Set.Subset.antisymm
        (OddLocal.orbitIn_subset_commSet hS.normal he)
        (fun x hx => by
          obtain ⟨g, hg, hgx⟩ := hL.transitive x hx e he
          exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by rw [← hgx]; group⟩)
    · intro e' he'
      exact Set.ncard_le_ncard (OddLocal.orbitIn_subset_commSet hS.normal he')
        (Set.toFinite _)
  let hC₁ : HypothesisC Λ :=
    { setup := hS
      conn := hconn
      d := d
      hd := hd
      E := commSet Λ d
      hE := hE }
  have hL_eq : Halpha Λ hC₁.alpha = Subgroup.closure (commSet Λ d) := by
    change Subgroup.closure (DalphaStar Λ hC₁.alpha) = Subgroup.closure (commSet Λ d)
    rw [hC₁.DalphaStar_alpha]
  refine ⟨hC₁, rfl, hL_eq, ?_, ?_⟩
  ·
    rw [hL_eq]
    obtain ⟨a, b, hab⟩ := Asc72.IsBenderGroup.exists_not_commute hL.bender
    exact CFSG.Quasithin.A314.solvableRadical_eq_of_simple
      (Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))
      (Asc72.IsBenderGroup.isSimpleGroup hL.bender) ⟨a, b, hab⟩
  · rw [hL_eq]
    exact hL.bender

theorem not_almostSimpleCase_of_localBender (h1 : TheoremOne) (h91 : Theorem9_1)
    {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ) {d : Y} (hd : d ∈ Λ)
    (hL : LocalBender Λ d) : ¬ AlmostSimpleCase Y Λ := by
  intro hAS
  classical
  obtain ⟨M, hMnorm, hMmin, -, hMsimple, hCen, hidx, hW, hclass⟩ := hAS
  have : M.Normal := hMnorm
  have : IsSimpleGroup M := hMsimple
  let N : Subgroup Y := M ⊔ Subgroup.zpowers d
  have hdN : d ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  let dN : N := ⟨d, hdN⟩
  have hMleN : M ≤ N := le_sup_left
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hclass' : IsOddTranspClass (conjSet M d) := hclass d hd
  have hSN : Setup N (conjSet M d) := ⟨hclass'.1, hclass'.2.1, hclass'.2.2⟩
  have hmemΛ : ∀ {u : N}, u ∈ conjSet M d → (u : Y) ∈ Λ := by
    intro u hu
    obtain ⟨m, -, hmu⟩ := hu
    have hm : m * d * m⁻¹ ∈ Λ := hS.normal m d hd
    rwa [← hmu] at hm
  have hne : ∀ x ∈ Λ, QuotientGroup.mk' M x ≠ 1 := by
    intro x hx hx1
    have hxM : x ∈ M := (QuotientGroup.eq_one_iff x).mp hx1
    have hle : Λ ⊆ M := by
      intro y hy
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
      exact hMnorm.conj_mem x hxM g
    have htop : M = ⊤ := by
      rw [eq_top_iff, ← hS.gen]
      exact (Subgroup.closure_le M).mpr hle
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hdM : d ∉ M := fun h => hne d hd ((QuotientGroup.eq_one_iff d).mpr h)
  have hMminN : Asc72.IsMinimalNormal (M.subgroupOf N) :=
    isMinimalNormal_subgroupOf hMleN hMsimple
  have hrelIndex_le : (M.subgroupOf N).index ≤ 2 :=
    relIndex_sup_zpowers_le_two (M := M) (u := d) hd2
  have hCenN : Subgroup.centralizer ((M.subgroupOf N : Subgroup N) : Set N) = ⊥ := by
    rw [← le_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hxY : (x : Y) ∈ Subgroup.centralizer (M : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hx
      exact congrArg Subtype.val (hx ⟨(y : Y), hMleN hy⟩ hy)
    rw [hCen, Subgroup.mem_bot] at hxY
    exact hxY
  have hradN : ∀ P : Subgroup N, P.Normal → Group.IsSolvable P → P = ⊥ :=
    solvable_normal_eq_bot_of_le hMleN hMsimple hCen hMmin.2.1
  have hconnN : ¬ Disconnected (conjSet M d) :=
    EightSix.not_disconnected_conjSet_of_theoremOne h1 hMsimple hCen hdM hclass'
  have hL' : LocalBender (conjSet M d) dN := by
    refine LocalBender.of_injective (d := dN) N.subtype N.subtype_injective ?_ hL
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨hmemΛ he'.1, he'.2.1.map N.subtype, fun h => he'.2.2 (Subtype.ext h)⟩
    · intro he
      have hdeM : d * e ∈ M := by
        have hSQ : Setup (Y ⧸ M) (QuotientGroup.mk' M '' Λ) :=
          hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) hne
        have hcommQ : Commute (QuotientGroup.mk' M d) (QuotientGroup.mk' M e) :=
          (he.2.1.map (QuotientGroup.mk' M)).symm
        have heq : QuotientGroup.mk' M d = QuotientGroup.mk' M e :=
          eq_of_commute_of_widthOne hSQ hW ⟨d, hd, rfl⟩ ⟨e, he.1, rfl⟩ hcommQ
        have hde1 : QuotientGroup.mk' M (d * e) = 1 := by
          rw [map_mul, ← heq, ← map_mul, hd2, map_one]
        exact (QuotientGroup.eq_one_iff (d * e)).mp hde1
      obtain ⟨m, hm, hme⟩ :=
        exists_conj_of_mul_mem hS M hCen hclass' hd he.1 hdeM
      have heN : e ∈ N := by
        rw [← hme]
        exact N.mul_mem (N.mul_mem (hMleN hm) hdN) (N.inv_mem (hMleN hm))
      refine ⟨⟨e, heN⟩, ⟨⟨m, hm, hme.symm⟩, ?_, fun h => he.2.2 (congrArg Subtype.val h)⟩, rfl⟩
      apply Subtype.ext
      exact he.2.1.eq
  have hdmem : dN ∈ conjSet M d := ⟨1, M.one_mem, by simp [dN]⟩
  obtain ⟨hC₁, -, -, hrad_eq, hbender⟩ :=
    exists_hypC_of_localBender hSN hconnN hdmem hL'
  obtain ⟨f, hf, -, h22 | h2⟩ := h91 N (conjSet M d) hC₁ hradN hrad_eq hbender
  ·
    obtain ⟨φ⟩ := h22
    have hsimpleMsub : IsSimpleGroup (M.subgroupOf N) :=
      (Subgroup.subgroupOfEquivOfLe hMleN).isSimpleGroup
    exact not_isSimpleGroup_of_index_le_two_l2Wreath hf φ (M.subgroupOf N) inferInstance
      hrelIndex_le hsimpleMsub
  ·
    obtain ⟨⟨ψ⟩, hCidx⟩ := h2
    have hsub_le_C : M.subgroupOf N ≤ commutator N := by
      by_contra hnot
      have hlt : M.subgroupOf N ⊓ commutator N = ⊥ := by
        rcases hMminN.2.2 (M.subgroupOf N ⊓ commutator N) inferInstance inf_le_left with
          h | h
        · exact h
        · exact absurd (inf_eq_left.mp h) hnot
      have hcomm_le : ⁅M.subgroupOf N, M.subgroupOf N⁆ ≤ M.subgroupOf N ⊓ commutator N := by
        refine le_inf ?_ ?_
        · simpa using Subgroup.commutator_le_inf (M.subgroupOf N) (M.subgroupOf N)
        · have hmono := Subgroup.commutator_mono
            (show M.subgroupOf N ≤ (⊤ : Subgroup N) from le_top)
            (show M.subgroupOf N ≤ (⊤ : Subgroup N) from le_top)
          exact hmono
      rw [hlt, le_bot_iff] at hcomm_le
      have hle_central : M.subgroupOf N ≤ Subgroup.centralizer (M.subgroupOf N : Set N) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_le
      rw [hCenN, le_bot_iff] at hle_central
      exact hMminN.2.1 hle_central
    have hMsub_eq_C : M.subgroupOf N = commutator N := by
      have hrel := Subgroup.relIndex_mul_index hsub_le_C
      rw [hCidx] at hrel
      have hne : (M.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrel1 : (M.subgroupOf N).relIndex (commutator N) = 1 := by
        have hpos : 0 < (M.subgroupOf N).relIndex (commutator N) := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, zero_mul] at hrel
          exact hne hrel.symm
        omega
      exact le_antisymm hsub_le_C (Subgroup.relIndex_eq_one.mp hrel1)
    have hMsub_iso : Nonempty (M.subgroupOf N ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) :=
      hMsub_eq_C ▸ ⟨ψ⟩
    have hMiso : Nonempty (M ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hMleN).symm.trans hMsub_iso.some⟩
    have hcomm_le_M : commutator Y ≤ M := by
      obtain ⟨eM⟩ := hMiso
      have h := CFSG.GH72.commutator_le_sup_centralizer_of_outer_mul_comm M
        (CFSG.GH72.outer_mul_comm_of_mulEquiv_psl2 (F := GaloisField 2 (2 * f)) eM)
      simpa [hCen] using h
    have hindex_le : M.index ≤ 2 := by
      have hdvd : M.index ∣ 2 := by
        rw [Subgroup.index_dvd_two_iff]
        refine ⟨d, fun b => ?_⟩
        let π : Y →* Y ⧸ M := QuotientGroup.mk' M
        have hcomm_quot : ∀ a b : Y, Commute (π a) (π b) := by
          have hbot : commutator (Y ⧸ M) = ⊥ := by
            have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup Y))
              (H₂ := (⊤ : Subgroup Y)) π
            rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective M)] at hmap
            change ⁅(⊤ : Subgroup (Y ⧸ M)), ⊤⁆ = ⊥
            rw [← hmap]
            exact (Subgroup.map_eq_bot_iff (commutator Y) (f := π)).mpr
              (by rw [QuotientGroup.ker_mk']; exact hcomm_le_M)
          have hcommQ : IsMulCommutative (Y ⧸ M) :=
            (commutator_eq_bot_iff (Y ⧸ M)).mp hbot
          intro a b
          exact hcommQ.is_comm.comm (π a) (π b)
        have himg : π '' Λ = {π d} := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd hy)
            rw [map_mul, map_mul, map_inv, (hcomm_quot g d).eq, mul_assoc, mul_inv_cancel,
              mul_one]
            rfl
          · intro hx
            rw [Set.mem_singleton_iff] at hx
            exact ⟨d, hd, hx.symm⟩
        have hgen : Subgroup.closure ({π d} : Set (Y ⧸ M)) = ⊤ := by
          rw [← himg, ← MonoidHom.map_closure, hS.gen, ← MonoidHom.range_eq_map]
          exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)
        have hd2q : π d * π d = 1 := by rw [← map_mul, hd2, map_one]
        have htwo : ∀ x : Y ⧸ M, x = 1 ∨ x = π d := by
          intro x
          have hx : x ∈ Subgroup.zpowers (π d) := by
            rw [Subgroup.zpowers_eq_closure, hgen]
            exact Subgroup.mem_top x
          by_cases hd1 : π d = 1
          · left
            rw [hd1, Subgroup.zpowers_one_eq_bot] at hx
            exact Subgroup.mem_bot.mp hx
          · exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two
              (orderOf_eq_prime (by rw [pow_two]; exact hd2q) hd1)).mp hx
        rcases htwo (π b) with h | h
        · right
          exact (QuotientGroup.eq_one_iff b).mp h
        · left
          have hbd : π (b * d) = 1 := by rw [map_mul, h, hd2q]
          exact (QuotientGroup.eq_one_iff (b * d)).mp hbd
      exact Nat.le_of_dvd (by norm_num) hdvd
    exact absurd hidx (not_lt.mpr hindex_le)

end CFSG.OddTranspositions.PartThree.EightEight

end
