module

public import CFSG.OddTranspositions.PartThree.LocalBenderBasic
public import CFSG.OddTranspositions.Width

import CFSG.GroupTheory.OddCoreQuotient
import CFSG.OddTranspositions.WidthSylowSetup
import CFSG.Timmesfeld.Bridge.Asc72YWidth
import CFSG.RankThree.PartOne.S12.ZStarStep
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
import CFSG.Assembly.QuasithinDefs
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.Defs
import CFSG.Timmesfeld.Bridge.Asc72XEnd

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

theorem sylow_inter_le_centSet {G : Type} [Group G] {D : Set G} (hD : IsOddTransp D)
    {z a b c : G} (S : Sylow 2 G)
    (ha : a ∈ D ∩ (S : Set G)) (hb : b ∈ D ∩ (S : Set G)) (hc : c ∈ D ∩ (S : Set G))
    (hz : z = a * b * c) : D ∩ (S : Set G) ⊆ centSet D z := by
  intro d hd
  have hcomm : ∀ x ∈ D ∩ (S : Set G), ∀ y ∈ D ∩ (S : Set G), Commute x y := fun x hx y hy =>
    hD.commute_of_isPGroup S.isPGroup' hx.1 hy.1 hx.2 hy.2
  refine ⟨hd.1, ?_⟩
  rw [hz]
  exact ((hcomm d hd a ha).mul_right (hcomm d hd b hb)).mul_right (hcomm d hd c hc)

theorem exists_sylow_of_centSet_triple {G : Type} [Group G] {D : Set G} (hS : Setup G D)
    {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (hmul : ∀ d ∈ centSet D z, ∀ e ∈ centSet D z, d ≠ e → Commute d e → d * e * z ∈ D) :
    ∃ S : Sylow 2 G, u ∈ S ∧ v ∈ S ∧ u * v * z ∈ S := by
  classical
  have hdD : u * v * z ∈ D := hmul u hu v hv huv hc
  have hpair := pairwise_commute_of_mem_centSet hu hv hc
  have hcomm3 : ∀ x ∈ ({u, v, u * v * z} : Finset G),
      ∀ y ∈ ({u, v, u * v * z} : Finset G), x ≠ y → Commute x y := by
    intro x hx y hy hxy
    exact hpair (by simpa using hx) (by simpa using hy) hxy
  have hsub3 : (↑({u, v, u * v * z} : Finset G) : Set G) ⊆ D := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu.1
    · exact hv.1
    · exact hdD
  obtain ⟨S, hSS⟩ := exists_sylow_of_pairwise_commuting_of_setup hS hsub3 hcomm3
  exact ⟨S, hSS (by simp), hSS (by simp), hSS (by simp)⟩

theorem exists_sylow_inter_data {G : Type} [Group G] {D : Set G} (hS : Setup G D)
    {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (hmul : ∀ d ∈ centSet D z, ∀ e ∈ centSet D z, d ≠ e → Commute d e → d * e * z ∈ D) :
    ∃ S : Sylow 2 G, u ∈ D ∩ (S : Set G) ∧ v ∈ D ∩ (S : Set G) ∧
      u * v * z ∈ D ∩ (S : Set G) ∧ z ∈ S ∧ z * z = 1 ∧ z = u * v * (u * v * z) := by
  have hdD : u * v * z ∈ D := hmul u hu v hv huv hc
  have hz2 : z * z = 1 := mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc hdD
  have hzuvd : z = u * v * (u * v * z) :=
    eq_mul_mul_of_mul_mul_mem hS.oddT hu hv hc
  obtain ⟨S, huS, hvS, hdS⟩ := exists_sylow_of_centSet_triple hS hu hv huv hc hmul
  have hzS : z ∈ S := by
    rw [hzuvd]
    exact S.mul_mem (S.mul_mem huS hvS) hdS
  exact ⟨S, ⟨hu.1, huS⟩, ⟨hv.1, hvS⟩, ⟨hdD, hdS⟩, hzS, hz2, hzuvd⟩

theorem commute_of_mem_sylow_of_conj_eq {G : Type} [Group G] {D : Set G}
    (hS : Setup G D) {z u v : G} (S : Sylow 2 G)
    (hu : u ∈ D ∩ (S : Set G)) (hv : v ∈ D ∩ (S : Set G))
    (hd : u * v * z ∈ D ∩ (S : Set G))
    (hz : z = u * v * (u * v * z))
    (hL : D ∩ (S : Set G) ⊆ centSet D z)
    (hconj : ∀ g : G, g * z * g⁻¹ ∈ localGroup D z → g * z * g⁻¹ = z) :
    ∀ s ∈ S, Commute s z := by
  intro s hs
  have hcL : ∀ t ∈ D ∩ (S : Set G), s * t * s⁻¹ ∈ localGroup D z := fun t ht =>
    mem_localGroup_of_mem
      (hL ⟨hS.normal s t ht.1, S.mul_mem (S.mul_mem hs ht.2) (S.inv_mem hs)⟩)
  have hmem : s * z * s⁻¹ ∈ localGroup D z := by
    have e1 : s * z * s⁻¹ =
        (s * u * s⁻¹) * (s * v * s⁻¹) * (s * (u * v * z) * s⁻¹) := by
      calc s * z * s⁻¹ = s * (u * v * (u * v * z)) * s⁻¹ := by rw [← hz]
        _ = _ := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hcL u hu) (hcL v hv)) (hcL _ hd)
  have h := hconj s hmem
  show s * z = z * s
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [h]

theorem exists_conj_commute_of_solvable_radical_bot {G : Type} [Group G] [Finite G]
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ g : G, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ≠ z := by
  have hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → ∀ n ∈ N, n * z = z * n := by
    intro N hNn hNodd n hn
    have hN1 : N = ⊥ := hrad N hNn (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd)
    rw [hN1] at hn
    rw [Subgroup.mem_bot] at hn
    rw [hn]
    exact Commute.one_left z
  have hnc : z ∉ Subgroup.center G := by
    intro hzcG
    have hZ : Subgroup.center G = ⊥ :=
      hrad (Subgroup.center G) inferInstance
        (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
    rw [hZ] at hzcG
    exact hz1 (Subgroup.mem_bot.mp hzcG)
  obtain ⟨g, hgne, hgc⟩ :=
    CFSG.RankThree.PartOne.exists_commuting_conj_of_not_central hz2 hodd hnc
  exact ⟨g, hgc, hgne⟩

theorem not_exists_two_commute_of_conj_eq {G : Type} [Group G] {D : Set G}
    (hS : Setup G D) {z a : G} (S : Sylow 2 G)
    (haz : Commute a z) (haconj : IsConj z a) (hane : a ≠ z)
    (hLcomm : ∀ d ∈ D ∩ (S : Set G), ∀ e ∈ D ∩ (S : Set G), Commute d e)
    (hmulL : ∀ d ∈ D ∩ (S : Set G), ∀ e ∈ D ∩ (S : Set G), d ≠ e →
      d * e * z ∈ D ∩ (S : Set G))
    (hconj : ∀ g : G, g * z * g⁻¹ ∈ localGroup D z → g * z * g⁻¹ = z) :
    ¬ ∃ d ∈ D ∩ (S : Set G), ∃ e ∈ D ∩ (S : Set G), d ≠ e ∧ Commute a d ∧ Commute a e := by
  rintro ⟨d, hd, e, he, hde, had, hae⟩
  have hf := hmulL d hd e he hde
  have haf : Commute a (d * e * z) := (had.mul_right hae).mul_right haz
  have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hd.1
  have hee : e * e = 1 := hS.oddT.mul_self_eq_one he.1
  have hc' := hLcomm d hd e he
  have h1 : z = d * e * (d * e * z) := by
    calc z = (d * d) * (e * e) * z := by rw [hdd, hee, one_mul, one_mul]
      _ = d * (d * e) * e * z := by group
      _ = d * (e * d) * e * z := by rw [hc'.eq]
      _ = d * e * (d * e * z) := by group
  have hzloc : z ∈ localGroup D a := by
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_localGroup_of_mem ⟨hd.1, had.symm⟩)
      (mem_localGroup_of_mem ⟨he.1, hae.symm⟩)) (mem_localGroup_of_mem ⟨hf.1, haf.symm⟩)
  obtain ⟨k, hk⟩ := isConj_iff.mp haconj
  rw [← hk] at hzloc
  have h2 := hconj (g := k⁻¹) (by simpa using conj_mem_localGroup_of_mem hS.normal hzloc)
  apply hane
  rw [← hk]
  calc k * z * k⁻¹ = k * (k⁻¹ * z * k⁻¹⁻¹) * k⁻¹ := by rw [h2]
    _ = z := by group

theorem ncard_inter_sylow_le_three {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) {z a : G} (S : Sylow 2 G)
    (hz2 : z * z = 1) (hzD : z ∉ D)
    (hLz : ∀ d ∈ D ∩ (S : Set G), Commute d z)
    (hmulL : ∀ d ∈ D ∩ (S : Set G), ∀ e ∈ D ∩ (S : Set G), d ≠ e →
      d * e * z ∈ D ∩ (S : Set G))
    (haa : a * a = 1) (haz : Commute a z)
    (haL : ∀ d ∈ D ∩ (S : Set G), a * d * a⁻¹ ∈ D ∩ (S : Set G))
    (hfix : ¬ ∃ d ∈ D ∩ (S : Set G), ∃ e ∈ D ∩ (S : Set G), d ≠ e ∧
      Commute a d ∧ Commute a e) :
    (D ∩ (S : Set G)).ncard ≤ 3 := by
  by_contra h4
  push Not at h4
  refine hfix (CFSG.Timmesfeld.Bridge.Asc72.YRank.exists_two_commute (D ∩ (S : Set G)) hz2
    (fun d hd => hS.oddT.mul_self_eq_one hd.1) hLz
    (fun d hd e he => hS.oddT.commute_of_isPGroup S.isPGroup' hd.1 he.1 hd.2 he.2)
    hmulL (fun h => hzD h.1) haa haz haL ?_)
  omega

theorem widthLe_three_of_mul_mem_of_conj_eq {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {z u v : G} (hz1 : z ≠ 1) (hzD : z ∉ D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (hmul : ∀ d ∈ centSet D z, ∀ e ∈ centSet D z, d ≠ e → Commute d e → d * e * z ∈ D)
    (hconj : ∀ g : G, g * z * g⁻¹ ∈ localGroup D z → g * z * g⁻¹ = z) :
    WidthLe D 3 := by
  classical
  obtain ⟨S₀, hu₀, hv₀, hd₀, hzS, hz2, hzuvd⟩ :=
    exists_sylow_inter_data hS hu hv huv hc hmul
  have hLcomm : ∀ d ∈ D ∩ (S₀ : Set G), ∀ e ∈ D ∩ (S₀ : Set G), Commute d e :=
    fun d hd e he => hS.oddT.commute_of_isPGroup S₀.isPGroup' hd.1 he.1 hd.2 he.2
  have hLC : D ∩ (S₀ : Set G) ⊆ centSet D z :=
    sylow_inter_le_centSet hS.oddT S₀ hu₀ hv₀ hd₀ hzuvd
  have hLz : ∀ d ∈ D ∩ (S₀ : Set G), Commute d z := fun d hd => (hLC hd).2
  have hmulL : ∀ d ∈ D ∩ (S₀ : Set G), ∀ e ∈ D ∩ (S₀ : Set G), d ≠ e →
      d * e * z ∈ D ∩ (S₀ : Set G) := by
    intro d hd e he hde
    exact ⟨hmul d (hLC hd) e (hLC he) hde (hLcomm d hd e he),
      S₀.mul_mem (S₀.mul_mem hd.2 he.2) hzS⟩
  have hzc : ∀ s ∈ S₀, Commute s z :=
    commute_of_mem_sylow_of_conj_eq hS S₀ hu₀ hv₀ hd₀ hzuvd hLC hconj
  obtain ⟨g, hgc', hgne⟩ := exists_conj_commute_of_solvable_radical_bot hrad hz1 hz2
  have hbb : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2, mul_one,
      mul_inv_cancel]
  obtain ⟨a, haS, hane, haconj, haa, haz⟩ :=
    CFSG.GroupTheory.exists_conj_mem_sylow_of_commute S₀ hzc (isConj_iff.mpr ⟨g, rfl⟩) hgc' hgne hbb
  have haL : ∀ d ∈ D ∩ (S₀ : Set G), a * d * a⁻¹ ∈ D ∩ (S₀ : Set G) := fun d hd =>
    ⟨hS.normal a d hd.1, S₀.mul_mem (S₀.mul_mem haS hd.2) (S₀.inv_mem haS)⟩
  have hfix : ¬ ∃ d ∈ D ∩ (S₀ : Set G), ∃ e ∈ D ∩ (S₀ : Set G), d ≠ e ∧
      Commute a d ∧ Commute a e :=
    not_exists_two_commute_of_conj_eq hS S₀ haz haconj hane hLcomm hmulL hconj
  have hLcard : (D ∩ (S₀ : Set G)).ncard ≤ 3 :=
    ncard_inter_sylow_le_three hS S₀ hz2 hzD hLz hmulL haa haz haL hfix
  refine widthLe_of_sylow_bound hS (fun T => ?_)
  rw [Set.inter_comm (↑T : Set G) D,
    CFSG.Timmesfeld.Bridge.OddTransp.ncard_inter_sylow_eq hS.normal S₀ T]
  exact hLcard

end CFSG.OddTranspositions.PartThree
