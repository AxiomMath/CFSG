module

public import CFSG.RankThree.PartOne.HNB.KComponent
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S11.SecTenSeven
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartOne.S10.Defs
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)
open scoped Pointwise

namespace Actor

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} (a : Actor G A L)

theorem H_ne_top (h : SteinbergBM.SectionTenSetup G 5 A) : a.H ≠ ⊤ :=
  haveI : IsSimpleGroup G := h.1
  centralizer_singleton_ne_top_of_simple h.2.1 a.b_ne_one

theorem isKGroup_H (h : SteinbergBM.SectionTenSetup G 5 A) : CFSG.IsKGroup a.H :=
  h.2.2.1 a.H (a.H_ne_top h)

theorem evenRank_H (h : SteinbergBM.SectionTenSetup G 5 A) : CFSG.Assembly.evenRank a.H ≤ 3 :=
  (Sec9A.evenRank_subgroup_le a.H).trans (sectionTenSetup_evenRank_eq h).le

theorem twoLocalOddRank_H (h : SteinbergBM.SectionTenSetup G 5 A) :
    CFSG.twoLocalOddRank a.H ≤ 3 := by
  rw [SteinbergBY.twoLocalOddRank_eq_evenRank]
  exact a.evenRank_H h

end Actor

structure Successor {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L) where
  X : Subgroup a.H
  hX : X ∈ thetaComponents 5 a.H
  hKX : a.K.subgroupOf a.H ≤ X

namespace Successor

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a : Actor G A L}
  (s : Successor a)

theorem exists_successor (hS : SchreierFor InCatalog) (h : SteinbergBM.SectionTenSetup G 5 A)
    (a : Actor G A L) : Nonempty (Successor a) := by
  obtain ⟨X, hX, hKX⟩ := local_theta_component_embedding_frontier hS a.H (a.isKGroup_H h)
    (a.evenRank_H h) 5 (by norm_num) (sectionTenSetup_three_lt h) a.cH a.orderOf_cH _
    a.KH_mem_thetaComponentsAt
  exact ⟨⟨X, hX, hKX⟩⟩

theorem mem_normalizer_of_pow_eq_one (h : SteinbergBM.SectionTenSetup G 5 A) {g : a.H}
    (hg : g ^ 5 = 1) : g ∈ Subgroup.normalizer (s.X : Set a.H) := by
  have hord : ∃ k : ℕ, orderOf g = 5 ^ k := by
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hg
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h1⟩
  exact selected_prime_elements_normalize_theta_components.1 a.H (a.evenRank_H h) 5
    (by norm_num) (sectionTenSetup_three_lt h) g hord s.X s.hX

theorem A0_le_normalizer (h : SteinbergBM.SectionTenSetup G 5 A) :
    a.A0.subgroupOf a.H ≤ Subgroup.normalizer (s.X : Set a.H) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro g hg
  refine s.mem_normalizer_of_pow_eq_one h (Subtype.ext ?_)
  have hA := a.isElementaryAbelian_A0
  have := elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := a.A0) (g : G)
    (Subgroup.mem_subgroupOf.mp hg)
  simpa using this

theorem R_le_normalizer (h : SteinbergBM.SectionTenSetup G 5 A) :
    a.R.subgroupOf a.H ≤ Subgroup.normalizer (s.X : Set a.H) := by
  have hX5 := fun {g : a.H} (hg : g ^ 5 = 1) => s.mem_normalizer_of_pow_eq_one h hg
  have hz : IsElementaryAbelian 5 (Subgroup.zpowers a.c) := a.isElementaryAbelian_zpowers_c
  set N' : Subgroup G := (Subgroup.normalizer (s.X : Set a.H)).map a.H.subtype with hN'
  have hR : a.R ≤ N' := by
    refine Subgroup.commutator_le.mpr fun u hu g hg => ?_
    have huH : u ∈ a.H := a.U_le_H hu
    have hgH : g ∈ a.H := (Subgroup.zpowers_le.mpr a.c_mem_H) hg
    have hg5 : g ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 5)
      (A := Subgroup.zpowers a.c) g hg
    set uH : a.H := ⟨u, huH⟩ with huH_def
    set gH : a.H := ⟨g, hgH⟩ with hgH_def
    have hgH5 : gH ^ 5 = 1 := Subtype.ext hg5
    have h1 : uH * gH * uH⁻¹ ∈ Subgroup.normalizer (s.X : Set a.H) :=
      hX5 (by rw [conj_pow, hgH5]; simp)
    have h2 : gH⁻¹ ∈ Subgroup.normalizer (s.X : Set a.H) := hX5 (by rw [inv_pow, hgH5, inv_one])
    refine ⟨uH * gH * uH⁻¹ * gH⁻¹, (Subgroup.normalizer _).mul_mem h1 h2, ?_⟩
    simp [commutatorElement_def, huH_def, hgH_def]
  intro r hr'
  obtain ⟨n, hn, hnr⟩ := hR (Subgroup.mem_subgroupOf.mp hr')
  have : n = r := Subtype.ext hnr
  exact this ▸ hn

theorem theta_eq : aschbacherSolvableCore 5 s.X =
    (aschbacherSolvableCore 5 a.H).subgroupOf s.X :=
  aschbacherSolvableCore_eq_subgroupOf (by norm_num) s.hX.2.1

end Successor

end CFSG.RankThree.PartOne.HNB
