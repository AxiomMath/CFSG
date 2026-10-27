module

public import CFSG.RankThree.PartOne.SolD3.Outcome
public import CFSG.RankThree.PartOne.SolD3.Sz

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.SolK CFSG.GH74
open CFSG.ComponentClassification.HSFLit (HaradaInput)
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

theorem sylow_map_maximal {G : Type} [Group G] {C : Subgroup G} (R : Sylow 2 ↥C) :
    ∀ U : Subgroup G, U ≤ C → IsPGroup 2 U → (R : Subgroup ↥C).map C.subtype ≤ U →
      U = (R : Subgroup ↥C).map C.subtype := by
  intro U hUC hU2 hRU
  have hU' : IsPGroup 2 (U.subgroupOf C) :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUC).symm
  have hle : (R : Subgroup ↥C) ≤ U.subgroupOf C := fun r hr => hRU ⟨r, hr, rfl⟩
  have heq : U.subgroupOf C = (R : Subgroup ↥C) := R.is_maximal' hU' hle
  calc U = (U.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hUC).symm
    _ = (R : Subgroup ↥C).map C.subtype := by rw [heq]

theorem gen4_of_degree_three (hE2 : SolomonTimmesfeldTight) (hOrd : TightSmallGroupOrders)
    (hHar : HaradaInput) (hWC3 : WCBlockCentralizerThree) (hSz3 : SzU3SylowIndecomposable)
    {G : Type} [Group G] [Finite G] (hKP : KProper InCatalog G)
    {M X : Subgroup G} {a : G} (h : Hyp3 G M X) (hb : Blk3 X a) (hR : rOf M X ≠ ⊥) :
    SectionalTwoRankLE G 4 := by
  classical
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hev : Even (Nat.card ↥C) := by
    have hRC : rOf M X ≤ C := inf_le_right
    have hR2 : IsPGroup 2 ↥(rOf M X) :=
      (isPGroup_pCoreOf' M).of_injective (Subgroup.inclusion (inf_le_left : rOf M X ≤ pCoreOf 2 M))
        (Subgroup.inclusion_injective _)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR2
    have h1 : 1 < Nat.card ↥(rOf M X) := (Subgroup.one_lt_card_iff_ne_bot (rOf M X)).2 hR
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      omega
    have h2 : 2 ∣ Nat.card ↥(rOf M X) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hRC))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hN := h.normalizer_C_eq hb hev
  have hmax : IsMaximalTwoLocal (Subgroup.normalizer (C : Set G)) := by
    rw [hN]
    exact h.maxLocal
  have hF : Subgroup.normalizer (C : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (C : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.normalizer (C : Set G)) := by
    rw [hN]
    exact h.charTwo M h.maxLocal.1
  have hna : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨w, hw, hw1⟩ := hb.exists_ne_one
    refine ⟨a, w, fun hcomm => hw1 (hb.fix w hw ?_)⟩
    calc a * w * a⁻¹ = (w * a) * a⁻¹ := by rw [hcomm]
      _ = w := by group
  have h27 := hE2 G hKP h.simple hna C (h.tightlyEmbedded_C hb hev) hmax hF R
  have hRC : (R : Subgroup ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 ((R : Subgroup ↥C).map C.subtype) := R.isPGroup'.map _
  rcases h27 with ⟨hRO, hab, g₀, hg₀N, hg₀ne⟩ | ⟨-, hdih⟩ | ⟨hQ8, hgrp⟩ |
      ⟨⟨H, -, hHR, ⟨hHe⟩, hHidx⟩, hL34⟩ | hSz | ⟨-, hel, h4, hTI6, hNR, hWC⟩
  ·
    have hrOf : rOf M X = (R : Subgroup ↥C).map C.subtype :=
      (h.rOf_eq_pCoreOf_C hb).trans hRO.symm
    have hcfg : Cfg3 G M X a :=
      ⟨h, hb, fun r hr r' hr' => by
        rw [hrOf] at hr hr'
        exact comm_of_cyclic_or_elem hab r hr r' hr', fun c hc hc2 => by
        obtain ⟨j, hj⟩ := hc2
        rw [h.rOf_eq_pCoreOf_C hb]
        exact two_element_mem_of_sylow R hRO hc hj⟩
    have hg₀M : g₀ ∉ M := by
      intro hg
      apply hg₀ne
      refine Subgroup.ext fun z => ?_
      rw [mem_conjSubgroup, ← hrOf]
      constructor
      · intro hz
        have := h.R_normalized hg hz
        have e : g₀ * (g₀⁻¹ * z * g₀) * g₀⁻¹ = z := by group
        rw [e] at this
        exact this
      · intro hz
        have := h.R_normalized (M.inv_mem hg) hz
        simpa using this
    refine hcfg.gen4_main hHar hR hg₀M fun r hr => ?_
    have hmem : g₀ * r * g₀⁻¹ ∈ conjSubgroup g₀ ((R : Subgroup ↥C).map C.subtype) := by
      rw [mem_conjSubgroup]
      have e : g₀⁻¹ * (g₀ * r * g₀⁻¹) * g₀ = r := by group
      rw [e, ← hrOf]
      exact hr
    have := hg₀N hmem
    rwa [hN] at this
  ·
    exact gen4_of_dihedral_or_semidihedral hdih
  ·
    have hb64 : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 := by
      rcases hgrp with h' | h' | h' | h' | h'
      · exact hOrd G (Or.inl h')
      · exact hOrd G (Or.inr (Or.inl h'))
      · exact hOrd G (Or.inr (Or.inr (Or.inl h')))
      · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inl h'))))
      · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    exact gen4_of_outcome_three h hb hb64 hRC hR2 (sylow_map_maximal R) hQ8
  ·
    exact gen4_of_outcome_four hb
      (hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL34)))))) hRC hR2 hHR hHe
  ·
    exact (false_of_szU3 hSz3 h hb hSz).elim
  ·
    exfalso
    have hXC : X ≤ Subgroup.centralizer (((R : Subgroup ↥C).map C.subtype : Subgroup G) : Set G) :=
      fun x hx r hr => (Subgroup.mem_centralizer_iff.1 (hRC hr) x hx).symm
    have hNRM : Subgroup.normalizer (((R : Subgroup ↥C).map C.subtype : Subgroup G) : Set G) =
        M := by
      rw [hNR]
      exact hN
    refine hWC3 G h.simple h.charTwo _ X hel h4 hTI6 ?_ ?_ ?_ ?_ ?_ h.short h.nat hXC
    · rw [hNRM]
      exact h.maxLocal
    · rw [hNRM]
      rw [hN] at hWC
      exact hWC
    · rw [hNRM]
      exact h.unique
    · rw [hNRM]
      exact h.le
    · rw [hNRM]
      exact h.normal

end CFSG.RankThree.PartOne.SolD3
