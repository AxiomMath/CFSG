module

public import CFSG.RankThree.GF2n.Tim79a34TwBound
public import CFSG.RankThree.GF2n.Tim79a34BigEnd

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigPV_nontrivial [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (hRN : ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∃ x ∈ P, ⁅r, x⁆ ∉ V) :
    ∃ m : ↥M, (m : Mbar M) ∈ Subgroup.normalClosure (RbarM M V H : Set (Mbar M)) ∧
      ∃ x ∈ P.subgroupOf M, ⁅m, x⁆ ∉ V.subgroupOf M := by
  obtain ⟨r, hr, x, hxP, hx⟩ := hRN
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hrM : r ∈ M := by
    have h1 : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.centralizer_le_normalizer (V : Set G)
    rw [hc.normalizer_eq] at h1
    exact h1 (Subgroup.mem_inf.mp hr).2
  refine ⟨⟨r, hrM⟩, ?_, ⟨x, hPM hxP⟩, Subgroup.mem_subgroupOf.mpr hxP, ?_⟩
  · refine Subgroup.subset_normalClosure ?_
    refine Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  · intro hmem
    apply hx
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [commutatorElement_def] using this

theorem bigPV_base [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) :
    P ≤ M ∧ V ≤ M ∧ Q ≤ M ∧ (P.subgroupOf M).Normal ∧ (V.subgroupOf M).Normal ∧
      Q = inSubgroup (pCore 2) M := by
  have hQMeq : Q = inSubgroup (pCore 2) M := hc.hQ
  have hQM : Q ≤ M := hQMeq ▸ (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hVM : V ≤ M := hc.V_le_P.trans hPM
  refine ⟨hPM, hVM, hQM, (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2
    hc.M_le_normalizer_P, (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).2 ?_, hQMeq⟩
  intro m hm
  rw [hc.normalizer_eq]
  exact hm

theorem bigPV_facts [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) :
    (V.subgroupOf M ≤ P.subgroupOf M) ∧
      (P.subgroupOf M ≤ (inSubgroup (pCore 2) M).subgroupOf M) ∧
      (∀ x ∈ P.subgroupOf M, x * x ∈ V.subgroupOf M) ∧
      (∀ x ∈ P.subgroupOf M, ∀ y ∈ P.subgroupOf M, ⁅x, y⁆ ∈ V.subgroupOf M) := by
  have hQMeq : Q = inSubgroup (pCore 2) M := hc.hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hc.V_le_P (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    have h1 : (x : G) ∈ Q := hc.P_le_Q (Subgroup.mem_subgroupOf.mp hx)
    rw [hQMeq] at h1
    exact Subgroup.mem_subgroupOf.mpr h1
  · intro x hx
    have h1 := twb_mul_self_mem_V hc (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h1)
  · intro x hx y hy
    have h1 := hc.commutator_mem_V_of_mem_P (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy)
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)

theorem mem_of_mem_subgroupOf_pCore [Finite G] {M V Q P H : Subgroup G}
    (hc : MinCex M V Q P H) {q : ↥M}
    (hq : q ∈ (inSubgroup (pCore 2) M).subgroupOf M) : (q : G) ∈ Q := by
  have hQMeq : Q = inSubgroup (pCore 2) M := hc.hQ
  rw [hQMeq]
  exact Subgroup.mem_subgroupOf.mp hq

theorem bigPV_comm_QP [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (hcomQ : ∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V ⊓ wOf V H) :
    ∀ q ∈ (inSubgroup (pCore 2) M).subgroupOf M, ∀ x ∈ P.subgroupOf M,
      ⁅q, x⁆ ∈ V.subgroupOf M := by
  intro q hq x hx
  have h1 := (hcomQ (q : G) (mem_of_mem_subgroupOf_pCore hc hq) (x : G)
    (Subgroup.mem_subgroupOf.mp hx)).1
  exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)

theorem map_subtype_commutator_subgroupOf {M P : Subgroup G} (hPM : P ≤ M) :
    (⁅P.subgroupOf M, P.subgroupOf M⁆).map M.subtype = ⁅P, P⁆ := by
  have h : (P.subgroupOf M).map M.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hPM
  rw [Subgroup.map_commutator, h]

end CFSG.RankThree.GF2n.Tim79a
