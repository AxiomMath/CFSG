module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k329_quasisimple_of_simple_nonabelian {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : CFSG.Open.IsQuasisimple G := by
  have hcomm : ¬ IsMulCommutative G := by
    rintro ⟨hc⟩
    obtain ⟨a, b, hab⟩ := hna
    exact hab (hc.comm a b)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exact absurd ((commutator_eq_bot_iff G).1 h) hcomm
    · exact h
  · have hctr : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · exact absurd (Subgroup.center_eq_top_iff.1 h) hcomm
    have e : (G ⧸ Subgroup.center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hctr).trans (QuotientGroup.quotientBot)
    exact e.isSimpleGroup

theorem k329_isQuasisimple_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple G' := by
  obtain ⟨hp, hs⟩ := hG
  have hc : (Subgroup.center G).map (e : G →* G') = Subgroup.center G' :=
    Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : G →* G') e.surjective, ← Subgroup.map_commutator,
    hp]

private theorem k329pg8_native {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem k329pg8_not_comm {Γ : Type} [Group Γ] (h : ∀ a b : Γ, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple Γ := by
  intro hq
  have hsimple : IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := hq.2
  obtain ⟨q, hq1⟩ := exists_ne (1 : Γ ⧸ Subgroup.center Γ)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  apply hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  exact fun g => h g a

private theorem k329pg8_le_normalizer {C : Type} [Group C] {ι : Type} (Lf : ι → Subgroup C)
    (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (i : ι) :
    (⨆ j, Lf j) ≤ Subgroup.normalizer (Lf i : Set C) := by
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hc j i hji)).trans
      (Subgroup.centralizer_le_normalizer (Lf i : Set C))

private theorem k329pg8_isComponent {C : Type} [Group C] {ι : Type} (Lf : ι → Subgroup C)
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i))
    (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (i : ι) :
    CFSG.IsComponent ((Lf i).subgroupOf (⨆ j, Lf j)) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_iSup Lf i)).symm (k329pg8_native (hq i))
  · exact Subgroup.Normal.isSubnormal
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup Lf i)).2
        (k329pg8_le_normalizer Lf hc i))

theorem k329_normal_quasisimple_eq_factor {C : Type} [Group C] [Finite C] {ι : Type} [Fintype ι]
    (Lf : ι → Subgroup C) (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i))
    (hc : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥) (N : Subgroup C) (hNL : N ≤ ⨆ i, Lf i)
    (hNn : (N.subgroupOf (⨆ i, Lf i)).Normal) (hNq : CFSG.Open.IsQuasisimple ↥N) :
    ∃ i, N = Lf i := by
  let L : Subgroup C := ⨆ i, Lf i
  have hLf_le : ∀ i, Lf i ≤ L := fun i => le_iSup Lf i
  have hLf_norm : ∀ i, L ≤ Subgroup.normalizer (Lf i : Set C) := fun i => k329pg8_le_normalizer Lf hc i
  have hLf_comp : ∀ i, CFSG.IsComponent ((Lf i).subgroupOf L) :=
    fun i => k329pg8_isComponent Lf hq hc i
  by_cases hcase : ∃ i, (Lf i).subgroupOf L ≤ N.subgroupOf L
  · obtain ⟨i, hi⟩ := hcase
    have hLN : Lf i ≤ N :=
      CFSG.LocalCores.le_of_subgroupOf_le (K := Lf i) (H := N) (L := L) (hLf_le i) hi
    have hnorm : ((Lf i).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 (hNL.trans (hLf_norm i))
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (k329pg8_native hNq) hnorm with
      htop | hcenter
    · refine ⟨i, le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hLN⟩
    · exfalso
      refine (k329pg8_not_comm (Γ := ↥(Lf i)) ?_) (hq i)
      intro a b
      apply Subtype.ext
      have ha : (⟨(a : C), hLN a.2⟩ : ↥N) ∈ Subgroup.center ↥N :=
        hcenter (Subgroup.mem_subgroupOf.mpr a.2)
      have h := (Subgroup.mem_center_iff.mp ha) (⟨(b : C), hLN b.2⟩ : ↥N)
      exact congrArg (Subtype.val : ↥N → C) h.symm
  · push Not at hcase
    have hcomm : ∀ i, ⁅(Lf i).subgroupOf L, N.subgroupOf L⁆ = ⊥ := fun i =>
      (CFSG.LocalCores.component_normal_subgroup (hLf_comp i) hNn).resolve_left (hcase i)
    have hcomm' : ∀ i, ⁅Lf i, N⁆ = ⊥ := fun i => by
      have h := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf (K := Lf i) (H := N)
        (L := L) (hLf_le i) (hcomm i)
      rwa [inf_eq_left.mpr hNL] at h
    have hle_cent : L ≤ Subgroup.centralizer (N : Set C) :=
      iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm' i)
    refine absurd hNq (k329pg8_not_comm (Γ := ↥N) ?_)
    intro a b
    apply Subtype.ext
    have ha : (a : C) ∈ Subgroup.centralizer (N : Set C) := hle_cent (hNL a.2)
    exact (Subgroup.mem_centralizer_iff.mp ha (b : C) b.2).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
