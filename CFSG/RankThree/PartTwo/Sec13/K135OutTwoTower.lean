module

public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoBase

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem ot_tower_level {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal] (W : Subgroup Γ)
    (hcyc : ∃ g : Γ, ∀ x : Γ, ∃ k : ℤ, g ^ k * x ∈ N) :
    ∃ a ∈ W, ∀ w ∈ W, ∃ m : ℤ, a ^ m * w ∈ N := by
  obtain ⟨g, hg⟩ := hcyc
  have hQ : IsCyclic (Γ ⧸ N) := by
    have hmem : ∀ y : Γ, (QuotientGroup.mk y : Γ ⧸ N) ∈
        Subgroup.zpowers (QuotientGroup.mk g : Γ ⧸ N) := by
      intro y
      obtain ⟨k, hk⟩ := hg y
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-k, ?_⟩
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, zpow_neg, inv_inv]
      exact hk
    refine ⟨⟨(QuotientGroup.mk g : Γ ⧸ N), fun x => ?_⟩⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hmem y
  haveI := hQ
  obtain ⟨γ, hγ⟩ : ∃ γ : (W.map (QuotientGroup.mk' N)),
      ∀ x : (W.map (QuotientGroup.mk' N)), x ∈ Subgroup.zpowers γ :=
    IsCyclic.exists_generator
  obtain ⟨a, haW, hγa⟩ := Subgroup.mem_map.mp γ.2
  refine ⟨a, haW, fun w hw => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (hγ ⟨QuotientGroup.mk' N w, Subgroup.mem_map_of_mem _ hw⟩)
  have h1 : (γ : Γ ⧸ N) ^ k = QuotientGroup.mk' N w := by
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h
    exact h
  rw [← hγa, ← map_zpow (QuotientGroup.mk' N) a k] at h1
  simp only [QuotientGroup.mk'_apply] at h1
  refine ⟨-k, ?_⟩
  rw [zpow_neg]
  exact QuotientGroup.eq.mp h1

theorem ot_tower_inner_of_pgroup {X : Type*} [Group X] (D₁ : Subgroup (MulAut X))
    (ha : ∀ δ ∈ D₁, ∀ k : ℕ, δ ^ (2 ^ k) ∈ (MulAut.conj : X →* MulAut X).range →
      δ ∈ (MulAut.conj : X →* MulAut X).range)
    (V : Subgroup (MulAut X)) (hV : IsPGroup 2 V) {d : MulAut X} (hdV : d ∈ V) (hdD : d ∈ D₁) :
    d ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨k, hk⟩ := hV ⟨d, hdV⟩
  have hk' : d ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  exact ha d hdD k (by rw [hk']; exact Subgroup.one_mem _)

theorem outTwoGen_of_tower {X : Type*} [Group X] [Finite X]
    (D₁ D₂ : Subgroup (MulAut X)) [D₁.Normal] [D₂.Normal]
    (ha : ∀ δ ∈ D₁, ∀ k : ℕ, δ ^ (2 ^ k) ∈ (MulAut.conj : X →* MulAut X).range →
      δ ∈ (MulAut.conj : X →* MulAut X).range)
    (hb : ∃ g₁ ∈ D₂, ∀ x ∈ D₂, ∃ k : ℤ, g₁ ^ k * x ∈ D₁)
    (hc : ∃ g₂ : MulAut X, ∀ x : MulAut X, ∃ k : ℤ, g₂ ^ k * x ∈ D₂) :
    OutTwoGen X := by
  unfold OutTwoGen
  intro V hV
  obtain ⟨a, haV, ha'⟩ := ot_tower_level D₂ V hc
  have hcyc2 : ∃ g : D₂, ∀ x : D₂, ∃ k : ℤ, g ^ k * x ∈ D₁.subgroupOf D₂ := by
    obtain ⟨g₁, hg₁D₂, hg₁⟩ := hb
    refine ⟨⟨g₁, hg₁D₂⟩, fun x => ?_⟩
    obtain ⟨k, hk⟩ := hg₁ x.1 x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
  obtain ⟨c', hc'V, hc'⟩ := ot_tower_level (D₁.subgroupOf D₂) (V.subgroupOf D₂) hcyc2
  have hcV : (c' : MulAut X) ∈ V := Subgroup.mem_subgroupOf.mp hc'V
  refine ⟨a, haV, (c' : MulAut X), hcV, ?_⟩
  intro v hv
  obtain ⟨m₁, hm₁⟩ := ha' v hv
  have hv₁V : a ^ m₁ * v ∈ V := mul_mem (zpow_mem haV m₁) hv
  have hw'V : (⟨a ^ m₁ * v, hm₁⟩ : D₂) ∈ V.subgroupOf D₂ :=
    Subgroup.mem_subgroupOf.mpr hv₁V
  obtain ⟨m₂, hm₂⟩ := hc' _ hw'V
  have hd1 : (c' : MulAut X) ^ m₂ * (a ^ m₁ * v) ∈ D₁ := by
    have h := Subgroup.mem_subgroupOf.mp hm₂
    simpa using h
  have hdV : (c' : MulAut X) ^ m₂ * (a ^ m₁ * v) ∈ V := mul_mem (zpow_mem hcV m₂) hv₁V
  have hdInn := ot_tower_inner_of_pgroup D₁ ha V hV hdV hd1
  have hv_eq : a ^ (-m₁) * (c' : MulAut X) ^ (-m₂) * ((c' : MulAut X) ^ m₂ * (a ^ m₁ * v)) = v := by
    group
  have hmemC : a ^ (-m₁) * (c' : MulAut X) ^ (-m₂) ∈
      Subgroup.closure ({a, (c' : MulAut X)} : Set (MulAut X)) :=
    mul_mem (zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (zpow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
  have key : a ^ (-m₁) * (c' : MulAut X) ^ (-m₂) * ((c' : MulAut X) ^ m₂ * (a ^ m₁ * v)) ∈
      Subgroup.closure ({a, (c' : MulAut X)} : Set (MulAut X)) ⊔
        (MulAut.conj : X →* MulAut X).range :=
    mul_mem (Subgroup.mem_sup_left hmemC) (Subgroup.mem_sup_right hdInn)
  rw [hv_eq] at key
  exact key

end CFSG.RankThree.PartTwo.Sec13.F135Last
