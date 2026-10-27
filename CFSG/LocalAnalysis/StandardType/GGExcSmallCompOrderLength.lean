module

public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrderCard

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

namespace SmallCompOrder

section Counting

variable {G : Type*} [Group G]

theorem sum_pow_eq_sum_card_filter (s : Finset G) (f : G → ℕ) (N q : ℕ)
    (hf : ∀ w ∈ s, f w ≤ N) :
    ∑ w ∈ s, q ^ f w =
      ∑ k ∈ Finset.range (N + 1), (s.filter (fun w => f w = k)).card * q ^ k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.range (N + 1))
    (fun w hw => Finset.mem_range.2 (Nat.lt_succ_of_le (hf w hw)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.1 hw).2]), Finset.sum_const,
    smul_eq_mul]

theorem card_filter_eq_zero_eq_one (s : Finset G) (f : G → ℕ) (h1 : (1 : G) ∈ s)
    (hf1 : f 1 = 0) (h0 : ∀ w ∈ s, f w = 0 → w = 1) :
    (s.filter (fun w => f w = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hfw⟩
    exact h0 w hw hfw
  · rintro rfl
    exact ⟨h1, hf1⟩

theorem card_filter_sub_eq (s : Finset G) (f : G → ℕ) (N : ℕ) (hf : ∀ w ∈ s, f w ≤ N)
    {w₀ : G} (hw₀ : ∀ w ∈ s, w₀ * w ∈ s ∧ f (w₀ * w) = N - f w) {k : ℕ} (hk : k ≤ N) :
    (s.filter (fun w => f w = N - k)).card = (s.filter (fun w => f w = k)).card := by
  have hinj : ∀ t : Finset G, Set.InjOn (fun w => w₀ * w) t :=
    fun _ _ _ _ _ h => mul_left_cancel h
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun w => w₀ * w) ?_ (hinj _)
    intro w hw
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hw ⊢
    obtain ⟨hws, hfw⟩ := hw
    obtain ⟨h1, h2⟩ := hw₀ w hws
    have := hf w hws
    exact ⟨h1, by omega⟩
  · refine Finset.card_le_card_of_injOn (fun w => w₀ * w) ?_ (hinj _)
    intro w hw
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hw ⊢
    obtain ⟨hws, hfw⟩ := hw
    obtain ⟨h1, h2⟩ := hw₀ w hws
    exact ⟨h1, by omega⟩

theorem card_filter_le_mul (s : Finset G) (f : G → ℕ) (R : Finset G)
    (hdesc : ∀ w ∈ s, 1 ≤ f w → ∃ r ∈ R, w * r ∈ s ∧ f (w * r) + 1 = f w) {k : ℕ}
    (hk : 1 ≤ k) :
    (s.filter (fun w => f w = k)).card ≤ R.card * (s.filter (fun w => f w = k - 1)).card := by
  have h : ∀ w ∈ s.filter (fun w => f w = k), ∃ r ∈ R, w * r ∈ s ∧ f (w * r) + 1 = f w :=
    fun w hw => by
      obtain ⟨hws, hfw⟩ := Finset.mem_filter.1 hw
      exact hdesc w hws (by omega)
  choose! r hr using h
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun w => (r w, w * r w)) ?_ ?_
  · intro w hw
    have hw' : w ∈ s.filter (fun w => f w = k) := hw
    obtain ⟨hrR, hws, hfw⟩ := hr w hw'
    have hk' := (Finset.mem_filter.1 hw').2
    simp only [Finset.coe_product, Finset.coe_filter, Set.mem_prod, Finset.mem_coe,
      Set.mem_ofPred_eq]
    exact ⟨hrR, hws, by omega⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    rw [h1] at h2
    exact mul_right_cancel h2

end Counting

section Weyl


variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem ncard_unionInversionRoots_le (J : Set (KernelComponent χ)) (w : WeylGroup τ) :
    (unionInversionRoots χ J w).ncard ≤ (posRoots (unionRoots χ J)).ncard :=
  Set.ncard_le_ncard (fun _ hα => hα.1) (finite_unionRoots.subset fun _ h => h.1)

theorem ncard_unionInversionRoots_one (J : Set (KernelComponent χ)) :
    (unionInversionRoots χ J 1).ncard = 0 := by
  have h : unionInversionRoots χ J 1 = ∅ := by
    ext α
    simp only [unionInversionRoots, one_smul, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]
    exact fun hα => hα.2.le
  rw [h, Set.ncard_empty]

theorem exists_simple_height_neg (J : Set (KernelComponent χ)) {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup χ J) (hne : w ≠ 1) :
    ∃ β ∈ unionSimpleRoots χ J, height (w • β) < 0 := by
  obtain ⟨β, hβ, hneg⟩ := exists_unionSimpleRoots_smul_mem_negRoots hw hne
  refine ⟨β, hβ, ?_⟩
  have h := hneg.2
  rw [height_neg] at h
  omega

theorem eq_one_of_ncard_unionInversionRoots_eq_zero (J : Set (KernelComponent χ))
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (h0 : (unionInversionRoots χ J w).ncard = 0) : w = 1 := by
  by_contra hne
  obtain ⟨β, hβ, hneg⟩ := exists_simple_height_neg J hw hne
  have hmem : β ∈ unionInversionRoots χ J w := ⟨mem_posRoots_of_mem_unionSimpleRoots hβ, hneg⟩
  have hfin : (unionInversionRoots χ J w).Finite := finite_unionRoots.subset fun _ h => h.1.1
  have := (Set.ncard_pos hfin).2 ⟨β, hmem⟩
  omega

theorem exists_descent (J : Set (KernelComponent χ)) {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup χ J) (h1 : 1 ≤ (unionInversionRoots χ J w).ncard) :
    ∃ β ∈ unionSimpleRoots χ J, (unionInversionRoots χ J (w * rootReflection β)).ncard + 1 =
      (unionInversionRoots χ J w).ncard := by
  have hne : w ≠ 1 := by
    rintro rfl
    rw [ncard_unionInversionRoots_one] at h1
    omega
  obtain ⟨β, hβ, hneg⟩ := exists_simple_height_neg J hw hne
  exact ⟨β, hβ, ncard_unionInversionRoots_mul_rootReflection hβ hneg⟩

theorem exists_longest_ncard (i : KernelComponent χ) :
    ∃ w₀ ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ)),
      ∀ w ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ)),
        (unionInversionRoots χ ({i} : Set (KernelComponent χ)) (w₀ * w)).ncard =
          (posRoots (componentRoots χ i)).ncard -
            (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w).ncard := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨w₀, hw₀, himg⟩ := exists_longest hΨ
  have hneg : ∀ x ∈ posRoots (componentRoots χ i), height (w₀ • x) < 0 := by
    intro x hx
    have hmem : w₀ • x ∈ negRoots (componentRoots χ i) := by
      rw [← himg]
      exact ⟨x, hx, rfl⟩
    have h := hmem.2
    rw [height_neg] at h
    omega
  rw [unionWeylGroup_singleton_eq]
  refine ⟨w₀, hw₀, fun w hw => ?_⟩
  have hI : unionInversionRoots χ ({i} : Set (KernelComponent χ)) (w₀ * w) =
      posRoots (componentRoots χ i) \
        unionInversionRoots χ ({i} : Set (KernelComponent χ)) w := by
    ext α
    simp only [unionInversionRoots, unionRoots_singleton_eq, Set.mem_sdiff, Set.mem_ofPred_eq,
      mul_smul]
    constructor
    · rintro ⟨hα, hh⟩
      refine ⟨hα, fun ⟨_, hwα⟩ => ?_⟩
      have hmem := smul_mem_of_mem_componentWeylGroup hΨ hw α hα.1
      have hpos : -(w • α) ∈ posRoots (componentRoots χ i) :=
        ⟨hΨ.neg_mem _ hmem, by rw [height_neg]; omega⟩
      have h := hneg _ hpos
      rw [smul_neg, height_neg] at h
      omega
    · rintro ⟨hα, hn⟩
      refine ⟨hα, ?_⟩
      have hmem := smul_mem_of_mem_componentWeylGroup hΨ hw α hα.1
      have hge : 0 ≤ height (w • α) := by
        by_contra h
        exact hn ⟨hα, by omega⟩
      have hne : height (w • α) ≠ 0 := by
        rcases IsRoot.height_pos_or_neg (hΨ.isRoot _ hmem) with h | h <;> omega
      exact hneg _ ⟨hmem, by omega⟩
  have hsub : unionInversionRoots χ ({i} : Set (KernelComponent χ)) w ⊆
      posRoots (componentRoots χ i) := by
    intro α hα
    have h := hα.1
    rwa [unionRoots_singleton_eq] at h
  rw [hI, Set.ncard_sdiff hsub (finite_unionRoots.subset fun _ h => h.1.1)]

end Weyl

end SmallCompOrder

end CFSG.StandardType
