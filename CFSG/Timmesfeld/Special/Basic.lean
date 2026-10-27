module

public import CFSG.Timmesfeld.RootSubgroupBasic

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

namespace Special

theorem commutatorElement_eq_mul_sq {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    ⁅a, b⁆ = (a * b) ^ 2 := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb,
    pow_two, mul_assoc (a * b)]

theorem commutatorElement_mem_of_mem_closure {S : Set G} {N : Subgroup G}
    (hN : ∀ n ∈ N, ∀ s ∈ S, Commute n s) (hgen : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : ⁅x, y⁆ ∈ N := by
  have hN' : ∀ n ∈ N, ∀ g ∈ Subgroup.closure S, Commute n g := by
    intro n hn g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hN n hn s hs
    | one => exact Commute.one_right n
    | mul g₁ g₂ _ _ h₁ h₂ => exact h₁.mul_right h₂
    | inv g _ h => exact h.inv_right
  have h1 : ∀ g ∈ Subgroup.closure S, ∀ t ∈ S, ⁅g, t⁆ ∈ N := by
    intro g hg t ht
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hgen s hs t ht
    | one => simp
    | mul g₁ g₂ hg₁ _ h₁ h₂ =>
      rw [commutatorElement_mul_left_eq_conj_mul, (hN' _ h₂ g₁ hg₁).symm.eq,
        mul_inv_cancel_right]
      exact N.mul_mem h₂ h₁
    | inv g hg h =>
      rw [commutatorElement_inv_left, ← commutatorElement_inv,
        (hN' _ (N.inv_mem h) g hg).symm.inv_left.eq, inv_mul_cancel_right]
      exact N.inv_mem h
  induction hy using Subgroup.closure_induction with
  | mem t ht => exact h1 x hx t ht
  | one => simp
  | mul y₁ y₂ hy₁ _ h₁ h₂ =>
    have hc : y₁ * ⁅x, y₂⁆ * y₁⁻¹ = ⁅x, y₂⁆ := by
      rw [(hN' _ h₂ y₁ hy₁).symm.eq, mul_inv_cancel_right]
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc, mul_assoc, ← mul_assoc y₁, hc]
    exact N.mul_mem h₁ h₂
  | inv y hy h =>
    rw [commutatorElement_inv_right, ← commutatorElement_inv,
      (hN' _ (N.inv_mem h) y hy).symm.inv_left.eq, inv_mul_cancel_right]
    exact N.inv_mem h

theorem upperCentralSeries_two_eq_top {K : Subgroup G}
    (h : ⁅K, K⁆ ≤ Subgroup.centralizer (K : Set G)) : Subgroup.upperCentralSeries K 2 = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro w
  have hc : ⁅(x : G), (y : G)⁆ ∈ Subgroup.centralizer (K : Set G) :=
    h (Subgroup.commutator_mem_commutator x.2 y.2)
  apply Subtype.ext
  simpa [commutatorElement_def] using (Subgroup.mem_centralizer_iff.mp hc w w.2)

end Special

open Special

section SpecialPair

variable {d e : G}

theorem mul_sq_mem_of_mem_rootSet (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) {a b : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D e) :
    (a * b) ^ 2 ∈ D :=
  hD.sq_mem ha.1 hb.1 (orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hb h4)

theorem commute_mul_sq_of_mem_rootGroup_left (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a b g : G} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D e) (hg : g ∈ rootGroup D d) : Commute g ((a * b) ^ 2) := by
  obtain ⟨hf, haf, -, -⟩ := sq_mem_of_orderOf_eq_four hD ha.1 hb.1
    (orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hb h4)
  exact commute_of_mem_rootGroup_of_commute hg hf ((ha.2 _ hf).1 haf)

theorem commute_mul_sq_of_mem_rootGroup_right (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a b g : G} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D e) (hg : g ∈ rootGroup D e) : Commute g ((a * b) ^ 2) := by
  obtain ⟨hf, -, hbf, -⟩ := sq_mem_of_orderOf_eq_four hD ha.1 hb.1
    (orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hb h4)
  exact commute_of_mem_rootGroup_of_commute hg hf ((hb.2 _ hf).1 hbf)

theorem rootGroup_sq_le_centralizer (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) :
    rootGroup D ((d * e) ^ 2) ≤ Subgroup.centralizer
      ((rootGroup D d ⊔ rootGroup D e ⊔ rootGroup D ((d * e) ^ 2) : Subgroup G) : Set G) := by
  obtain ⟨hz, hdz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  rw [Subgroup.le_centralizer_iff]
  refine sup_le (sup_le ?_ ?_) ?_ <;> intro g hg <;> rw [Subgroup.mem_centralizer_iff] <;>
    intro c hc
  · exact commute_of_mem_rootGroup_of_commute' hd hc hg hdz.symm
  · exact commute_of_mem_rootGroup_of_commute' he hc hg hez.symm
  · exact commute_of_mem_rootGroup hz hc hg

theorem rootGroup_sq_subgroupOf_le_center (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) :
    (rootGroup D ((d * e) ^ 2)).subgroupOf (rootGroup D d ⊔ rootGroup D e ⊔
      rootGroup D ((d * e) ^ 2)) ≤
      Subgroup.center ↥(rootGroup D d ⊔ rootGroup D e ⊔ rootGroup D ((d * e) ^ 2)) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (rootGroup_sq_le_centralizer hD hd he h4 hx) y y.2)

theorem commutator_sup_rootGroup_le_centralizer (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    ⁅rootGroup D d ⊔ rootGroup D e, rootGroup D d ⊔ rootGroup D e⁆ ≤
      Subgroup.centralizer ((rootGroup D d ⊔ rootGroup D e : Subgroup G) : Set G) := by
  set S : Set G := rootSet D d ∪ rootSet D e with hS
  have hX : rootGroup D d ⊔ rootGroup D e = Subgroup.closure S := by
    rw [hS, Subgroup.closure_union]
    rfl
  set N : Subgroup G := Subgroup.closure
    {g | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D e, g = (a * b) ^ 2} with hN
  have hNS : ∀ n ∈ N, ∀ s ∈ S, Commute n s := by
    intro n hn s hs
    induction hn using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      rcases hs with hs | hs
      · exact (commute_mul_sq_of_mem_rootGroup_left hD hd he h4 ha hb
          (rootSet_subset_rootGroup D d hs)).symm
      · exact (commute_mul_sq_of_mem_rootGroup_right hD hd he h4 ha hb
          (rootSet_subset_rootGroup D e hs)).symm
    | one => exact Commute.one_left s
    | mul g₁ g₂ _ _ h₁ h₂ => exact h₁.mul_left h₂
    | inv g _ h => exact h.inv_left
  have hgen : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N := by
    have hmem : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, ⁅a, b⁆ ∈ N := fun a ha b hb => by
      rw [commutatorElement_eq_mul_sq (hD.mul_self_eq_one ha.1) (hD.mul_self_eq_one hb.1)]
      exact Subgroup.subset_closure ⟨a, ha, b, hb, rfl⟩
    rintro s (hs | hs) t (ht | ht)
    · rw [(commute_of_mem_rootSet hd hs ht).commutator_eq]
      exact N.one_mem
    · exact hmem s hs t ht
    · rw [← commutatorElement_inv]
      exact N.inv_mem (hmem t ht s hs)
    · rw [(commute_of_mem_rootSet he hs ht).commutator_eq]
      exact N.one_mem
  have hNc : N ≤ Subgroup.centralizer ((rootGroup D d ⊔ rootGroup D e : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hX] at hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact (hNS n hn s hs).symm.eq
    | one => rw [one_mul, mul_one]
    | mul g₁ g₂ _ _ h₁ h₂ => exact ((Commute.mul_left h₁ h₂ : Commute (g₁ * g₂) n)).eq
    | inv g _ h => exact ((Commute.inv_left h : Commute g⁻¹ n)).eq
  refine le_trans ?_ hNc
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [hX] at hx hy
  exact commutatorElement_mem_of_mem_closure hNS hgen hx hy

theorem upperCentralSeries_sup_rootGroup_eq_top (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    Subgroup.upperCentralSeries ↥(rootGroup D d ⊔ rootGroup D e) 2 = ⊤ :=
  upperCentralSeries_two_eq_top (commutator_sup_rootGroup_le_centralizer hD hd he h4)

theorem isNilpotent_sup_rootGroup (hD : IsRootInvolutionSet D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : Group.IsNilpotent ↥(rootGroup D d ⊔ rootGroup D e) :=
  ⟨⟨2, upperCentralSeries_sup_rootGroup_eq_top hD hd he h4⟩⟩

theorem nilpotencyClass_sup_rootGroup_le_two (hD : IsRootInvolutionSet D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    haveI := isNilpotent_sup_rootGroup hD hd he h4
    Group.nilpotencyClass ↥(rootGroup D d ⊔ rootGroup D e) ≤ 2 :=
  haveI := isNilpotent_sup_rootGroup hD hd he h4
  Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp
    (upperCentralSeries_sup_rootGroup_eq_top hD hd he h4)

end SpecialPair

end CFSG.Timmesfeld
