module

public import CFSG.Timmesfeld.Closure.LS

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

@[expose] def RootPairBound (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∉ D →
    ∀ g : G, ¬ Commute d (g * d * g⁻¹) → Odd (orderOf (d * (g * d * g⁻¹))) →
      IsPGroup 2 (Subgroup.closure ({a * b, g * (a * b) * g⁻¹} : Set G))

theorem mul_mem_rootGroup {d a b : G} (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d) :
    a * b ∈ rootGroup D d :=
  (rootGroup D d).mul_mem (rootSet_subset_rootGroup D d ha) (rootSet_subset_rootGroup D d hb)

theorem mul_ne_one_of_mem_rootSet (hD : IsRootInvolutionSet D) {d a b : G}
    (hb : b ∈ rootSet D d) (hab : a ≠ b) : a * b ≠ 1 := by
  intro h1
  apply hab
  rw [← hD.inv_eq hb.1]
  exact eq_inv_of_mul_eq_one_left h1

theorem mul_notMem_of_notMem_rootSet [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {d a b : G} (hd : d ∈ D) (ha : a ∈ rootSet D d) (hb : b ∈ rootSet D d)
    (hnot : a * b ∉ rootSet D d) : a * b ∉ D :=
  fun hmem => hnot (mem_rootSet_of_mem_rootGroup hclass hd hmem (mul_mem_rootGroup ha hb))

theorem isPGroup_closure_of_not_opposite (hD : IsRootInvolutionSet D) {d d' w w' : G}
    (hd : d ∈ D) (hd' : d' ∈ D) (hw : w ∈ rootGroup D d) (hw' : w' ∈ rootGroup D d')
    (hrel : Commute d d' ∨ orderOf (d * d') = 4) :
    IsPGroup 2 (Subgroup.closure ({w, w'} : Set G)) := by
  have hww := mul_self_eq_one_of_mem_rootGroup hD hd hw
  have hww' := mul_self_eq_one_of_mem_rootGroup hD hd' hw'
  rcases hrel with hc | h4
  · have hcomm : Commute w w' := commute_of_mem_rootGroup_of_commute' hd' hw hw' hc
    refine isPGroup_two_closure_pair hww hww' (k := 1) ?_
    rw [pow_one, ← (commute_iff_mul_sq_eq_one hww hww').1 hcomm]
  ·
    have hF : ∀ t ∈ rootSet D d, ∀ t' ∈ rootSet D d',
        (t * t') ^ 2 ∈ D ∧ Commute t ((t * t') ^ 2) ∧ Commute t' ((t * t') ^ 2) := by
      intro t ht t' ht'
      obtain ⟨h1, h2, h3, -⟩ := sq_mem_of_orderOf_eq_four hD ht.1 ht'.1
        (orderOf_mul_eq_four_of_mem_rootSet hD hd hd' ht ht' h4)
      exact ⟨h1, h2, h3⟩
    set F : Set G := {f | ∃ t ∈ rootSet D d, ∃ t' ∈ rootSet D d', f = (t * t') ^ 2} with hFdef
    have hFD : ∀ f ∈ F, f ∈ D := by
      rintro f ⟨t, ht, t', ht', rfl⟩
      exact (hF t ht t' ht').1
    have hFT : ∀ f ∈ F, ∀ t ∈ rootSet D d, Commute t f := by
      rintro f ⟨t₀, ht₀, t₀', ht₀', rfl⟩ t ht
      obtain ⟨hfD, h1, -⟩ := hF t₀ ht₀ t₀' ht₀'
      exact (ht.2 _ hfD).2 ((ht₀.2 _ hfD).1 h1)
    have hFT' : ∀ f ∈ F, ∀ t' ∈ rootSet D d', Commute t' f := by
      rintro f ⟨t₀, ht₀, t₀', ht₀', rfl⟩ t' ht'
      obtain ⟨hfD, -, h1⟩ := hF t₀ ht₀ t₀' ht₀'
      exact (ht'.2 _ hfD).2 ((ht₀'.2 _ hfD).1 h1)
    have hFF : ∀ f ∈ F, ∀ f' ∈ F, Commute f f' := by
      rintro f hf f' ⟨t₁, ht₁, t₁', ht₁', rfl⟩
      exact (((hFT f hf t₁ ht₁).symm.mul_right (hFT' f hf t₁' ht₁').symm)).pow_right 2
    set S : Set G := rootSet D d ∪ F with hSdef
    have hSc : S.Pairwise Commute := by
      rintro x (hx | hx) y (hy | hy) -
      · exact commute_of_mem_rootSet hd hx hy
      · exact hFT y hy x hx
      · exact (hFT x hx y hy).symm
      · exact hFF x hx y hy
    have hS2 : ∀ x ∈ S, x * x = 1 := by
      rintro x (hx | hx)
      · exact hD.mul_self_eq_one hx.1
      · exact hD.mul_self_eq_one (hFD x hx)
    have hK : IsPGroup 2 (Subgroup.closure S) := isPGroup_closure_of_pairwise hSc hS2
    have hnorm : rootGroup D d' ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
      rw [rootGroup, Subgroup.closure_le]
      intro t' ht'
      have ht'2 := hD.mul_self_eq_one ht'.1
      refine RootSubgroup.mem_normalizer_closure_of_involution ht'2 ?_
      rintro x (hx | hx)
      · have hx2 := hD.mul_self_eq_one hx.1
        have : t' * x * t'⁻¹ = x * (x * t') ^ 2 := by
          rw [inv_eq_of_mul_eq_one_right ht'2, pow_two]
          simp only [← mul_assoc, hx2, one_mul]
        rw [this]
        exact (Subgroup.closure S).mul_mem (Subgroup.subset_closure (Or.inl hx))
          (Subgroup.subset_closure (Or.inr ⟨x, hx, t', ht', rfl⟩))
      · rw [(hFT' x hx t' ht').eq, mul_inv_cancel_right]
        exact Subgroup.subset_closure (Or.inr hx)
    refine ((isPGroup_rootGroup hD hd').to_sup_of_normal_right' hK hnorm).to_le ?_
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_right (Subgroup.closure_mono Set.subset_union_left hw)
    · exact Subgroup.mem_sup_left hw'

theorem eq_one_of_forall_opposite [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {d w : G} (hd : d ∈ D) (hw : w ∈ rootGroup D d)
    (h : ∀ g : G, ¬ Commute d (g * d * g⁻¹) → Odd (orderOf (d * (g * d * g⁻¹))) →
      IsPGroup 2 (Subgroup.closure ({w, g * w * g⁻¹} : Set G))) : w = 1 := by
  have hmem : w ∈ CFSG.pCore 2 G := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hdg : g * d * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hd
    have hwg : g * w * g⁻¹ ∈ rootGroup D (g * d * g⁻¹) := by
      rw [rootGroup_conj hclass]
      exact ⟨w, hw, rfl⟩
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hdg with hc | h4 | ⟨hodd, hnc⟩
    · exact isPGroup_closure_of_not_opposite hD hd hdg hw hwg (Or.inl hc)
    · exact isPGroup_closure_of_not_opposite hD hd hdg hw hwg (Or.inr h4)
    · exact h g hnc hodd
  rwa [hO2 _ (CFSG.BaerSuzuki.Helpers.pCore_normal 2)
    (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2), Subgroup.mem_bot] at hmem

theorem rootClosure_of_rootPairBound (h : Hyp G D) (hB : RootPairBound D) : RootClosure D := by
  have := h.finite
  intro d hd a ha b hb hab
  by_contra hnot
  have hnD := mul_notMem_of_notMem_rootSet h.isClass hd ha hb hnot
  exact mul_ne_one_of_mem_rootSet h.root hb hab (eq_one_of_forall_opposite h.isClass h.root
    h.twoCore hd (mul_mem_rootGroup ha hb) (hB d hd a ha b hb hab hnD))

end CFSG.Timmesfeld.Bridge
