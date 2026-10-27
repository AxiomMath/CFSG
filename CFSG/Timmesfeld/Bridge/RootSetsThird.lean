module

public import CFSG.Timmesfeld.RootInductionStruct
public import CFSG.Timmesfeld.Bridge.LocalA
public import CFSG.Timmesfeld.Bridge.RootSetsCases
public import CFSG.Timmesfeld.Bridge.RootSetsKernel

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

theorem isPGroup_sup_rootGroup (hD : IsRootInvolutionSet D) {d d' : G} (hd : d ∈ D)
    (hd' : d' ∈ D) (hrel : Commute d d' ∨ orderOf (d * d') = 4) :
    IsPGroup 2 (rootGroup D d ⊔ rootGroup D d' : Subgroup G) := by
  rcases hrel with hc | h4
  · rw [rootGroup, rootGroup, ← Subgroup.closure_union]
    refine isPGroup_closure_of_pairwise ?_ ?_
    · rintro x (hx | hx) y (hy | hy) -
      · exact commute_of_mem_rootSet hd hx hy
      · exact commute_of_mem_rootGroup_of_commute' hd' (rootSet_subset_rootGroup D d hx)
          (rootSet_subset_rootGroup D d' hy) hc
      · exact (commute_of_mem_rootGroup_of_commute' hd' (rootSet_subset_rootGroup D d hy)
          (rootSet_subset_rootGroup D d' hx) hc).symm
      · exact commute_of_mem_rootSet hd' hx hy
    · rintro x (hx | hx)
      · exact hD.mul_self_eq_one hx.1
      · exact hD.mul_self_eq_one hx.1
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
    have hP : IsPGroup 2 (rootGroup D d' ⊔ Subgroup.closure S : Subgroup G) :=
      (isPGroup_rootGroup hD hd').to_sup_of_normal_right' hK hnorm
    have hAK : rootGroup D d ≤ Subgroup.closure S := by
      rw [rootGroup]
      exact Subgroup.closure_mono Set.subset_union_left
    have hle : (rootGroup D d ⊔ rootGroup D d' : Subgroup G) ≤
        rootGroup D d' ⊔ Subgroup.closure S :=
      sup_le (hAK.trans le_sup_right) le_sup_left
    exact hP.to_le hle

theorem commute_or_special_conj {x u : G} (hx : x * x = 1) (hu : u * u = 1)
    (h : orderOf (x * u) = 4 ∨ orderOf (x * u) = 8) :
    Commute x (u * x * u⁻¹) ∨ orderOf (x * (u * x * u⁻¹)) = 4 := by
  have hsq : x * (u * x * u⁻¹) = (x * u) ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right hu, pow_two]
    group
  have hx2 : orderOf ((x * u) ^ 2) = orderOf (x * u) / 2 := by
    rw [orderOf_pow' _ two_ne_zero]
    rcases h with h | h <;> rw [h] <;> norm_num
  have hy : u * x * u⁻¹ * (u * x * u⁻¹) = 1 := by
    rw [show u * x * u⁻¹ * (u * x * u⁻¹) = u * (x * x) * u⁻¹ by group, hx, mul_one,
      mul_inv_cancel]
  rcases h with h | h
  · left
    have h2 : orderOf (x * (u * x * u⁻¹)) = 2 := by rw [hsq, hx2, h]
    have hpow : (x * (u * x * u⁻¹)) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    exact (commute_iff_mul_sq_eq_one hx hy).2 hpow
  · right
    rw [hsq, hx2, h]

theorem rootPairBound_of_rootFixThird (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hT : RootFixThird D) : RootPairBound D := by
  intro d hd a ha b hb hab hnD g hnc hodd
  have hu2 := (commute_of_mem_rootSet_pair hD hd ha hb).2
  have hxD : g * d * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hd
  set x := g * d * g⁻¹ with hx
  set u := a * b with hu
  have hx2 := hD.mul_self_eq_one hxD
  have hyD : u * x * u⁻¹ ∈ D := conj_mem_of_isClass hclass u hxD
  have h48 : orderOf (x * u) = 4 ∨ orderOf (x * u) = 8 := by
    rcases orderOf_mul_cases hclass hD hd ha hb hxD with (h | ⟨m, hm, h⟩) | h | h
    · exact absurd (mem_of_odd_orderOf_mul hclass hD hxD hu2 h) hnD
    · exact absurd h (hT d hd a ha b hb hab hnD x hxD hnc hodd m hm)
    · exact Or.inl h
    · exact Or.inr h
  have hR := isPGroup_sup_rootGroup hD hxD hyD (commute_or_special_conj hx2 hu2 h48)
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hmap : (rootGroup D x ⊔ rootGroup D (u * x * u⁻¹)).map (MulAut.conj u).toMonoidHom =
      rootGroup D x ⊔ rootGroup D (u * x * u⁻¹) := by
    rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass,
      show u * (u * x * u⁻¹) * u⁻¹ = x by
        rw [huinv]; simp only [← mul_assoc, hu2, one_mul]; rw [mul_assoc, hu2, mul_one],
      sup_comm]
  have hnorm : Subgroup.zpowers u ≤
      Subgroup.normalizer ((rootGroup D x ⊔ rootGroup D (u * x * u⁻¹) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact RootSubgroup.mem_normalizer_of_map_eq hmap
  have hzp : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [Subgroup.zpowers_eq_closure]
    exact isPGroup_closure_of_pairwise (Set.pairwise_singleton _ Commute)
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hu2)
  have hug : g * u * g⁻¹ ∈ rootGroup D x := by
    rw [hx, rootGroup_conj hclass]
    exact ⟨u, mul_mem_rootGroup ha hb, rfl⟩
  refine (hzp.to_sup_of_normal_right' hR hnorm).to_le ?_
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hug)

theorem rootClosure_of_rootFixThird (h : Hyp G D) (hT : RootFixThird D) : RootClosure D := by
  have := h.finite
  exact rootClosure_of_rootPairBound h (rootPairBound_of_rootFixThird h.isClass h.root hT)

@[expose] def ThirdKindStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStruct G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootFixThird D

end CFSG.Timmesfeld.Bridge
