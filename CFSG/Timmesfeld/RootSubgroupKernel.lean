module

public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def FixesOpposite (D : Set G) (d w : G) : Prop :=
  w ∈ rootGroup D d ∧
    ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) → w * c * w⁻¹ ∈ rootSet D c

namespace RootSubgroup

theorem mem_normalizer_of_map_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem mem_normalizer_closure_of_involution {S : Set G} {g : G} (hg : g * g = 1)
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hle : ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hS y hy
    | one => simp
    | mul y z _ _ ihy ihz =>
      have := (Subgroup.closure S).mul_mem ihy ihz
      simpa [mul_assoc] using this
    | inv y _ ih =>
      have := (Subgroup.closure S).inv_mem ih
      simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hle x, fun hx => ?_⟩
  have := hle _ hx
  rwa [hginv, show g * (g * x * g) * g = (g * g) * x * (g * g) by group, hg, one_mul,
    mul_one] at this

theorem isPGroup_closure_pair (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d d' w w' : G} (hd : d ∈ D)
    (hd' : d' ∈ D) (hw : FixesOpposite D d w) (hw' : FixesOpposite D d' w') :
    IsPGroup 2 (Subgroup.closure ({w, w'} : Set G)) := by
  have hww := mul_self_eq_one_of_mem_rootGroup hD hd hw.1
  have hww' := mul_self_eq_one_of_mem_rootGroup hD hd' hw'.1
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hd' with hc | h4 | ⟨hodd, hc⟩
  ·
    have hcomm : Commute w w' := commute_of_mem_rootGroup_of_commute' hd' hw.1 hw'.1 hc
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
      refine mem_normalizer_closure_of_involution ht'2 ?_
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
    · exact Subgroup.mem_sup_right (Subgroup.closure_mono Set.subset_union_left hw.1)
    · exact Subgroup.mem_sup_left hw'.1
  ·
    have hmem := hw.2 d' hd' hc hodd
    have hmap : (rootGroup D d').map (MulAut.conj w).toMonoidHom = rootGroup D d' :=
      (rootGroup_conj hclass w d').symm.trans (rootGroup_eq_of_mem hmem)
    have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (rootGroup D d' : Set G) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_map_eq hmap
    have hzp : IsPGroup 2 (Subgroup.zpowers w) := by
      rw [Subgroup.zpowers_eq_closure]
      exact isPGroup_closure_of_pairwise (Set.pairwise_singleton w Commute)
        (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hww)
    refine (hzp.to_sup_of_normal_right' (isPGroup_rootGroup hD hd') hnorm).to_le ?_
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    · exact Subgroup.mem_sup_right hw'.1

theorem fixesOpposite_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d w : G}
    (hw : FixesOpposite D d w) (g : G) : FixesOpposite D (g * d * g⁻¹) (g * w * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [rootGroup_conj hclass]
    exact Subgroup.mem_map_of_mem _ hw.1
  intro c' hc' hnc hodd
  have hc : g⁻¹ * c' * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hc'
  have hcc : g * (g⁻¹ * c' * g) * g⁻¹ = c' := by group
  have hnc' : ¬ Commute d (g⁻¹ * c' * g) := fun h => hnc (by
    rw [← hcc]; exact (Commute.conj_iff g).2 h)
  have hodd' : Odd (orderOf (d * (g⁻¹ * c' * g))) := by
    rw [← orderOf_conj_eq g, show g * (d * (g⁻¹ * c' * g)) * g⁻¹ = g * d * g⁻¹ * c' by group]
    exact hodd
  have h1 := hw.2 _ hc hnc' hodd'
  have h2 : g * (w * (g⁻¹ * c' * g) * w⁻¹) * g⁻¹ ∈ rootSet D (g * (g⁻¹ * c' * g) * g⁻¹) := by
    rw [rootSet_conj hclass]
    exact ⟨_, h1, rfl⟩
  rw [hcc] at h2
  rwa [show g * (w * (g⁻¹ * c' * g) * w⁻¹) * g⁻¹ = g * w * g⁻¹ * c' * (g * w * g⁻¹)⁻¹ by group]
    at h2

end RootSubgroup

theorem eq_one_of_fixesOpposite [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    {d w : G} (hd : d ∈ D) (hw : FixesOpposite D d w) : w = 1 := by
  have hmem : w ∈ CFSG.pCore 2 G := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    exact RootSubgroup.isPGroup_closure_pair hclass hD hd (conj_mem_of_isClass hclass g hd) hw
      (RootSubgroup.fixesOpposite_conj hclass hw g)
  rwa [hO2 _ (CFSG.BaerSuzuki.Helpers.pCore_normal 2)
    (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2), Subgroup.mem_bot] at hmem

theorem Hyp.eq_one_of_fixesOpposite (h : Hyp G D) {d w : G} (hd : d ∈ D)
    (hw : FixesOpposite D d w) : w = 1 :=
  have := h.finite
  Timmesfeld.eq_one_of_fixesOpposite h.isClass h.root h.twoCore hd hw

end CFSG.Timmesfeld
