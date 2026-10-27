module

public import CFSG.Walter.J1.A5Inv
public import CFSG.Walter.J1.Signalizer

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem ncard_commute_t : {u : G | orderOf u = 2 ∧ u * h.t = h.t * u}.ncard = 31 := by
  have ht2 := h.t_mul_t
  have htinv := h.t_inv
  set A := {f : G | f ∈ h.F ∧ f ^ 2 = 1 ∧ f ≠ 1}
  set A₁ := {f : G | f ∈ h.F ∧ f ^ 2 = 1}
  have hA : A.ncard = 15 := A5Sub.ncard_involutions h.iso
  have hA₁ : A₁.ncard = 16 := by
    have : A₁ = insert 1 A := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, A₁, A]
      constructor
      · rintro ⟨hf, hf2⟩
        by_cases hf1 : f = 1
        · exact Or.inl hf1
        · exact Or.inr ⟨hf, hf2, hf1⟩
      · rintro (rfl | ⟨hf, hf2, -⟩)
        · exact ⟨h.F.one_mem, one_pow 2⟩
        · exact ⟨hf, hf2⟩
    rw [this, Set.ncard_insert_of_notMem (fun h1 => h1.2.2 rfl), hA]
  have hset : {u : G | orderOf u = 2 ∧ u * h.t = h.t * u} = A ∪ (fun f => h.t * f) '' A₁ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, A, A₁]
    constructor
    · rintro ⟨hu, hut⟩
      obtain ⟨hu2, hu1⟩ := orderOf_eq_two_iff.mp hu
      rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hut) with
        huF | huF
      · exact Or.inl ⟨huF, by rw [pow_two]; exact hu2, hu1⟩
      · refine Or.inr ⟨h.t * u, ⟨huF, ?_⟩, ?_⟩
        · rw [pow_two]
          calc h.t * u * (h.t * u) = h.t * (u * h.t) * u := by group
            _ = h.t * (h.t * u) * u := by rw [hut]
            _ = 1 := by rw [← mul_assoc, ht2, one_mul, hu2]
        · rw [← mul_assoc, ht2, one_mul]
    · rintro (⟨hf, hf2, hf1⟩ | ⟨f, ⟨hf, hf2⟩, rfl⟩)
      · exact ⟨orderOf_eq_two_iff.mpr ⟨by rw [← pow_two]; exact hf2, hf1⟩, h.commute_of_mem_F hf⟩
      · have hft := h.commute_of_mem_F hf
        refine ⟨orderOf_eq_two_iff.mpr ⟨?_, fun h1 => h.t_not_mem ?_⟩, ?_⟩
        · calc h.t * f * (h.t * f) = h.t * (f * h.t) * f := by group
            _ = h.t * (h.t * f) * f := by rw [hft]
            _ = 1 := by rw [← mul_assoc, ht2, one_mul, ← pow_two, hf2]
        · have : h.t = f⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact h.F.inv_mem hf
        · rw [mul_assoc, hft, ← mul_assoc]
  have hdisj : Disjoint A ((fun f => h.t * f) '' A₁) := by
    rw [Set.disjoint_left]
    rintro _ ⟨htf, -, -⟩ ⟨f, ⟨hf, -⟩, rfl⟩
    apply h.t_not_mem
    have : h.t = h.t * f * f⁻¹ := by group
    rw [this]
    exact h.F.mul_mem htf (h.F.inv_mem hf)
  rw [hset, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ (mul_right_injective h.t),
    hA, hA₁]

include h in
theorem ncard_commute_involution {s : G} (hs : orderOf s = 2) :
    {u : G | orderOf u = 2 ∧ u * s = s * u}.ncard = 31 := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hs
  rw [← hg]
  exact (h.conj g).ncard_commute_t

theorem ncard_commute_t_inv {x : G} (hxF : x ∈ h.F) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    {u : G | orderOf u = 2 ∧ u * h.t = h.t * u ∧ u * x * u⁻¹ = x⁻¹}.ncard = 6 := by
  have ht2 := h.t_mul_t
  have htinv := h.t_inv
  have hxt := h.commute_of_mem_F hxF
  set A := {f : G | f ∈ h.F ∧ f ^ 2 = 1 ∧ f ≠ 1 ∧ f * x * f⁻¹ = x⁻¹}
  have hA : A.ncard = 3 := A5Sub.ncard_inv_three h.iso hxF hx3 hx1
  have htx : h.t * x * h.t⁻¹ = x := by rw [← hxt, mul_inv_cancel_right]
  have hset : {u : G | orderOf u = 2 ∧ u * h.t = h.t * u ∧ u * x * u⁻¹ = x⁻¹} =
      A ∪ (fun f => h.t * f) '' A := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, A]
    constructor
    · rintro ⟨hu, hut, hux⟩
      obtain ⟨hu2, hu1⟩ := orderOf_eq_two_iff.mp hu
      rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hut) with
        huF | huF
      · exact Or.inl ⟨huF, by rw [pow_two]; exact hu2, hu1, hux⟩
      · refine Or.inr ⟨h.t * u, ⟨huF, ?_, fun h1 => ?_, ?_⟩, ?_⟩
        · rw [pow_two]
          calc h.t * u * (h.t * u) = h.t * (u * h.t) * u := by group
            _ = h.t * (h.t * u) * u := by rw [hut]
            _ = 1 := by rw [← mul_assoc, ht2, one_mul, hu2]
        · have hut' : u = h.t := by
            have : u = h.t⁻¹ := eq_inv_of_mul_eq_one_right h1
            rw [this, htinv]
          rw [hut', htx] at hux
          apply hx1
          have h2 : x * x = 1 := by
            calc x * x = x * x⁻¹ := by rw [← hux]
              _ = 1 := mul_inv_cancel x
          rw [pow_three, h2, mul_one] at hx3
          exact hx3
        · rw [mul_inv_rev, show h.t * u * x * (u⁻¹ * h.t⁻¹) = h.t * (u * x * u⁻¹) * h.t⁻¹ by
            group, hux, show h.t * x⁻¹ * h.t⁻¹ = (h.t * x * h.t⁻¹)⁻¹ by group, htx]
        · rw [← mul_assoc, ht2, one_mul]
    · rintro (⟨hf, hf2, hf1, hfx⟩ | ⟨f, ⟨hf, hf2, hf1, hfx⟩, rfl⟩)
      · exact ⟨orderOf_eq_two_iff.mpr ⟨by rw [← pow_two]; exact hf2, hf1⟩,
          h.commute_of_mem_F hf, hfx⟩
      · have hft := h.commute_of_mem_F hf
        refine ⟨orderOf_eq_two_iff.mpr ⟨?_, fun h1 => h.t_not_mem ?_⟩, ?_, ?_⟩
        · calc h.t * f * (h.t * f) = h.t * (f * h.t) * f := by group
            _ = h.t * (h.t * f) * f := by rw [hft]
            _ = 1 := by rw [← mul_assoc, ht2, one_mul, ← pow_two, hf2]
        · have : h.t = f⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact h.F.inv_mem hf
        · rw [mul_assoc, hft, ← mul_assoc]
        · rw [mul_inv_rev, show h.t * f * x * (f⁻¹ * h.t⁻¹) = h.t * (f * x * f⁻¹) * h.t⁻¹ by
            group, hfx, show h.t * x⁻¹ * h.t⁻¹ = (h.t * x * h.t⁻¹)⁻¹ by group, htx]
  have hdisj : Disjoint A ((fun f => h.t * f) '' A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨htf, -, -, -⟩ ⟨f, ⟨hf, -, -, -⟩, rfl⟩
    apply h.t_not_mem
    have : h.t = h.t * f * f⁻¹ := by group
    rw [this]
    exact h.F.mul_mem htf (h.F.inv_mem hf)
  rw [hset, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ (mul_right_injective h.t),
    hA]

include h in
theorem ncard_inv_six {w : G} (hw : orderOf w = 6) :
    {u : G | orderOf u = 2 ∧ u * w * u⁻¹ = w⁻¹}.ncard = 6 := by
  set s := w ^ 3
  set x := w ^ 4
  have hs : orderOf s = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hw]; norm_num), hw]
  have hx : orderOf x = 3 := by
    rw [orderOf_pow' w (by norm_num), hw]
    norm_num
  have hxs : x * s = w := by
    simp only [x, s]
    rw [← pow_add, show 4 + 3 = 6 + 1 by norm_num, pow_succ, ← hw, pow_orderOf_eq_one, one_mul]
  have hcomm : x * s = s * x := by simp only [x, s]; rw [← pow_add, ← pow_add, add_comm]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (orderOf_eq_two_iff.mp hs).1
  have hset : {u : G | orderOf u = 2 ∧ u * w * u⁻¹ = w⁻¹} =
      {u : G | orderOf u = 2 ∧ u * s = s * u ∧ u * x * u⁻¹ = x⁻¹} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu, huw⟩
      refine ⟨hu, ?_, ?_⟩
      · have : u * s * u⁻¹ = s := by
          have h1 : u * s * u⁻¹ = s⁻¹ := by
            simp only [s]
            rw [← conj_pow, huw, inv_pow]
          rw [h1, hsinv]
        calc u * s = u * s * u⁻¹ * u := by group
          _ = s * u := by rw [this]
      · simp only [x]
        rw [← conj_pow, huw, inv_pow]
    · rintro ⟨hu, hus, hux⟩
      refine ⟨hu, ?_⟩
      rw [← hxs, show u * (x * s) * u⁻¹ = (u * x * u⁻¹) * (u * s * u⁻¹) by group, hux,
        show u * s * u⁻¹ = s by rw [hus, mul_inv_cancel_right], mul_inv_rev, hsinv]
      exact (Commute.inv_left (show Commute x s from hcomm)).eq
  rw [hset]
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hs
  have hxC : x ∈ Subgroup.centralizer ({(h.conj g).t} : Set G) := by
    rw [hg, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hxF : x ∈ (h.conj g).F := (h.conj g).mem_F_of_odd hxC (by rw [hx]; decide)
  have h1 := (h.conj g).ncard_commute_t_inv hxF (by rw [← hx]; exact pow_orderOf_eq_one x)
    (fun h0 => by rw [h0, orderOf_one] at hx; omega)
  rw [hg] at h1
  exact h1

end JankoHyp

end CFSG.Walter.J1
