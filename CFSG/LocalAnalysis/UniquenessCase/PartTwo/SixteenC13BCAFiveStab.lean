module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem s16c13bcA_mem_sup_zpowers {A : Type*} [Group A] {z : A} {H : Subgroup A}
    (hzc : ∀ h ∈ H, z * h = h * z) {x : A} (hx : x ∈ Subgroup.zpowers z ⊔ H) :
    ∃ (i : ℤ) (y : A), y ∈ H ∧ x = z ^ i * y := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact ⟨i, 1, H.one_mem, by rw [mul_one]⟩
    · exact ⟨0, a, ha, by rw [zpow_zero, one_mul]⟩
  | one => exact ⟨0, 1, H.one_mem, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, y, hy, rfl⟩ := ha
    obtain ⟨j, y', hy', rfl⟩ := hb
    have hc : Commute y (z ^ j) := (Commute.zpow_left (hzc y hy) j).symm
    refine ⟨i + j, y * y', H.mul_mem hy hy', ?_⟩
    rw [zpow_add, mul_assoc (z ^ i) y, ← mul_assoc y (z ^ j) y', hc.eq,
      mul_assoc (z ^ j) y y', ← mul_assoc (z ^ i) (z ^ j)]
  | inv a _ ha =>
    obtain ⟨i, y, hy, rfl⟩ := ha
    have hc : Commute (z ^ i) y := Commute.zpow_left (hzc y hy) i
    refine ⟨-i, y⁻¹, H.inv_mem hy, ?_⟩
    rw [mul_inv_rev, zpow_neg]
    exact hc.inv_inv.eq.symm

theorem s16c13bcA_mem_orbit_smul {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {z : MulAut W} (hzc : ∀ h ∈ H, z * h = h * z)
    (hT : ∀ w₁ w₂ : W, w₁ ≠ 1 → w₂ ≠ 1 → Odd (Nat.card (MulAction.orbit ↥H w₁)) →
      Odd (Nat.card (MulAction.orbit ↥H w₂)) → w₂ ∈ MulAction.orbit ↥H w₁)
    {n : W} (hn1 : n ≠ 1) (hodd : Odd (Nat.card (MulAction.orbit ↥H n))) :
    ∃ h ∈ H, h n = z n := by
  have hzn1 : z n ≠ 1 := by
    intro h
    apply hn1
    have h1 : z.symm (z n) = n := z.symm_apply_apply n
    rw [h, map_one] at h1
    exact h1.symm
  have hcomm : ∀ h : ↥H, z ((h : MulAut W) n) = (h : MulAut W) (z n) := by
    intro h
    have h1 := congrArg (fun φ : MulAut W => φ n) (hzc (h : MulAut W) h.2)
    exact h1
  have horb : MulAction.orbit ↥H (z n) = (fun w => z w) '' MulAction.orbit ↥H n := by
    ext w
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨(h : MulAut W) n, ⟨h, rfl⟩, hcomm h⟩
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, (hcomm h).symm⟩
  have hcard : Nat.card (MulAction.orbit ↥H (z n)) = Nat.card (MulAction.orbit ↥H n) := by
    rw [horb]
    exact Nat.card_image_of_injective z.injective _
  obtain ⟨h, hh⟩ := hT n (z n) hn1 hzn1 hodd (hcard ▸ hodd)
  exact ⟨(h : MulAut W), h.2, hh⟩

theorem s16c13bcA_nine_dvd_card_stab {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {z : MulAut W} (hz3 : z ^ 3 = 1) (hzH : z ∉ H)
    (hzc : ∀ h ∈ H, z * h = h * z) {n : W} (hψ : ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ n = n)
    (hzn : ∃ h ∈ H, h n = z n) :
    9 ∣ Nat.card ↥((Subgroup.zpowers z ⊔ H) ⊓ MulAction.stabilizer (MulAut W) n) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G' : Subgroup (MulAut W) := Subgroup.zpowers z ⊔ H with hG'
  set St : Subgroup (MulAut W) := MulAction.stabilizer (MulAut W) n with hSt
  set S : Subgroup (MulAut W) := G' ⊓ St with hS
  set Hn : Subgroup (MulAut W) := H ⊓ St with hHn
  have hHG' : H ≤ G' := le_sup_right
  have hHnS : Hn ≤ S := inf_le_inf hHG' le_rfl
  have hSleG' : S ≤ G' := inf_le_left
  have hHS : H ⊓ S = Hn := by
    rw [hS, hHn, ← inf_assoc, inf_eq_left.mpr hHG']
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer H := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha h' hh'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute (z ^ i) h' := Commute.zpow_left (hzc h' hh') i
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hh'
  have hnorm : (H.subgroupOf G').Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHG', hG']
    exact sup_le hzN Subgroup.le_normalizer
  haveI : (H.subgroupOf G').Normal := hnorm
  have hzG' : z ∈ G' := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  obtain ⟨h, hh, hhn⟩ := hzn
  set b : MulAut W := z⁻¹ * h with hb
  have hbG' : b ∈ G' := by
    rw [hb]
    exact G'.mul_mem
      (Subgroup.mem_sup_left (Subgroup.inv_mem (Subgroup.zpowers z) (Subgroup.mem_zpowers z)))
      (Subgroup.mem_sup_right hh)
  have hbSt : b ∈ St := by
    rw [MulAction.mem_stabilizer_iff]
    change b n = n
    rw [hb, MulAut.mul_apply, hhn, MulAut.inv_apply_self]
  have hbS : b ∈ S := by
    rw [hS]
    exact ⟨hbG', hbSt⟩
  let Q := ↥G' ⧸ H.subgroupOf G'
  let f : ↥S →* Q := (QuotientGroup.mk' (H.subgroupOf G')).comp (Subgroup.inclusion hSleG')
  have hfker : f.ker = Hn.subgroupOf S := by
    have h1 : f.ker = H.subgroupOf S := by
      show ((QuotientGroup.mk' (H.subgroupOf G')).comp
        (Subgroup.inclusion hSleG')).ker = H.subgroupOf S
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        Subgroup.comap_inclusion_subgroupOf]
    rw [h1, ← Subgroup.inf_subgroupOf_right H S, hHS]
  have hhG' : h ∈ G' := Subgroup.mem_sup_right hh
  have hh_ker : QuotientGroup.mk' (H.subgroupOf G') ⟨h, hhG'⟩ = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr hh
  have hf_b : f ⟨b, hbS⟩ = (QuotientGroup.mk' (H.subgroupOf G') ⟨z, hzG'⟩)⁻¹ := by
    have hb_eq : (⟨b, hbG'⟩ : ↥G') = (⟨z, hzG'⟩ : ↥G')⁻¹ * ⟨h, hhG'⟩ := by
      ext
      rfl
    change QuotientGroup.mk' (H.subgroupOf G') (⟨b, hSleG' hbS⟩ : ↥G') = _
    rw [show (⟨b, hSleG' hbS⟩ : ↥G') = ⟨b, hbG'⟩ from rfl, hb_eq, map_mul, map_inv,
      hh_ker, mul_one]
  have hfrange : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf G') q
    obtain ⟨i, y, hy, hgy⟩ := s16c13bcA_mem_sup_zpowers hzc g.2
    have hyG' : y ∈ G' := Subgroup.mem_sup_right hy
    have hy_ker : QuotientGroup.mk' (H.subgroupOf G') ⟨y, hyG'⟩ = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hy
    refine ⟨⟨b, hbS⟩ ^ (-i), ?_⟩
    have hg_eq : g = (⟨z, hzG'⟩ : ↥G') ^ i * ⟨y, hyG'⟩ :=
      Subtype.ext (by simpa using hgy)
    rw [map_zpow, hf_b, hg_eq, map_mul, map_zpow, hy_ker, mul_one]
    rw [inv_zpow, zpow_neg, inv_inv]
  have hQ : Nat.card Q = 3 := by
    let x : Q := QuotientGroup.mk' (H.subgroupOf G') ⟨z, hzG'⟩
    have hz3' : (⟨z, hzG'⟩ : ↥G') ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    have hx3 : x ^ 3 = 1 := by
      change (QuotientGroup.mk' (H.subgroupOf G') ⟨z, hzG'⟩) ^ 3 = 1
      rw [← map_pow, hz3', map_one]
    have hx1 : x ≠ 1 := by
      intro hx
      exact hzH ((QuotientGroup.eq_one_iff (⟨z, hzG'⟩ : ↥G')).mp hx)
    have htop : Subgroup.zpowers x = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf G') q
      obtain ⟨i, y, hy, hgy⟩ := s16c13bcA_mem_sup_zpowers hzc g.2
      have hg_eq : g = (⟨z, hzG'⟩ : ↥G') ^ i * ⟨y, Subgroup.mem_sup_right hy⟩ :=
        Subtype.ext (by simpa using hgy)
      rw [hg_eq, map_mul, map_zpow]
      have hyk : QuotientGroup.mk' (H.subgroupOf G')
          ⟨y, Subgroup.mem_sup_right hy⟩ = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr hy
      rw [hyk, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    have hcard : Nat.card Q = Nat.card (Subgroup.zpowers x) := by
      rw [htop, Subgroup.card_top]
    rw [hcard, Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcardHn : Nat.card (Hn.subgroupOf S) = Nat.card Hn :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHnS).toEquiv
  have hcardS : Nat.card ↥S = Nat.card Hn * 3 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hcardHn, hfrange, Subgroup.card_top, hQ] at h
    exact h.symm
  obtain ⟨ψ, hψH, hψord, hψn⟩ := hψ
  have hψHn : ψ ∈ Hn := ⟨hψH, MulAction.mem_stabilizer_iff.mpr hψn⟩
  have h3dvd : 3 ∣ Nat.card Hn := by
    have h := Hn.orderOf_dvd_natCard hψHn
    rwa [hψord] at h
  obtain ⟨k, hk⟩ := h3dvd
  rw [hcardS]
  exact ⟨k, by rw [hk]; ring⟩

theorem s16c13bcA_noncyclic_stab {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hzH : z ∉ H) (hzc : ∀ h ∈ H, z * h = h * z)
    (h9 : ∀ y ∈ H, orderOf y ≠ 9) {n : W} (hψ : ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ n = n)
    (hzn : ∃ h ∈ H, h n = z n) :
    ∃ X : Subgroup (MulAut W), X ≤ Subgroup.zpowers z ⊔ H ∧ IsPGroup 3 ↥X ∧ ¬ IsCyclic ↥X ∧
      ∀ x ∈ X, x n = n := by
  classical
  set Q : Subgroup (MulAut W) :=
    (Subgroup.zpowers z ⊔ H) ⊓ MulAction.stabilizer (MulAut W) n with hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 2 ∣ Nat.card ↥Q := by
    have h := s16c13bcA_nine_dvd_card_stab hz3 hzH hzc hψ hzn
    norm_num
    exact h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Q) 3 hdvd
  have hKcard : Nat.card (K.map Q.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact hK
  have hQle : Q ≤ Subgroup.zpowers z ⊔ H := inf_le_left
  have hmem : ∀ x ∈ K.map Q.subtype, x ∈ Q := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  refine ⟨K.map Q.subtype, fun x hx => hQle (hmem x hx), IsPGroup.of_card hKcard, ?_, ?_⟩
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = 9 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hKcard]
      norm_num
    have hxord : orderOf (g : MulAut W) = 9 := by
      rw [Subgroup.orderOf_coe]
      exact hord
    obtain ⟨i, y, hy, hxy⟩ := s16c13bcA_mem_sup_zpowers hzc (hQle (hmem g g.2))
    have hcy : Commute (z ^ i) y := (Commute.zpow_left (hzc y hy) i)
    have h3 : (g : MulAut W) ^ 3 = y ^ 3 := by
      rw [hxy, hcy.mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3,
        one_zpow, one_mul]
    have h9y : y ^ 9 = 1 := by
      have h1 : (g : MulAut W) ^ 9 = 1 := by
        rw [← hxord]
        exact pow_orderOf_eq_one _
      rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, ← h3, ← pow_mul]
      exact h1
    have hy3 : y ^ 3 ≠ 1 := by
      rw [← h3]
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hxord] at this
      revert this
      decide
    apply h9 y hy
    have hd9 : orderOf y ∣ 3 ^ 2 := by
      rw [show 3 ^ 2 = 9 by norm_num]
      exact orderOf_dvd_of_pow_eq_one h9y
    obtain ⟨k, hk, hky⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd9
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hky
      apply hy3
      rw [hky, one_pow]
    · exfalso
      apply hy3
      rw [← pow_orderOf_eq_one y, hky]
      norm_num
    · rw [hky]
      norm_num
  · intro x hx
    exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (hmem x hx)).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
