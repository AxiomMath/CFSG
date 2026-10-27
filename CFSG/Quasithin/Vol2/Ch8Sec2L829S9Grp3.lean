module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.H13.L829N

abbrev s9gPi {G : Type} [Group G] (M H : Subgroup G) : H →* E2.StarQuot M H :=
  QuotientGroup.mk' ((kerIn M H).subgroupOf H)

theorem s9gPi_surjective {G : Type} [Group G] (M H : Subgroup G) :
    Function.Surjective (s9gPi M H) :=
  QuotientGroup.mk'_surjective _

@[expose] def s9gStar {G : Type} [Group G] (M H K : Subgroup G) (hKH : K ≤ H) :
    K →* E2.star M H K :=
  MonoidHom.codRestrict ((s9gPi M H).comp (Subgroup.inclusion hKH)) (E2.star M H K)
    (fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2))

theorem s9gStar_surjective {G : Type} [Group G] (M H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (s9gStar M H K hKH) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩

theorem s9g3_mem_star {G : Type} [Group G] {M H X : Subgroup G} {y : E2.StarQuot M H} :
    y ∈ E2.star M H X ↔ ∃ z : H, z ∈ X.subgroupOf H ∧ s9gPi M H z = y :=
  Subgroup.mem_map

theorem s9g3_star_normalizes {G : Type} [Group G] {M H A : Subgroup G} {h : G} (hhH : h ∈ H)
    (hn : ∀ a : G, a ∈ A ↔ h * a * h⁻¹ ∈ A) :
    s9gPi M H ⟨h, hhH⟩ ∈
      Subgroup.normalizer ((E2.star M H A : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨z, rfl⟩ := s9gPi_surjective M H y
  rw [s9g3_mem_star, s9g3_mem_star]
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine ⟨⟨h * w * h⁻¹, H.mul_mem (H.mul_mem hhH w.2) (H.inv_mem hhH)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact (hn _).mp (Subgroup.mem_subgroupOf.mp hw)
    · rw [← hwz, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg (s9gPi M H) (Subtype.ext (by simp [mul_assoc]))
  · rintro ⟨w, hw, hwz⟩
    refine ⟨⟨h⁻¹ * w * h, H.mul_mem (H.mul_mem (H.inv_mem hhH) w.2) hhH⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hw ⊢
      refine (hn (h⁻¹ * w * h)).mpr ?_
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp hw
    · have e : s9gPi M H ⟨h⁻¹ * w * h, H.mul_mem (H.mul_mem (H.inv_mem hhH) w.2) hhH⟩ =
          (s9gPi M H ⟨h, hhH⟩)⁻¹ * s9gPi M H w * s9gPi M H ⟨h, hhH⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg (s9gPi M H) (Subtype.ext (by simp [mul_assoc]))
      rw [e, hwz]
      group

theorem s9g3_subgroupOf_normal {G : Type} [Group G] {H K : Subgroup G}
    (hHn : H ≤ Subgroup.normalizer (K : Set G)) : (K.subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact (Subgroup.mem_normalizer_iff.mp (hHn g.2) (n : G)).mp hn

@[expose] def s9gInner {Y : Type} [Group Y] (Ks : Subgroup Y) (x : Y) : Prop :=
  ∃ z ∈ Ks, ∀ y ∈ Ks, x * y * x⁻¹ = z * y * z⁻¹

theorem s9g3_relIndex_eq {G : Type} [Group G] [Finite G] {H K T : Subgroup G}
    (hKH : K ≤ H) (hTH : T ≤ H) (hHKT : H = K ⊔ T) (hKn : (K.subgroupOf H).Normal) :
    T.relIndex K = T.relIndex H := by
  haveI := hKn
  have hKH' : K.relIndex H = K.relIndex T := by
    have hsup : (K.subgroupOf H) ⊔ (T.subgroupOf H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHKT, Subgroup.subgroupOf_self]
    have h1 := Subgroup.relIndex_sup_right (T.subgroupOf H) (K.subgroupOf H)
    rw [sup_comm, hsup, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.relIndex_subgroupOf (H := K) (K := T) (L := H) hTH
    exact h1.trans h2
  have hpos : K.relIndex T ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_inf_mul_relIndex K T H
  have h2 := Subgroup.relIndex_inf_mul_relIndex T K H
  rw [inf_eq_left.mpr hTH] at h1
  rw [inf_eq_left.mpr hKH] at h2
  rw [inf_comm K T] at h1
  rw [hKH'] at h2
  have h3 := h1.trans h2.symm
  rw [mul_comm (T.relIndex K)] at h3
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) h3).symm

theorem s9g3_map_starHom {G : Type} [Group G] {M H K T : Subgroup G} (hKH : K ≤ H) :
    ((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH) =
      (E2.star M H (T ⊓ K)).subgroupOf (E2.star M H K) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Subgroup.mem_subgroupOf, s9g3_mem_star]
    refine ⟨Subgroup.inclusion hKH b, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp hb
  · intro hy
    rw [Subgroup.mem_subgroupOf, s9g3_mem_star] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzT : (z : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hz
    refine ⟨⟨(z : G), (Subgroup.mem_inf.mp hzT).2⟩, Subgroup.mem_subgroupOf.mpr hzT, ?_⟩
    exact Subtype.ext hzy

theorem s9g3_index_odd {G : Type} [Group G] [Finite G] {M H K T : Subgroup G} (hKH : K ≤ H)
    (hTH : T ≤ H) (hHKT : H = K ⊔ T) (hKn : (K.subgroupOf H).Normal)
    (hodd : ¬ 2 ∣ (T.subgroupOf H).index) :
    ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH)).index := by
  have hdvd := Subgroup.index_map_dvd ((T ⊓ K).subgroupOf K) (s9gStar_surjective M H K hKH)
  have hB : ((T ⊓ K).subgroupOf K).index = T.relIndex K := by
    rw [Subgroup.inf_subgroupOf_right]
    rfl
  have h3 : ((T ⊓ K).subgroupOf K).index ∣ (T.subgroupOf H).index := by
    rw [hB, s9g3_relIndex_eq hKH hTH hHKT hKn]
    exact dvd_refl _
  intro h
  exact hodd (h.trans (hdvd.trans h3))

theorem s9g3_outer_translate {G : Type} [Group G] {M H K T : Subgroup G} (hKH : K ≤ H)
    (hTH : T ≤ H) {t : G} (ht : t ∈ T)
    (hnot : ¬ s9gInner (E2.star M H K) (s9gPi M H ⟨t, hTH ht⟩)) :
    ∀ k ∈ K, ∃ x ∈ K, t * x * t⁻¹ * (k * x * k⁻¹)⁻¹ ∉ K ⊓ kerIn M H := by
  intro k hk
  by_contra hcon
  push Not at hcon
  apply hnot
  refine ⟨s9gPi M H ⟨k, hKH hk⟩, ?_, ?_⟩
  · rw [s9g3_mem_star]
    exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  · intro y hy
    rw [s9g3_mem_star] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzK : (z : G) ∈ K := Subgroup.mem_subgroupOf.mp hz
    have hwker : t * (z : G) * t⁻¹ * (k * (z : G) * k⁻¹)⁻¹ ∈ K ⊓ kerIn M H := hcon _ hzK
    have hw1 : s9gPi M H (⟨t, hTH ht⟩ * z * (⟨t, hTH ht⟩ : H)⁻¹ *
        (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹)⁻¹) = 1 := by
      have hmem : (⟨t, hTH ht⟩ * z * (⟨t, hTH ht⟩ : H)⁻¹ *
          (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹)⁻¹ : H) ∈ (kerIn M H).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp hwker).2
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have key : (⟨t, hTH ht⟩ : H) * z * (⟨t, hTH ht⟩ : H)⁻¹ =
        ((⟨t, hTH ht⟩ : H) * z * (⟨t, hTH ht⟩ : H)⁻¹ *
          (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹)⁻¹) * (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹) := by
      group
    calc s9gPi M H ⟨t, hTH ht⟩ * s9gPi M H z * (s9gPi M H ⟨t, hTH ht⟩)⁻¹
        = s9gPi M H ((⟨t, hTH ht⟩ : H) * z * (⟨t, hTH ht⟩ : H)⁻¹) := by
          simp only [map_mul, map_inv]
      _ = s9gPi M H (((⟨t, hTH ht⟩ : H) * z * (⟨t, hTH ht⟩ : H)⁻¹ *
          (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹)⁻¹) * (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹)) := by
          rw [← key]
      _ = s9gPi M H (⟨k, hKH hk⟩ * z * (⟨k, hKH hk⟩ : H)⁻¹) := by
          rw [map_mul, hw1, one_mul]
      _ = s9gPi M H ⟨k, hKH hk⟩ * s9gPi M H z * (s9gPi M H ⟨k, hKH hk⟩)⁻¹ := by
          simp only [map_mul, map_inv]

end CFSG.Quasithin.H13.L829N
