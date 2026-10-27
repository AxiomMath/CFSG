module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section CS5Star

variable {G : Type} [Group G]

theorem star_sup_cs5 {M H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    E2.star M H (A ⊔ B) = E2.star M H A ⊔ E2.star M H B := by
  unfold E2.star
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem mem_star_cs5 {M H A : Subgroup G} {y : E2.StarQuot M H} :
    y ∈ E2.star M H A ↔ ∃ a : ↥H, (a : G) ∈ A ∧ (QuotientGroup.mk a : E2.StarQuot M H) = y := by
  unfold E2.star
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem star_conjSub_cs5 {M H A : Subgroup G} {h : G} (hh : h ∈ H) (hA : A ≤ H) :
    B6.conjSub h A ≤ H ∧ E2.star M H (B6.conjSub h A) =
      B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot M H) (E2.star M H A) := by
  have hsub : B6.conjSub h A ≤ H := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    have h1 := H.mul_mem (H.mul_mem hh (hA hx)) (H.inv_mem hh)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at h1
  refine ⟨hsub, ?_⟩
  ext y
  simp only [mem_star_cs5, B6.mem_conjSub]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(⟨h, hh⟩ : ↥H)⁻¹ * a * (⟨h, hh⟩ : ↥H), ha, ?_⟩
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · rintro ⟨a', ha', hy⟩
    refine ⟨(⟨h, hh⟩ : ↥H) * a' * (⟨h, hh⟩ : ↥H)⁻¹, ?_, ?_⟩
    · have e : h⁻¹ * (h * (a' : G) * h⁻¹) * h = (a' : G) := by group
      show h⁻¹ * (h * (a' : G) * h⁻¹) * h ∈ A
      rw [e]
      exact ha'
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hy]
      group

private theorem le_normalizer_map_normal_cs5 {H : Subgroup G} {D : Subgroup ↥H} (hD : D.Normal) :
    H ≤ Subgroup.normalizer ((D.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g : ↥H, ∀ x ∈ D.map H.subtype,
      (g : G) * x * (g : G)⁻¹ ∈ D.map H.subtype := by
    rintro g x ⟨d, hd, rfl⟩
    exact ⟨g * d * g⁻¹, hD.conj_mem d hd g, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key ⟨h, hh⟩ x hx
  · intro hx
    have h2 := key ⟨h⁻¹, H.inv_mem hh⟩ _ hx
    have h3 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ D.map H.subtype := h2
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h3

private theorem le_kerIn_subgroupOf_of_normal_cs5 {H M : Subgroup G} {D : Subgroup ↥H}
    (hD : D.Normal) (hDL : D ≤ (H ⊓ M).subgroupOf H) :
    D ≤ (kerIn (H ⊓ M) H).subgroupOf H := by
  intro d hd
  have hA : D.map H.subtype ≤ H ⊓ M := by
    rintro _ ⟨d', hd', rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hDL hd')
  have hdG : (d : G) ∈ D.map H.subtype := ⟨d, hd, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr
    (le_kerIn_of_le_normalizer hA (le_normalizer_map_normal_cs5 hD) hdG)

theorem normal_twoGroup_starQuot_eq_bot_cs5 [Finite G] {H T M : Subgroup G}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (N : Subgroup (E2.StarQuot (H ⊓ M) H)) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H) :
      ↥H →* E2.StarQuot (H ⊓ M) H) := QuotientGroup.mk'_surjective _
  have hT' : IsPGroup 2 (T.subgroupOf H) := hT.2.1.comap_subtype
  let P : Sylow 2 ↥H := hT'.toSylow hT.2.2
  have hNP : N ≤ (P.mapSurjective hπ : Subgroup (E2.StarQuot (H ⊓ M) H)) :=
    IsPGroup.le_sylow_of_normal hN _
  have hDnormal : (N.comap (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H))).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hDL : N.comap (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) ≤
      (H ⊓ M).subgroupOf H := by
    intro d hd
    have hd' : (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) d ∈ N := hd
    have hmem : (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) d ∈
        (T.subgroupOf H).map (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) :=
      hNP hd'
    obtain ⟨t, ht, htd⟩ := Subgroup.mem_map.mp hmem
    have hk : t⁻¹ * d ∈ (kerIn (H ⊓ M) H).subgroupOf H := by
      rw [← QuotientGroup.ker_mk' ((kerIn (H ⊓ M) H).subgroupOf H), MonoidHom.mem_ker, map_mul,
        map_inv, htd, inv_mul_cancel]
    have htL : t ∈ (H ⊓ M).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr ⟨t.2, hTM (Subgroup.mem_subgroupOf.mp ht)⟩
    have hkL : t⁻¹ * d ∈ (H ⊓ M).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (kerIn_le (Subgroup.mem_subgroupOf.mp hk))
    have h2 := ((H ⊓ M).subgroupOf H).mul_mem htL hkL
    rwa [mul_inv_cancel_left] at h2
  have hDN0 := le_kerIn_subgroupOf_of_normal_cs5 hDnormal hDL
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (H ⊓ M) H).subgroupOf H) n
  have hd : d ∈ N.comap (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) := hn
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff d).mpr (hDN0 hd)

theorem star_normal_cs5 {H T K M : Subgroup G} (hH : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : (E2.star (H ⊓ M) H K).Normal := by
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer hTK
  have hKnorm : (K.subgroupOf H).Normal := by
    constructor
    intro n hn g
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) _).mp hn
  exact Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)

theorem isPGroup_starQuot_quotient_cs5 {H T K M : Subgroup G}
    [(E2.star (H ⊓ M) H K).Normal] (hT : IsPGroup 2 T) (hH : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) := by
  have hTH : T ≤ H := hH ▸ le_sup_right
  have hKH : K ≤ H := hH ▸ le_sup_left
  have hKT : ∀ h ∈ H, ∃ k ∈ K, ∃ t ∈ T, h = k * t := by
    intro h hh
    let S : Subgroup G :=
      { carrier := {x | ∃ k ∈ K, ∃ t ∈ T, x = k * t}
        mul_mem' := by
          rintro _ _ ⟨k1, hk1, t1, ht1, rfl⟩ ⟨k2, hk2, t2, ht2, rfl⟩
          refine ⟨k1 * (t1 * k2 * t1⁻¹), K.mul_mem hk1 ?_, t1 * t2, T.mul_mem ht1 ht2, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp (hTK ht1) k2).mp hk2
          · group
        one_mem' := ⟨1, K.one_mem, 1, T.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨k, hk, t, ht, rfl⟩
          refine ⟨t⁻¹ * k⁻¹ * t, ?_, t⁻¹, T.inv_mem ht, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k⁻¹).mp (K.inv_mem hk)
          rw [inv_inv] at this
          exact this }
    have hS : K ⊔ T ≤ S := sup_le (fun k hk => ⟨k, hk, 1, T.one_mem, by group⟩)
      (fun t ht => ⟨1, K.one_mem, t, ht, by group⟩)
    have hh' : h ∈ K ⊔ T := hH ▸ hh
    obtain ⟨k, hk, t, ht, e⟩ := hS hh'
    exact ⟨k, hk, t, ht, e⟩
  let φ : ↥T →* (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
    (QuotientGroup.mk' (E2.star (H ⊓ M) H K)).comp
      ((QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)).comp (Subgroup.inclusion hTH))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (E2.star (H ⊓ M) H K) y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (H ⊓ M) H).subgroupOf H) z
    obtain ⟨k, hk, t, ht, e⟩ := hKT (h : G) h.2
    have hkH : k ∈ H := hKH hk
    have hk' : (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H) ⟨k, hkH⟩ :
        E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H K :=
      ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hh_eq : h = (⟨k, hkH⟩ : ↥H) * ⟨t, hTH ht⟩ := Subtype.ext (by simp [e])
    refine ⟨⟨t, ht⟩, ?_⟩
    have hk1 : (QuotientGroup.mk' (E2.star (H ⊓ M) H K))
        (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H) ⟨k, hkH⟩) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hk'
    show (QuotientGroup.mk' (E2.star (H ⊓ M) H K))
        ((QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) (Subgroup.inclusion hTH ⟨t, ht⟩)) = _
    rw [hh_eq, map_mul, map_mul, hk1, one_mul]
    rfl
  exact IsPGroup.of_surjective hT φ hφ

theorem isElemAbelian_star_cs5 {M H V : Subgroup G} (_hVH : V ≤ H) (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 (E2.star M H V) := by
  refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_star_cs5.mp hy
    apply Subtype.ext
    have hab : (a : G) * (b : G) = (b : G) * (a : G) := by
      have := congrArg Subtype.val (isMulCommutative_iff.mp hV.1 ⟨(a : G), ha⟩ ⟨(b : G), hb⟩)
      exact this
    show (QuotientGroup.mk a : E2.StarQuot M H) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (fun z : ↥H => (QuotientGroup.mk z : E2.StarQuot M H)) (Subtype.ext hab)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hx
    have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa using hV.2 (a : G) ha)
    rw [← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]

theorem star_le_normalizer_star_cs5 {M H A V : Subgroup G} (_hA : A ≤ H) (_hVH : V ≤ H)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    E2.star M H A ≤ Subgroup.normalizer
      ((E2.star M H V : Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H)) := by
  have key : ∀ x ∈ E2.star M H A, ∀ y ∈ E2.star M H V, x * y * x⁻¹ ∈ E2.star M H V := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_star_cs5.mp hy
    refine mem_star_cs5.mpr ⟨a * v * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAV ha) (v : G)).mp hv
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key x hx y hy
  · intro hy
    have h2 := key x⁻¹ ((E2.star M H A).inv_mem hx) _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [e] at h2

theorem isPGroup_star_cs5 {M H A : Subgroup G} (hA : IsPGroup 2 A) :
    IsPGroup 2 (E2.star M H A) := by
  have hA' : IsPGroup 2 (A.subgroupOf H) := hA.comap_subtype
  exact hA'.map (QuotientGroup.mk' ((kerIn M H).subgroupOf H))

end CS5Star

end CFSG.Quasithin.H13
