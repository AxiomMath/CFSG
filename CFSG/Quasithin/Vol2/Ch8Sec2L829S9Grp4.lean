module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Grp2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Grp3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat

public section

namespace CFSG.Quasithin.H13.L829N

theorem s9g4_unique {Y : Type} [Group Y] {Ks : Subgroup Y}
    (hZ : ∀ u : ↥Ks, (∀ y : ↥Ks, u * y = y * u) → u = 1) {x z z' : Y} (hz : z ∈ Ks)
    (hz' : z' ∈ Ks) (h : ∀ y ∈ Ks, x * y * x⁻¹ = z * y * z⁻¹)
    (h' : ∀ y ∈ Ks, x * y * x⁻¹ = z' * y * z'⁻¹) : z = z' := by
  have hu : z⁻¹ * z' ∈ Ks := Ks.mul_mem (Ks.inv_mem hz) hz'
  have hc : ∀ y ∈ Ks, (z⁻¹ * z') * y = y * (z⁻¹ * z') := by
    intro y hy
    have e : z * y * z⁻¹ = z' * y * z'⁻¹ := (h y hy).symm.trans (h' y hy)
    have h3 : (z⁻¹ * z') * y * (z⁻¹ * z')⁻¹ = y := by
      calc (z⁻¹ * z') * y * (z⁻¹ * z')⁻¹ = z⁻¹ * (z' * y * z'⁻¹) * z := by group
        _ = z⁻¹ * (z * y * z⁻¹) * z := by rw [e]
        _ = y := by group
    calc (z⁻¹ * z') * y = (z⁻¹ * z') * y * (z⁻¹ * z')⁻¹ * (z⁻¹ * z') := by group
      _ = y * (z⁻¹ * z') := by rw [h3]
  have hu1 : z⁻¹ * z' = 1 := by
    have := hZ ⟨z⁻¹ * z', hu⟩ (fun y => Subtype.ext (hc y.1 y.2))
    exact congrArg Subtype.val this
  exact inv_mul_eq_one.mp hu1

theorem s9g4_c2 {G : Type} [Group G] [Finite G] {M H K T : Subgroup G}
    (hKH : K ≤ H) (hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T H)
    (hPSL : IsPSL 3 2 1 ↥(E2.star M H K))
    (hauto : 8 < E2.autCard (E2.star M H T) (E2.star M H K)) :
    ∃ x ∈ E2.star M H T, ¬ s9gInner (E2.star M H K) x := by
  by_contra hall
  push Not at hall
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    hTsyl.2.1.comap_of_injective H.subtype Subtype.val_injective
  have hTs2 : IsPGroup 2 ↥(E2.star M H T) := hT2.map (s9gPi M H)
  have hX2 : IsPGroup 2
      ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) :=
    hTs2.to_le inf_le_left
  obtain ⟨ψ⟩ := s9g2_iso_sl32 hPSL
  have hKsCard : Nat.card ↥(E2.star M H K) = 168 := by
    rw [Nat.card_congr ψ.toEquiv, s9g2_card_sl32]
  have hZ : ∀ u : ↥(E2.star M H K), (∀ y : ↥(E2.star M H K), u * y = y * u) → u = 1 := by
    intro u hu
    apply ψ.injective
    rw [map_one]
    apply s9g2_center_sl32
    intro h
    obtain ⟨y, rfl⟩ := ψ.surjective h
    rw [← map_mul, ← map_mul, hu y]
  have hex : ∀ x : ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)),
      ∃ z : E2.StarQuot M H, z ∈ E2.star M H K ∧
        ∀ y ∈ E2.star M H K, (x : E2.StarQuot M H) * y * (x : E2.StarQuot M H)⁻¹ = z * y * z⁻¹ :=
    fun x => hall _ (Subgroup.mem_inf.mp x.2).1
  choose zf hzf using hex
  let φf : ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) →
      ↥(E2.star M H K) := fun x => ⟨zf x, (hzf x).1⟩
  have hmul : ∀ x x' : ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)),
      φf (x * x') = φf x * φf x' := by
    intro x x'
    apply Subtype.ext
    show zf (x * x') = zf x * zf x'
    refine s9g4_unique hZ (hzf (x * x')).1 ((E2.star M H K).mul_mem (hzf x).1 (hzf x').1)
      (hzf (x * x')).2 ?_
    intro y hy
    have hy' : zf x' * y * (zf x')⁻¹ ∈ E2.star M H K :=
      (E2.star M H K).mul_mem ((E2.star M H K).mul_mem (hzf x').1 hy)
        ((E2.star M H K).inv_mem (hzf x').1)
    have h1 := (hzf x).2 _ hy'
    have h2 := (hzf x').2 y hy
    rw [Subgroup.coe_mul]
    calc (x : E2.StarQuot M H) * (x' : E2.StarQuot M H) * y *
          ((x : E2.StarQuot M H) * (x' : E2.StarQuot M H))⁻¹
        = (x : E2.StarQuot M H) * ((x' : E2.StarQuot M H) * y * (x' : E2.StarQuot M H)⁻¹) *
            (x : E2.StarQuot M H)⁻¹ := by group
      _ = (x : E2.StarQuot M H) * (zf x' * y * (zf x')⁻¹) * (x : E2.StarQuot M H)⁻¹ := by rw [h2]
      _ = zf x * (zf x' * y * (zf x')⁻¹) * (zf x)⁻¹ := h1
      _ = (zf x * zf x') * y * (zf x * zf x')⁻¹ := by group
  let φ : ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) →*
      ↥(E2.star M H K) := MonoidHom.mk' φf hmul
  have hker : ∀ x : ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)),
      φ x = 1 ↔ (x : E2.StarQuot M H) ∈
        Subgroup.centralizer ((E2.star M H K : Subgroup _) : Set (E2.StarQuot M H)) := by
    intro x
    constructor
    · intro h1
      have h1' : zf x = 1 := congrArg Subtype.val h1
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hx := (hzf x).2 h hh
      rw [h1', one_mul, inv_one, mul_one] at hx
      have e1 : (x : E2.StarQuot M H) * h = h * (x : E2.StarQuot M H) := by
        calc (x : E2.StarQuot M H) * h = ((x : E2.StarQuot M H) * h * (x : E2.StarQuot M H)⁻¹) *
              (x : E2.StarQuot M H) := by group
          _ = h * (x : E2.StarQuot M H) := by rw [hx]
      exact e1.symm
    · intro hc
      rw [Subgroup.mem_centralizer_iff] at hc
      have hz1 : zf x = 1 := by
        refine s9g4_unique hZ (hzf x).1 (E2.star M H K).one_mem (hzf x).2 ?_
        intro y hy
        have hc' := hc y hy
        show (x : E2.StarQuot M H) * y * (x : E2.StarQuot M H)⁻¹ = 1 * y * 1⁻¹
        rw [inv_one, mul_one, one_mul]
        calc (x : E2.StarQuot M H) * y * (x : E2.StarQuot M H)⁻¹
            = y * (x : E2.StarQuot M H) * (x : E2.StarQuot M H)⁻¹ := by rw [hc']
          _ = y := by group
      apply Subtype.ext
      exact hz1
  have hker_eq : φ.ker =
      ((E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) ⊓
        Subgroup.centralizer ((E2.star M H K : Subgroup _) : Set (E2.StarQuot M H))).subgroupOf
        (E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) := by
    ext x
    rw [MonoidHom.mem_ker, hker x, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hauto2 : 8 < φ.ker.index := by
    rw [hker_eq]
    exact hauto
  have hdvdX : φ.ker.index ∣ Nat.card
      ↥(E2.star M H T ⊓ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _)) :=
    Dvd.intro_left _ (Subgroup.card_mul_index φ.ker)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hX2
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hm ▸ hdvdX)
  have hdvdKs : φ.ker.index ∣ 168 := by
    rw [Subgroup.index_ker, ← hKsCard]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hn] at hauto2 hdvdKs
  have hn4 : 4 ≤ n := by
    by_contra hc
    have h8 : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8
    omega
  have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hn4
  have h168 := h16.trans hdvdKs
  norm_num at h168

theorem s9g4_conj_inf {G : Type} [Group G] {T K : Subgroup G} {t : G} (ht : t ∈ T)
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (a : G) :
    a ∈ T ⊓ K ↔ t * a * t⁻¹ ∈ T ⊓ K := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨haT, haK⟩
    exact ⟨T.mul_mem (T.mul_mem ht haT) (T.inv_mem ht), (Subgroup.mem_normalizer_iff.mp htK a).mp haK⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htK a).mpr h2⟩
    have e : a = t⁻¹ * (t * a * t⁻¹) * t := by group
    rw [e]
    exact T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht

theorem s9g4_c1 {G : Type} [Group G] [Finite G] {M H K T : Subgroup G}
    (hKH : K ≤ H) (hTH : T ≤ H) (hHKT : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T H)
    (hPSL : IsPSL 3 2 1 ↥(E2.star M H K))
    (hDN : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K))) :
    ∃ x ∈ E2.star M H T, ¬ s9gInner (E2.star M H K) x := by
  have hHn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHKT]
    exact sup_le Subgroup.le_normalizer hTK
  have hKn : (K.subgroupOf H).Normal := s9g3_subgroupOf_normal hHn
  have hTKs_le : E2.star M H (T ⊓ K) ≤ E2.star M H K := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := s9g3_mem_star.mp hy
    exact s9g3_mem_star.mpr ⟨z, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2, rfl⟩
  have hB2 : IsPGroup 2 ↥((T ⊓ K).subgroupOf K) := by
    have h1 : IsPGroup 2 ↥(T ⊓ K) := hTsyl.2.1.to_le inf_le_left
    exact h1.comap_of_injective K.subtype Subtype.val_injective
  have hSK2 : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH)) := hB2.map _
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH)) ⊤ := by
    refine ⟨le_top, hSK2, ?_⟩
    change ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact s9g3_index_odd hKH hTH hHKT hKn hTsyl.2.2
  obtain ⟨ψ⟩ := s9g2_iso_sl32 hPSL
  obtain ⟨P₀, hmax₀, hnorm₀⟩ := s9_exists_parabolic _ (s9g2_isSylow_map ψ hSyl)
  have hmaxR := s9g2_maxParabolic_map ψ.symm hmax₀
  have hmaxP := s9g2_maxParabolic_subgroup hmaxR
  set P := (P₀.map ψ.symm.toMonoidHom).map (E2.star M H K).subtype with hPdef
  have hPKs : P ≤ E2.star M H K := Subgroup.map_subtype_le _
  have hNP : E2.star M H K ⊓ Subgroup.normalizer ((E2.star M H (T ⊓ K) : Subgroup _) : Set _) ≤
      P := by
    intro k hk
    obtain ⟨hkKs, hkN⟩ := Subgroup.mem_inf.mp hk
    have hk'N : (⟨k, hkKs⟩ : ↥(E2.star M H K)) ∈
        Subgroup.normalizer ((((T ⊓ K).subgroupOf K).map (s9gStar M H K hKH) :
          Subgroup ↥(E2.star M H K)) : Set ↥(E2.star M H K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      rw [s9g3_map_starHom hKH, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have h1 := Subgroup.mem_normalizer_iff.mp hkN (a : E2.StarQuot M H)
      simpa using h1
    have hψk := s9g2_normalizer_map ψ hk'N
    have hψP : ψ ⟨k, hkKs⟩ ∈ P₀ := hnorm₀ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, hψk⟩)
    have hk'R : (⟨k, hkKs⟩ : ↥(E2.star M H K)) ∈ P₀.map ψ.symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨ψ ⟨k, hkKs⟩, hψP, by simp⟩
    exact (s9g2_mem_map_subtype (⟨k, hkKs⟩ : ↥(E2.star M H K))).mpr hk'R
  obtain ⟨x, hxTs, hxP⟩ : ∃ x ∈ E2.star M H T, x ∉ Subgroup.normalizer (P : Set _) := by
    by_contra hc
    push Not at hc
    refine hDN P hmaxP hNP ?_
    intro x hx
    exact hc x hx
  refine ⟨x, hxTs, ?_⟩
  rintro ⟨z, hz, hxz⟩
  apply hxP
  obtain ⟨t, ht, rfl⟩ := s9g3_mem_star.mp hxTs
  have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have htK : (t : G) ∈ Subgroup.normalizer (K : Set G) := hTK htT
  have hxNKs : s9gPi M H t ∈ Subgroup.normalizer ((E2.star M H K : Subgroup _) : Set _) :=
    s9g3_star_normalizes t.2 (Subgroup.mem_normalizer_iff.mp htK)
  have hxNTKs : s9gPi M H t ∈ Subgroup.normalizer ((E2.star M H (T ⊓ K) : Subgroup _) : Set _) :=
    s9g3_star_normalizes t.2 (fun a => s9g4_conj_inf htT htK a)
  have hxKs : ∀ h : E2.StarQuot M H, h ∈ E2.star M H K ↔
      s9gPi M H t * h * (s9gPi M H t)⁻¹ ∈ E2.star M H K :=
    fun h => Subgroup.mem_normalizer_iff.mp hxNKs h
  have hxTKs : ∀ h : E2.StarQuot M H, h ∈ E2.star M H (T ⊓ K) ↔
      s9gPi M H t * h * (s9gPi M H t)⁻¹ ∈ E2.star M H (T ⊓ K) :=
    fun h => Subgroup.mem_normalizer_iff.mp hxNTKs h
  have hzTKs : z ∈ Subgroup.normalizer ((E2.star M H (T ⊓ K) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhKs : h ∈ E2.star M H K := hTKs_le hh
      rw [← hxz h hhKs]
      exact (hxTKs h).mp hh
    · intro hzh
      have hzhKs : z * h * z⁻¹ ∈ E2.star M H K := hTKs_le hzh
      have hhKs : h ∈ E2.star M H K := by
        have := (E2.star M H K).mul_mem ((E2.star M H K).mul_mem ((E2.star M H K).inv_mem hz)
          hzhKs) hz
        simpa [mul_assoc] using this
      have e := hxz h hhKs
      exact (hxTKs h).mpr (by rw [e]; exact hzh)
  have hzP : z ∈ P := hNP (Subgroup.mem_inf.mpr ⟨hz, hzTKs⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hhP
    have hhKs : h ∈ E2.star M H K := hPKs hhP
    rw [hxz h hhKs]
    exact P.mul_mem (P.mul_mem hzP hhP) (P.inv_mem hzP)
  · intro hxhP
    have hhKs : h ∈ E2.star M H K := (hxKs h).mpr (hPKs hxhP)
    have e := hxz h hhKs
    have hzhP : z * h * z⁻¹ ∈ P := by
      rw [← e]
      exact hxhP
    have e2 : h = z⁻¹ * (z * h * z⁻¹) * z := by group
    rw [e2]
    exact P.mul_mem (P.mul_mem (P.inv_mem hzP) hzhP) hzP

end CFSG.Quasithin.H13.L829N
