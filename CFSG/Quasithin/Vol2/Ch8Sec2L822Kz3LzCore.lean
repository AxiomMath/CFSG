module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Quot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem map_comap_subtype_eq_kz3 {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L) :
    (K.comap L.subtype).map L.subtype = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKL hx⟩, hx, rfl⟩

theorem perfect_comap_subtype_kz3 {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L)
    (hK : ⁅K, K⁆ = K) : ⁅K.comap L.subtype, K.comap L.subtype⁆ = K.comap L.subtype := by
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [Subgroup.map_commutator, map_comap_subtype_eq_kz3 hKL, hK]

theorem quasithinIsCComponent_kz3 {G : Type} [Group G] [Finite G] {Lz T : Subgroup G}
    (hperf : ⁅Lz, Lz⁆ = Lz) (hne : Lz ≠ ⊥) (hTN : T ≤ Subgroup.normalizer (Lz : Set G))
    (hqs : CFSG.IsQuasisimple (↥Lz ⧸ CFSG.pCore 2 ↥Lz)) :
    quasithinIsCComponent Lz (Lz ⊔ T) := by
  refine ⟨hne, hperf, ?_, ?_⟩
  · have hnorm : (Lz.subgroupOf (Lz ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTN)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  · intro K hKlt hKne hKperf hKsub
    have hKL : CFSG.Open.IsSubnormal K Lz :=
      CFSG.Quasithin.A3.subnormal_of_le_of_le hKsub hKlt.le le_sup_left
    have hKc : CFSG.Open.IsSubnormal (K.comap Lz.subtype) (Lz.comap Lz.subtype) :=
      CFSG.Quasithin.A3.subnormal_comap Lz.subtype hKL
    have htop : Lz.comap Lz.subtype = ⊤ := by
      ext x
      simp
    rw [htop] at hKc
    have hK'perf : ⁅K.comap Lz.subtype, K.comap Lz.subtype⁆ = K.comap Lz.subtype :=
      perfect_comap_subtype_kz3 hKlt.le hKperf
    have hS : CFSG.Open.IsSubnormal ((K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)))
        (⊤ : Subgroup (↥Lz ⧸ CFSG.pCore 2 ↥Lz)) := by
      have h := CFSG.Quasithin.A3.subnormal_map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) hKc
      rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    have hSperf : ⁅(K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)),
        (K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz))⁆ =
        (K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) := by
      rw [← Subgroup.map_commutator, hK'perf]
    rcases eq_bot_or_top_of_perfect_subnormal_kz3 hqs hS hSperf with hSb | hSt
    ·
      have hle : K.comap Lz.subtype ≤ CFSG.pCore 2 ↥Lz := by
        intro y hy
        have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) y ∈
            (K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) :=
          Subgroup.mem_map_of_mem _ hy
        rw [hSb, Subgroup.mem_bot] at h1
        exact (QuotientGroup.eq_one_iff y).mp h1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2grp : IsPGroup 2 ↥(K.comap Lz.subtype) :=
        IsPGroup.to_le (CFSG.pCore_isPGroup (p := 2) (G := ↥Lz)) hle
      have hbot : K.comap Lz.subtype = ⊥ :=
        perfect_pgroup_eq_bot_kz3 h2grp hK'perf
      apply hKne
      rw [← map_comap_subtype_eq_kz3 hKlt.le, hbot, Subgroup.map_bot]
    ·
      have hcov : K.comap Lz.subtype ⊔ CFSG.pCore 2 ↥Lz = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) x ∈
            (K.comap Lz.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lz)) := by
          rw [hSt]
          exact Subgroup.mem_top _
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
        have hx' : x = y * (y⁻¹ * x) := by group
        rw [hx']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hyx)
      have hperfL : Group.IsPerfect ↥Lz := Subgroup.isPerfect_iff.mpr hperf
      have htopK : K.comap Lz.subtype = ⊤ :=
        subnormal_top_of_sup_pCore_kz3 hperfL hKc hcov
      have hLzK : Lz ≤ K := by
        intro x hx
        have hxt : (⟨x, hx⟩ : ↥Lz) ∈ K.comap Lz.subtype := by
          rw [htopK]
          exact Subgroup.mem_top _
        exact hxt
      exact hKlt.2 hLzK

theorem lz_construct_kz3 {G : Type} [Group G] [Finite G] (L T : Subgroup G) (z : G)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (Pq : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hPC : Pq = (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    (hM0 : CFSG.pCore 2 ↥L ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)))
    (hperf : ⁅Pq, Pq⁆ = Pq) (hne : Pq ≠ ⊥) :
    ∃ Lz : Subgroup G, Lz ≤ Subgroup.centralizer ({z} : Set G) ∧ ⁅Lz, Lz⁆ = Lz ∧ Lz ≠ ⊥ ∧
      T ≤ Subgroup.normalizer (Lz : Set G) ∧
      Nonempty (↥Lz ⧸ CFSG.pCore 2 ↥Lz ≃* ↥Pq ⧸ CFSG.pCore 2 ↥Pq) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf' : ⁅(Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
      (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))⁆ =
      (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [← hPC]
    exact hperf
  have hsup := sup_perfectCore_eq_kz3 hM0 hperf'
  have hM0f : (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff h).mpr hh
  set Λ := CFSG.Quasithin.perfectCore (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))) with hΛ
  have hΛC : Λ ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) :=
    CFSG.Quasithin.perfectCore_le _
  have hPΛ : Pq = Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [hPC]
    conv_lhs => rw [← hsup]
    rw [Subgroup.map_sup, hM0f, sup_bot_eq]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := CFSG.Quasithin.perfectCore_perfect _
  refine ⟨Λ.map L.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    exact hΛC hc
  · rw [← Subgroup.map_commutator, hΛperf]
  · intro hL
    apply hne
    have hΛbot : Λ = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      have h1 : L.subtype c ∈ Λ.map L.subtype := Subgroup.mem_map_of_mem _ hc
      rw [hL, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Subtype.ext h1
    rw [hPΛ, hΛbot, Subgroup.map_bot]
  · have hmax : ∀ K : Subgroup G, ⁅K, K⁆ = K → K ≤ L → K ≤ Subgroup.centralizer ({z} : Set G) →
        K ≤ Λ.map L.subtype := by
      intro K hKperf hKL hKC
      have hK'C : K.comap L.subtype ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) :=
        fun y hy => hKC hy
      have hK'Λ : K.comap L.subtype ≤ Λ :=
        CFSG.Quasithin.le_perfectCore_of_perfect hK'C (perfect_comap_subtype_kz3 hKL hKperf)
      rw [← map_comap_subtype_eq_kz3 hKL]
      exact Subgroup.map_mono hK'Λ
    have hconj : ∀ t ∈ T, ∀ x ∈ Λ.map L.subtype, t * x * t⁻¹ ∈ Λ.map L.subtype := by
      intro t ht x hx
      have hLzperf : ⁅Λ.map L.subtype, Λ.map L.subtype⁆ = Λ.map L.subtype := by
        rw [← Subgroup.map_commutator, hΛperf]
      have hKperf : ⁅(Λ.map L.subtype).map (MulAut.conj t).toMonoidHom,
          (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom⁆ =
          (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom := by
        rw [← Subgroup.map_commutator, hLzperf]
      have hKL : (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom ≤ L := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.mp hy
        have hyL : (c : G) ∈ L := c.2
        exact (Subgroup.mem_normalizer_iff.mp (hTL ht) (c : G)).mp hyL
      have hKC : (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom ≤
          Subgroup.centralizer ({z} : Set G) := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
        have hcz : (c : G) * z = z * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp (hΛC hc)
        have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
        have htz' : t⁻¹ * z = z * t⁻¹ := by
          calc t⁻¹ * z = t⁻¹ * (z * t) * t⁻¹ := by group
            _ = t⁻¹ * (t * z) * t⁻¹ := by rw [htz]
            _ = z * t⁻¹ := by group
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        show t * (c : G) * t⁻¹ * z = z * (t * (c : G) * t⁻¹)
        calc t * (c : G) * t⁻¹ * z = t * (c : G) * (t⁻¹ * z) := by group
          _ = t * (c : G) * (z * t⁻¹) := by rw [htz']
          _ = t * ((c : G) * z) * t⁻¹ := by group
          _ = t * (z * (c : G)) * t⁻¹ := by rw [hcz]
          _ = (t * z) * (c : G) * t⁻¹ := by group
          _ = (z * t) * (c : G) * t⁻¹ := by rw [htz]
          _ = z * (t * (c : G) * t⁻¹) := by group
      have hmem := hmax _ hKperf hKL hKC
      have hx' : (MulAut.conj t).toMonoidHom x ∈ (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      exact hmem hx'
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj t ht x hx
    · intro hx
      have h1 := hconj t⁻¹ (T.inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at h1
  · have hM0mem : ∀ y : ↥L, (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) y = 1 →
        ∃ n : ℕ, y ^ 2 ^ n = 1 := by
      intro y hy
      have hy' : y ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff y).mp hy
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y, hy'⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    let e0 : ↥Λ ≃* ↥(Λ.map L.subtype) := Subgroup.equivMapOfInjective Λ L.subtype L.subtype_injective
    let φ1 : ↥Λ →* ↥Pq := ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp Λ.subtype).codRestrict Pq
      (fun x => by rw [hPΛ]; exact Subgroup.mem_map_of_mem _ x.2)
    have hφ1 : Function.Surjective φ1 := by
      intro q
      have hq : (q : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [← hPΛ]
        exact q.2
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
    let φ2 : ↥(Λ.map L.subtype) →* ↥Pq := φ1.comp e0.symm.toMonoidHom
    have hφ2 : Function.Surjective φ2 := hφ1.comp e0.symm.surjective
    have hK : ∀ x : ↥(Λ.map L.subtype), φ2 x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      intro x hx
      have h1 : φ1 (e0.symm x) = 1 := hx
      have hlam : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ((e0.symm x : ↥Λ) : ↥L) = 1 :=
        congrArg Subtype.val h1
      obtain ⟨n, hn⟩ := hM0mem _ hlam
      refine ⟨n, ?_⟩
      have h3 : (e0.symm x) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        simpa using hn
      have h4 := congrArg e0 h3
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h4
      exact h4
    exact pCore_quot_equiv_kz3 φ2 hφ2 hK

end CFSG.Quasithin.H13
