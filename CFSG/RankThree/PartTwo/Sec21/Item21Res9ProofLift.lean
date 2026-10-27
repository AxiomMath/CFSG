module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup

section PGroups

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {g : G} {k : ℕ} (hg : g ^ 3 ^ k = 1) :
    IsPGroup 3 (zpowers g) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem isPGroup_sup_zpowers {t u : G} {a b : ℕ} (ht : t ^ 3 ^ a = 1) (hu : u ^ 3 ^ b = 1)
    (htu : t * u = u * t) : IsPGroup 3 (zpowers t ⊔ zpowers u : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : zpowers t ≤ normalizer (zpowers u : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : t * u ^ k = u ^ k * t := (Commute.zpow_right htu k).eq
    rw [hc, mul_inv_cancel_right]
    exact zpow_mem_zpowers u k
  exact IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow ht)
    (isPGroup_zpowers_of_pow hu) hle

theorem isPGroup_closure_pair {x t : G} {N : Subgroup G} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hN : IsPGroup 3 N) (htN : t ∈ N) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    IsPGroup 3 (closure ({x, t} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (zpowers x) := isPGroup_zpowers_of_pow hx
  have hle : zpowers x ≤ normalizer (N : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_fintype hxN
  refine (IsPGroup.to_sup_of_normal_right' hxp hN hle).to_le ?_
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact mem_sup_left (mem_zpowers g)
  · exact mem_sup_right htN

theorem isPGroup_closure_heis {x t : G} {k : ℕ} (hx : x ^ 3 = 1) (ht : t ^ 3 ^ k = 1)
    (hc3 : (x * t * x⁻¹ * t⁻¹) ^ 3 = 1)
    (hct : x * t * x⁻¹ * t⁻¹ * t = t * (x * t * x⁻¹ * t⁻¹))
    (hcx : x * t * x⁻¹ * t⁻¹ * x = x * (x * t * x⁻¹ * t⁻¹)) :
    IsPGroup 3 (closure ({x, t} : Set G)) := by
  set c := x * t * x⁻¹ * t⁻¹ with hc
  refine isPGroup_closure_pair (k := 1) (by rw [pow_one]; exact hx)
    (isPGroup_sup_zpowers ht (b := 1) (by rw [pow_one]; exact hc3)
    hct.symm) (mem_sup_left (mem_zpowers t)) fun n hn => ?_
  have hle : zpowers t ⊔ zpowers c ≤ (zpowers t ⊔ zpowers c).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : x * t * x⁻¹ = c * t := by rw [hc]; group
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers c)) (mem_sup_left (mem_zpowers t))
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : x * c * x⁻¹ = c := by rw [mul_inv_eq_iff_eq_mul, hcx]
      rw [e]
      exact mem_sup_right (mem_zpowers c)
  have h := hle hn
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

end PGroups

section Centralizers

variable {G H : Type*} [Group G] [Group H]

theorem card_centralizer_conj (c a : G) :
    Nat.card (centralizer ({c * a * c⁻¹} : Set G)) = Nat.card (centralizer ({a} : Set G)) := by
  have h : centralizer ({c * a * c⁻¹} : Set G) =
      (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom := by
    ext g
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro hg
      calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * g) * c := by rw [hg]
        _ = a * (c⁻¹ * g * c) := by group
    · intro hg
      calc g * (c * a * c⁻¹) = c * (c⁻¹ * g * c * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * g * c)) * c⁻¹ := by rw [hg]
        _ = c * a * c⁻¹ * g := by group
  rw [h, card_map_of_injective (MulAut.conj c).injective]

theorem centralizer_inv_singleton (a : G) :
    centralizer ({a⁻¹} : Set G) = centralizer ({a} : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hg
    calc g * a = a * (a⁻¹ * g) * a := by group
      _ = a * (g * a⁻¹) * a := by rw [hg]
      _ = a * g := by group
  · intro hg
    calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
      _ = a⁻¹ * (g * a) * a⁻¹ := by rw [hg]
      _ = a⁻¹ * g := by group

end Centralizers

@[expose] def RealPair (H : Type*) [Group H] : Prop :=
  ∃ x t y : H, x ^ 3 = 1 ∧ y * x * y⁻¹ = x⁻¹ ∧ x * t ≠ t * x ∧
    IsPGroup 3 (closure ({x, t} : Set H))

theorem RealPair.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : RealPair H') : RealPair H := by
  obtain ⟨x, t, y, hx3, hy, hxt, hp⟩ := h
  refine ⟨e.symm x, e.symm t, e.symm y, by rw [← map_pow, hx3, map_one],
    by rw [← map_inv, ← map_mul, ← map_mul, hy, map_inv],
    fun h => hxt (e.symm.injective (by rw [map_mul, map_mul, h])), ?_⟩
  have := hp.map e.symm.toMonoidHom
  rwa [MonoidHom.map_closure, Set.image_pair] at this

section Sylow

variable {X : Type*} [Group X] [Finite X]

theorem exists_noncentral_of_sylow (S' S : Sylow 3 X)
    (h : ∃ s ∈ (S' : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S' : Subgroup X), s * t ≠ t * s) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S
  obtain ⟨s, hs, hs3, t, ht, hst⟩ := h
  have hmem : ∀ u ∈ (S' : Subgroup X), g * u * g⁻¹ ∈ (S : Subgroup X) := by
    intro u hu
    rw [← hg, Sylow.coe_subgroup_smul]
    have := smul_mem_pointwise_smul u (MulAut.conj g) (S' : Subgroup X) hu
    simpa [MulAut.smul_def] using this
  refine ⟨g * s * g⁻¹, hmem s hs, by rw [conj_pow, hs3, mul_one, mul_inv_cancel],
    g * t * g⁻¹, hmem t ht, fun h => hst ?_⟩
  calc s * t = g⁻¹ * (g * s * g⁻¹ * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * (g * s * g⁻¹)) * g := by rw [h]
    _ = t * s := by group

omit [Finite X] in
theorem mem_sylow_of_mem_center {v : X} (hv : v ∈ center X) {k : ℕ} (hk : v ^ 3 ^ k = 1)
    (S : Sylow 3 X) : v ∈ (S : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (zpowers v).Normal := normal_of_le_center (zpowers_le.mpr hv)
  exact IsPGroup.le_sylow_of_normal (isPGroup_zpowers_of_pow hk) S (mem_zpowers v)

omit [Finite X] in
theorem exists_lift_of_real (N : Subgroup X) [N.Normal] (hN : N ≤ center X) (S : Sylow 3 X)
    {x y : X ⧸ N} (hxS : x ∈ (S : Subgroup X).map (QuotientGroup.mk' N)) (hx3 : x ^ 3 = 1)
    (hy : y * x * y⁻¹ = x⁻¹) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ QuotientGroup.mk' N s = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haS, rfl⟩ := mem_map.mp hxS
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hζN : a ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hx3
  set z := a * (w * a * w⁻¹) with hz
  have hzN : z ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, hz, map_mul, map_mul, map_mul,
      map_inv, hy, mul_inv_cancel]
  have hzc : z ∈ center X := hN hzN
  have hζc : a ^ 3 ∈ center X := hN hζN
  have hwa : w * a * w⁻¹ = a⁻¹ * z := by rw [hz]; group
  have hζz : a ^ 3 * a ^ 3 = z ^ 3 := by
    have h1 : w * a ^ 3 * w⁻¹ = a ^ 3 := by
      rw [mem_center_iff.mp hζc w, mul_inv_cancel_right]
    have h2 : w * a ^ 3 * w⁻¹ = (a⁻¹ * z) ^ 3 := by rw [← conj_pow, hwa]
    have h3 : (a⁻¹ * z) ^ 3 = a⁻¹ ^ 3 * z ^ 3 :=
      (Commute.mul_pow (mem_center_iff.mp hzc a⁻¹) 3)
    rw [h1, h3, inv_pow] at h2
    calc a ^ 3 * a ^ 3 = a ^ 3 * ((a ^ 3)⁻¹ * z ^ 3) := by rw [← h2]
      _ = z ^ 3 := by group
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨a ^ 3, pow_mem haS 3⟩
  have hk' : (a ^ 3) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set m := (3 ^ k + 1) / 2 with hm
  have h2m : 2 * m = 3 ^ k + 1 := by
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨r, hr⟩ := hodd
    rw [hm, hr]
    omega
  have hζ : a ^ 3 = (z ^ m) ^ 3 := by
    calc a ^ 3 = (a ^ 3) ^ (3 ^ k + 1) := by rw [pow_succ (a ^ 3), hk', one_mul]
      _ = (a ^ 3 * a ^ 3) ^ m := by rw [← h2m, pow_mul, sq]
      _ = (z ^ m) ^ 3 := by rw [hζz, ← pow_mul, ← pow_mul, mul_comm]
  set v := z ^ m with hv
  have hvc : v ∈ center X := pow_mem hzc m
  have hvN : v ∈ N := pow_mem hzN m
  have hvS : v ∈ (S : Subgroup X) :=
    mem_sylow_of_mem_center hvc (k := k + 1) (by rw [pow_succ', pow_mul, ← hζ, hk']) S
  refine ⟨a * v⁻¹, mul_mem haS (inv_mem hvS), ?_, ?_⟩
  · rw [(Commute.mul_pow (mem_center_iff.mp (inv_mem hvc) a) 3), inv_pow, ← hζ,
      mul_inv_cancel]
  · have hv1 : QuotientGroup.mk' N v = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hvN
    rw [map_mul, map_inv, hv1, inv_one, mul_one]

theorem exists_noncentral_of_quotient (N : Subgroup X) [N.Normal] (hN : N ≤ center X)
    {x t y : X ⧸ N} (hx3 : x ^ 3 = 1) (hy : y * x * y⁻¹ = x⁻¹) (hxt : x * t ≠ t * x)
    (hp : IsPGroup 3 (closure ({x, t} : Set (X ⧸ N)))) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ u ∈ (S : Subgroup X), s * u ≠ u * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨S', rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) 3 Q
  apply exists_noncentral_of_sylow S'
  have hxS : x ∈ (S' : Subgroup X).map (QuotientGroup.mk' N) := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N)]
    exact hQ (subset_closure (Set.mem_insert _ _))
  have htS : t ∈ (S' : Subgroup X).map (QuotientGroup.mk' N) := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N)]
    exact hQ (subset_closure (Set.mem_insert_of_mem _ rfl))
  obtain ⟨s, hs, hs3, rfl⟩ := exists_lift_of_real N hN S' hxS hx3 hy
  obtain ⟨u, hu, rfl⟩ := mem_map.mp htS
  exact ⟨s, hs, hs3, u, hu, fun h => hxt (by rw [← map_mul, ← map_mul, h])⟩

theorem exists_noncentral_of_realPair (h : RealPair (X ⧸ center X)) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ u ∈ (S : Subgroup X), s * u ≠ u * s := by
  obtain ⟨x, t, y, hx3, hy, hxt, hp⟩ := h
  exact exists_noncentral_of_quotient (center X) le_rfl hx3 hy hxt hp S

theorem exists_noncentral_of_heis (N : Subgroup X) [N.Normal] (hN : N ≤ center X)
    {x t y : X ⧸ N} (hx3 : x ^ 3 = 1) (ht3 : t ^ 3 = 1) (hy : y * x * y⁻¹ = x⁻¹)
    (hc1 : x * t * x⁻¹ * t⁻¹ ≠ 1) (hc3 : (x * t * x⁻¹ * t⁻¹) ^ 3 = 1)
    (hct : x * t * x⁻¹ * t⁻¹ * t = t * (x * t * x⁻¹ * t⁻¹))
    (hcx : x * t * x⁻¹ * t⁻¹ * x = x * (x * t * x⁻¹ * t⁻¹)) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ u ∈ (S : Subgroup X), s * u ≠ u * s :=
  exists_noncentral_of_quotient N hN hx3 hy
    (fun h => hc1 (by rw [h]; group))
    (isPGroup_closure_heis (k := 1) hx3 (by rw [pow_one]; exact ht3) hc3 hct hcx) S

theorem exists_noncentral_of_quotient_centralizer (N : Subgroup X) [N.Normal]
    (hN : N ≤ center X) {x y : X ⧸ N} (hx3 : x ^ 3 = 1) (hy : y * x * y⁻¹ = x⁻¹) {n : ℕ}
    (hn : 3 ^ n ∣ Nat.card (X ⧸ N))
    (hC : ¬ 3 ^ n ∣ Nat.card (centralizer ({x} : Set (X ⧸ N)))) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ u ∈ (S : Subgroup X), s * u ≠ u * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (zpowers x) := isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one]; exact hx3)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨S', rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) 3 Q
  apply exists_noncentral_of_sylow S'
  have hxS : x ∈ (S' : Subgroup X).map (QuotientGroup.mk' N) := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N)]
    exact hQ (mem_zpowers x)
  obtain ⟨s, hs, hs3, rfl⟩ := exists_lift_of_real N hN S' hxS hx3 hy
  refine ⟨s, hs, hs3, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : (Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S' : Subgroup (X ⧸ N)) ≤
      centralizer ({QuotientGroup.mk' N s} : Set (X ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcon u hu]
  exact hC ((Sylow.pow_dvd_card_of_pow_dvd_card _ hn).trans (card_dvd_of_le hle))

theorem exists_noncentral_of_quotient_coprime (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N)
    (h : ∀ Q : Sylow 3 (X ⧸ N), ∃ s ∈ (Q : Subgroup (X ⧸ N)), s ^ 3 = 1 ∧
      ∃ t ∈ (Q : Subgroup (X ⧸ N)), s * t ≠ t * s) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ u ∈ (S : Subgroup X), s * u ≠ u * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨sb, hsb, hsb3, tb, htb, hst⟩ := h (S.mapSurjective (QuotientGroup.mk'_surjective N))
  rw [Sylow.coe_mapSurjective] at hsb htb
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hsb
  obtain ⟨t, ht, rfl⟩ := mem_map.mp htb
  have hdisj : Disjoint (S : Subgroup X) N := by
    obtain ⟨k, hk⟩ := (S.isPGroup').exists_card_eq
    refine disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
  have hs3 : s ^ 3 = 1 := by
    have hsN : s ^ 3 ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
      exact hsb3
    have hmem : s ^ 3 ∈ (S : Subgroup X) ⊓ N := mem_inf.mpr ⟨pow_mem hs 3, hsN⟩
    rw [hdisj.eq_bot, mem_bot] at hmem
    exact hmem
  exact ⟨s, hs, hs3, t, ht, fun hc => hst (by rw [← map_mul, ← map_mul, hc])⟩

end Sylow

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
