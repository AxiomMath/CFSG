module

public import CFSG.Quasithin.H13.NQCatLieOverRank1

public section

open scoped commutatorElement

namespace CFSG.Quasithin

open CFSG.Open CFSG.GH74.Uniqueness.Bender

@[expose] def IsRankOneSylowCyclic (K : Type*) [Group K] : Prop :=
  IsRankOneSylow K ∧ ∀ T : Subgroup K, IsPGroup 2 T → ¬ 2 ∣ T.index →
    ∃ D : Subgroup K, IsCyclic D ∧ T ⊔ D = Subgroup.normalizer (T : Set K)

theorem IsRankOneSylowCyclic.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : IsRankOneSylowCyclic K) : IsRankOneSylowCyclic K' := by
  obtain ⟨hR, hcyc⟩ := h
  refine ⟨hR.of_mulEquiv e, fun T' hT' hodd' => ?_⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hT : IsPGroup 2 (T'.comap e.toMonoidHom) :=
    hT'.comap_of_injective e.toMonoidHom e.injective
  have hodd : ¬ 2 ∣ (T'.comap e.toMonoidHom).index := by
    rw [Subgroup.index_comap_of_surjective T' hsurj]
    exact hodd'
  obtain ⟨D, hD, hsup⟩ := hcyc _ hT hodd
  refine ⟨D.map e.toMonoidHom, (MulEquiv.subgroupMap e D).isCyclic.mp hD, ?_⟩
  have h1 : (T'.comap e.toMonoidHom).map e.toMonoidHom = T' :=
    Subgroup.map_comap_eq_self_of_surjective hsurj T'
  have h2 := congrArg (Subgroup.map e.toMonoidHom) hsup
  rw [Subgroup.map_sup, h1] at h2
  rw [h2, Subgroup.map_equiv_normalizer_eq _ e, h1]

theorem isRankOneSylowCyclic_of_benderType {K : Type*} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) : IsRankOneSylowCyclic K := by
  refine ⟨CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType h, fun T hT hodd => ?_⟩
  have hQ : ((hT.toSylow hodd : Sylow 2 K) : Subgroup K) = T := IsPGroup.toSylow_coe hT hodd
  obtain ⟨t, hc⟩ := h.exists_benderCore (hT.toSylow hodd)
  rw [hQ] at hc
  exact ⟨cartan T t, hc.isCyclic, hc.sup_eq⟩

section Cover

variable {K K' : Type*} [Group K] [Group K']

theorem eq_one_of_odd_orderOf_of_pow {w : K} (ho : Odd (orderOf w)) {k : ℕ}
    (hw : w ^ 2 ^ k = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hw
  have h2 : Nat.Coprime (orderOf w) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 ho)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem exists_mul_of_sup_eq_normalizer {P D : Subgroup K'} (hsup : P ⊔ D = Subgroup.normalizer
    (P : Set K')) {x : K'} (hx : x ∈ Subgroup.normalizer (P : Set K')) :
    ∃ p ∈ P, ∃ d ∈ D, x = p * d := by
  set N := Subgroup.normalizer (P : Set K') with hNdef
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hDN : D ≤ N := hsup ▸ le_sup_right
  have htop : P.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPN hDN, hsup, Subgroup.subgroupOf_self]
  obtain ⟨p, hp, d, hd, hpd⟩ := Subgroup.mem_sup_of_normal_left.mp
    (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥N))
  exact ⟨p, hp, d, hd, (congrArg Subtype.val hpd).symm⟩

theorem commutator_mul_center_left {a b z : K} (hz : z ∈ Subgroup.center K) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b * z⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hz b).symm
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅a, b⁆ := by rw [h]; simp [commutatorElement_def, mul_assoc]

theorem commutator_mul_center_right {a b z : K} (hz : z ∈ Subgroup.center K) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hz a⁻¹).symm
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅a, b⁆ := by rw [h]; simp [commutatorElement_def, mul_assoc]

theorem commutator_mul_central {m₁ m₂ z₁ z₂ : K} (h₁ : z₁ ∈ Subgroup.center K)
    (h₂ : z₂ ∈ Subgroup.center K) : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
  rw [commutator_mul_center_left h₁, commutator_mul_center_right h₂]

theorem commutator_mem_of_mul_normalizer {T : Subgroup K} {p q w v : K} (hp : p ∈ T) (hq : q ∈ T)
    (hw : w ∈ Subgroup.normalizer (T : Set K)) (hv : v ∈ Subgroup.normalizer (T : Set K))
    (hwv : w * v = v * w) : ⁅p * w, q * v⁆ ∈ T := by
  have h1 : w * q * w⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hw q).mp hq
  have h2 : v * p⁻¹ * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hv p⁻¹).mp (T.inv_mem hp)
  have hc : v * w⁻¹ = w⁻¹ * v := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hwv, ← mul_assoc, inv_mul_cancel, one_mul]
  have e : ⁅p * w, q * v⁆ = p * (w * q * w⁻¹) * (v * p⁻¹ * v⁻¹) * q⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    have : v * (w⁻¹ * (p⁻¹ * (v⁻¹ * q⁻¹))) = w⁻¹ * (v * (p⁻¹ * (v⁻¹ * q⁻¹))) := by
      rw [← mul_assoc, hc, mul_assoc]
    rw [this]
  rw [e]
  exact T.mul_mem (T.mul_mem (T.mul_mem hp h1) h2) (T.inv_mem hq)

theorem isRankOneSylow_of_central_cover (π : K →* K') (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) (hodd : ∀ z ∈ π.ker, Odd (orderOf z))
    (hcomm : π.ker ≤ commutator K) (h : IsRankOneSylowCyclic K') : IsRankOneSylow K := by
  obtain ⟨hR, hcyc⟩ := h
  intro T hT hTodd
  have hTexp : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hT'p : IsPGroup 2 (T.map π) := hT.map π
  have hT'odd : ¬ 2 ∣ (T.map π).index := fun hd =>
    hTodd (hd.trans (Subgroup.index_map_dvd T hπ))
  obtain ⟨hN', hM', -⟩ := hR (T.map π) hT'p hT'odd
  obtain ⟨D', hD'cyc, hsup'⟩ := hcyc (T.map π) hT'p hT'odd
  have hclaim : ∀ x : K, π x ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') →
      ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro x hx t ht
    have hu : π (x * t * x⁻¹) ∈ T.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hx (π t)).mp (Subgroup.mem_map_of_mem π ht)
    obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.mp hu
    obtain ⟨z, hzdef⟩ : ∃ z, z = t0⁻¹ * (x * t * x⁻¹) := ⟨_, rfl⟩
    have hz : z ∈ π.ker := by
      rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, ht0eq, inv_mul_cancel]
    have hu_eq : x * t * x⁻¹ = t0 * z := by rw [hzdef]; group
    have hcomm : Commute t0 z := Subgroup.mem_center_iff.mp (hZ hz) t0
    obtain ⟨k1, hk1⟩ := hTexp t ht
    obtain ⟨k2, hk2⟩ := hTexp t0 ht0
    have hpt : (x * t * x⁻¹) ^ 2 ^ (k1 + k2) = 1 := by
      rw [conj_pow, pow_add, pow_mul, hk1, one_pow]
      simp
    have hpt0 : t0 ^ 2 ^ (k1 + k2) = 1 := by
      rw [add_comm, pow_add, pow_mul, hk2, one_pow]
    have hzp : z ^ 2 ^ (k1 + k2) = 1 := by
      rw [hu_eq, hcomm.mul_pow, hpt0, one_mul] at hpt
      exact hpt
    have hz1 : z = 1 := eq_one_of_odd_orderOf_of_pow (hodd z hz) hzp
    rw [hu_eq, hz1, mul_one]
    exact ht0
  have hE : ∀ x : K, π x ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') →
      x ∈ Subgroup.normalizer (T : Set K) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hclaim x hx g hg, fun hg => ?_⟩
    have hx' : π x⁻¹ ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hx
    have := hclaim x⁻¹ hx' _ hg
    simpa [mul_assoc] using this
  have hNT : ∀ x ∈ Subgroup.normalizer (T : Set K),
      π x ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') :=
    fun x hx => Subgroup.le_normalizer_map π ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hNtop
    have hnorm : T.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    exact hN' (Subgroup.normalizer_eq_top_iff.mpr (hnorm.map π hπ))
  · intro M hTM hMtop
    by_cases hMπ : M.map π = ⊤
    · exfalso
      apply hMtop
      have hsplit : ∀ k : K, ∃ m ∈ M, ∃ z ∈ π.ker, k = m * z := by
        intro k
        have : π k ∈ M.map π := hMπ ▸ Subgroup.mem_top _
        obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp this
        refine ⟨m, hm, m⁻¹ * k, ?_, by group⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
      have hcommM : commutator K ≤ M := by
        rw [commutator_def, Subgroup.commutator_le]
        intro g1 _ g2 _
        obtain ⟨m1, hm1, z1, hz1, rfl⟩ := hsplit g1
        obtain ⟨m2, hm2, z2, hz2, rfl⟩ := hsplit g2
        rw [commutator_mul_central (hZ hz1) (hZ hz2)]
        exact M.mul_mem (M.mul_mem (M.mul_mem hm1 hm2) (M.inv_mem hm1)) (M.inv_mem hm2)
      rw [eq_top_iff]
      intro k _
      obtain ⟨m, hm, z, hz, rfl⟩ := hsplit k
      exact M.mul_mem hm (hcommM (hcomm hz))
    · intro m hm
      exact hE m (hM' (M.map π) (Subgroup.map_mono hTM) hMπ (Subgroup.mem_map_of_mem π hm))
  · intro x hx y hy
    obtain ⟨g, hg⟩ := hD'cyc.exists_generator
    obtain ⟨d0, hd0⟩ := hπ (g : K')
    have hDle : D' ≤ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') :=
      hsup' ▸ le_sup_right
    have hd0N : d0 ∈ Subgroup.normalizer (T : Set K) := hE d0 (by rw [hd0]; exact hDle g.2)
    have hdec : ∀ x ∈ Subgroup.normalizer (T : Set K), ∃ p0 ∈ T, ∃ a : ℤ,
        ∃ z ∈ Subgroup.center K, x = p0 * d0 ^ a * z := by
      intro x hx
      obtain ⟨p, hp, e, he, hxe⟩ := exists_mul_of_sup_eq_normalizer hsup' (hNT x hx)
      obtain ⟨p0, hp0, hp0eq⟩ := Subgroup.mem_map.mp hp
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨e, he⟩)
      have hea : (g : K') ^ a = e := by
        have := congrArg Subtype.val ha
        simpa using this
      have hπx1 : π (p0 * d0 ^ a) = π x := by
        rw [map_mul, map_zpow, hp0eq, hd0, hea, ← hxe]
      refine ⟨p0, hp0, a, (p0 * d0 ^ a)⁻¹ * x, hZ ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπx1, inv_mul_cancel]
    obtain ⟨p0, hp0, a, z1, hz1, rfl⟩ := hdec x hx
    obtain ⟨q0, hq0, b, z2, hz2, rfl⟩ := hdec y hy
    have key : ⁅p0 * d0 ^ a * z1, q0 * d0 ^ b * z2⁆ ∈ T := by
      rw [commutator_mul_central hz1 hz2]
      exact commutator_mem_of_mul_normalizer hp0 hq0 (Subgroup.zpow_mem _ hd0N a)
        (Subgroup.zpow_mem _ hd0N b) (Commute.zpow_zpow_self d0 a b).eq
    exact key

end Cover

end CFSG.Quasithin
