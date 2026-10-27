module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.QuasithinUnique

section CentralOdd

variable {K : Type} [Group K] [Finite K] (Z : Subgroup K) [Z.Normal]

private theorem mem_of_pow_two_pow_of_mk'_mem {T : Subgroup K} (hT : IsPGroup 2 T)
    (hZ : Z ≤ Subgroup.center K) (hZodd : ¬ 2 ∣ Nat.card Z) {x : K} {m : ℕ}
    (hx : x ^ 2 ^ m = 1) (hπ : QuotientGroup.mk' Z x ∈ T.map (QuotientGroup.mk' Z)) :
    x ∈ T := by
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hπ
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at htx
  obtain ⟨z, hzZ, rfl⟩ : ∃ z ∈ Z, x = t * z :=
    ⟨t⁻¹ * x, (QuotientGroup.eq (s := Z)).1 htx, (mul_inv_cancel_left t x).symm⟩
  have htz : Commute t z := Subgroup.mem_center_iff.mp (hZ hzZ) t
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hN : (t * z) ^ (2 ^ k * 2 ^ m) = 1 := by
    rw [show 2 ^ k * 2 ^ m = 2 ^ m * 2 ^ k from mul_comm _ _, pow_mul, hx, one_pow]
  have htN : t ^ (2 ^ k * 2 ^ m) = 1 := by
    rw [pow_mul, hk', one_pow]
  have hzN : z ^ (2 ^ k * 2 ^ m) = 1 := by
    have h1 := htz.mul_pow (2 ^ k * 2 ^ m)
    rw [htN, one_mul, hN] at h1
    exact h1.symm
  have hcop : Nat.Coprime (2 ^ k * 2 ^ m) (Nat.card Z) := by
    rw [← pow_add]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hZodd)
  have hdvdZ : orderOf z ∣ Nat.card Z := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzZ)
    rwa [Nat.card_zpowers] at this
  have hone : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hzN) hcop) hdvdZ
  rw [orderOf_eq_one_iff.mp hone, mul_one]
  exact ht

private theorem card_comap_mk' (S : Subgroup (K ⧸ Z)) :
    Nat.card (S.comap (QuotientGroup.mk' Z)) = Nat.card Z * Nat.card S := by
  have h1 := Subgroup.card_mul_index (S.comap (QuotientGroup.mk' Z))
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)] at h1
  have h2 := Subgroup.card_mul_index S
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h3, ← h2]
  ring

theorem normalizer_eq_comap_of_central_odd (hZ : Z ≤ Subgroup.center K) (hZodd : ¬ 2 ∣ Nat.card Z)
    {T : Subgroup K} (hT : IsPGroup 2 T) :
    Subgroup.normalizer (T : Set K) =
      (Subgroup.normalizer ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) :
        Set (K ⧸ Z))).comap (QuotientGroup.mk' Z) := by
  have fwd : ∀ g : K, (∀ t ∈ T, g * t * g⁻¹ ∈ T) →
      ∀ y ∈ T.map (QuotientGroup.mk' Z),
        QuotientGroup.mk' Z g * y * (QuotientGroup.mk' Z g)⁻¹ ∈ T.map (QuotientGroup.mk' Z) := by
    intro g hg y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have e : QuotientGroup.mk' Z g * QuotientGroup.mk' Z t * (QuotientGroup.mk' Z g)⁻¹ =
        QuotientGroup.mk' Z (g * t * g⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map.mpr ⟨g * t * g⁻¹, hg t ht, rfl⟩
  have bwd : ∀ g : K, QuotientGroup.mk' Z g ∈ Subgroup.normalizer
      ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) →
      ∀ h ∈ T, g * h * g⁻¹ ∈ T := by
    intro g hg h hh
    obtain ⟨k, hk⟩ := hT ⟨h, hh⟩
    have hk' : h ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine mem_of_pow_two_pow_of_mk'_mem Z hT hZ hZodd (m := k) ?_ ?_
    · rw [conj_pow, hk', mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg (QuotientGroup.mk' Z h)).mp
        (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
  ext g
  rw [Subgroup.mem_comap]
  constructor
  · intro hg
    have hconj : ∀ t ∈ T, g * t * g⁻¹ ∈ T := fun t ht =>
      (Subgroup.mem_normalizer_iff.mp hg t).mp ht
    have hginv : g⁻¹ ∈ Subgroup.normalizer (T : Set K) := inv_mem hg
    have hconj' : ∀ t ∈ T, g⁻¹ * t * g⁻¹⁻¹ ∈ T := fun t ht =>
      (Subgroup.mem_normalizer_iff.mp hginv t).mp ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact fwd g hconj y hy
    · intro hy
      have h1 := fwd g⁻¹ hconj' _ hy
      have e : QuotientGroup.mk' Z g⁻¹ * (QuotientGroup.mk' Z g * y * (QuotientGroup.mk' Z g)⁻¹) *
          (QuotientGroup.mk' Z g⁻¹)⁻¹ = y := by
        simp only [map_inv, inv_inv]
        group
      rw [e] at h1
      exact h1
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact bwd g hg h hh
    · intro hh
      have hginv : QuotientGroup.mk' Z g⁻¹ ∈ Subgroup.normalizer
          ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) := by
        rw [map_inv]
        exact inv_mem hg
      have h1 := bwd g⁻¹ hginv _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact h1

theorem card_normalizer_of_central_odd (hZ : Z ≤ Subgroup.center K) (hZodd : ¬ 2 ∣ Nat.card Z)
    {T : Subgroup K} (hT : IsPGroup 2 T) :
    Nat.card ↥(Subgroup.normalizer (T : Set K)) = Nat.card Z *
      Nat.card ↥(Subgroup.normalizer ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) :
        Set (K ⧸ Z))) := by
  rw [normalizer_eq_comap_of_central_odd Z hZ hZodd hT]
  exact card_comap_mk' Z _

theorem isSylowTwoOf_map_mk' {T : Subgroup K} (hT : IsSylowTwoOf T ⊤) :
    IsSylowTwoOf (T.map (QuotientGroup.mk' Z)) ⊤ := by
  obtain ⟨-, hT2, hTi⟩ := hT
  change ¬ 2 ∣ T.relIndex ⊤ at hTi
  rw [Subgroup.relIndex_top_right] at hTi
  unfold IsSylowTwoOf
  refine ⟨le_top, hT2.map (QuotientGroup.mk' Z), ?_⟩
  change ¬ 2 ∣ (T.map (QuotientGroup.mk' Z)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact fun h => hTi (dvd_trans h (Subgroup.index_map_dvd T (QuotientGroup.mk'_surjective Z)))

theorem overgroup_of_central_quotient (hZ : Z ≤ Subgroup.center K) (hZ3 : Nat.card Z = 3)
    (hbar : ∀ T' N' W' : Subgroup (K ⧸ Z), IsSylowTwoOf T' ⊤ →
      Subgroup.normalizer (T' : Set (K ⧸ Z)) ≤ N' → N' ≠ Subgroup.normalizer (T' : Set (K ⧸ Z)) →
      N' ≠ ⊤ → W' ≤ N' → (W'.subgroupOf N').Normal →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card W' → p = 2 ∨ p = 3) → ¬ 3 ∣ Nat.card W')
    (T N W : Subgroup K) (hT : IsSylowTwoOf T ⊤) (hB : Subgroup.normalizer (T : Set K) ≤ N)
    (hNB : N ≠ Subgroup.normalizer (T : Set K)) (hNK : N ≠ ⊤) (hWN : W ≤ N)
    (hWnorm : (W.subgroupOf N).Normal)
    (hW23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) : ¬ 9 ∣ Nat.card W := by
  intro h9
  have hZodd : ¬ 2 ∣ Nat.card Z := by
    rw [hZ3]
    norm_num
  have hZN : Z ≤ N := hZ.trans ((Subgroup.center_le_normalizer (T : Set K)).trans hB)
  have hcomapN : (N.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZN]
  have hnorm : ∀ x : K, x ∈ Subgroup.normalizer (T : Set K) ↔
      QuotientGroup.mk' Z x ∈ Subgroup.normalizer
        ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) := by
    intro x
    rw [normalizer_eq_comap_of_central_odd Z hZ hZodd hT.2.1, Subgroup.mem_comap]
  have hbarT : IsSylowTwoOf (T.map (QuotientGroup.mk' Z)) ⊤ := isSylowTwoOf_map_mk' Z hT
  have hBar : Subgroup.normalizer ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) :
      Set (K ⧸ Z)) ≤ N.map (QuotientGroup.mk' Z) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact Subgroup.mem_map.mpr ⟨x, hB ((hnorm x).mpr hy), rfl⟩
  have hNB' : N.map (QuotientGroup.mk' Z) ≠
      Subgroup.normalizer ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) := by
    intro heq
    apply hNB
    refine le_antisymm ?_ hB
    intro x hx
    rw [hnorm x, ← heq]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hNK' : N.map (QuotientGroup.mk' Z) ≠ ⊤ := by
    intro htop
    apply hNK
    have h1 := hcomapN
    rw [htop, Subgroup.comap_top] at h1
    exact h1.symm
  have hWN' : W.map (QuotientGroup.mk' Z) ≤ N.map (QuotientGroup.mk' Z) :=
    Subgroup.map_mono hWN
  have hWnorm' :
      ((W.map (QuotientGroup.mk' Z)).subgroupOf (N.map (QuotientGroup.mk' Z))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hWN']
    intro x k hx hk
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨b * a * b⁻¹,
      (Subgroup.normal_subgroupOf_iff hWN).mp hWnorm a b ha hb, ?_⟩
    simp only [map_mul, map_inv]
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (W.map (QuotientGroup.mk' Z)) →
      p = 2 ∨ p = 3 := by
    intro p hp hpd
    exact hW23 p hp (dvd_trans hpd (Subgroup.card_map_dvd W (QuotientGroup.mk' Z)))
  have h3 : ¬ 3 ∣ Nat.card (W.map (QuotientGroup.mk' Z)) :=
    hbar _ _ _ hbarT hBar hNB' hNK' hWN' hWnorm' hprime
  apply h3
  have hcard : Nat.card (W ⊔ Z : Subgroup K) =
      Nat.card Z * Nat.card (W.map (QuotientGroup.mk' Z)) := by
    have h := card_comap_mk' Z (W.map (QuotientGroup.mk' Z))
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have hWdvd : Nat.card W ∣ Nat.card (W ⊔ Z : Subgroup K) :=
    Subgroup.card_dvd_of_le le_sup_left
  rw [hZ3] at hcard
  have h9' := dvd_trans h9 hWdvd
  rw [hcard] at h9'
  omega

end CentralOdd

end CFSG.Quasithin.H13.S126P31
