module

public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

private theorem w16g_commute_zpowers {G : Type*} [Group G] {z k : G} (hzk : Commute z k)
    {a b : G} (ha : a ∈ Subgroup.zpowers z) (hb : b ∈ Subgroup.zpowers k) : Commute a b := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact hzk.zpow_zpow i j

private theorem w16g_zpowers_le_normalizer {G : Type*} [Group G] {z k : G} (hzk : Commute z k) :
    Subgroup.zpowers k ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  have hc : Commute a b := w16g_commute_zpowers hzk ha hb
  rw [← hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact ha

private theorem w16g_zpow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {z : G} (hz : z ^ p = 1)
    {a : G} (ha : a ∈ Subgroup.zpowers z) : a ^ p = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  calc (z ^ i) ^ p = (z ^ i) ^ (p : ℤ) := by rw [zpow_natCast]
    _ = z ^ (i * (p : ℤ)) := by rw [zpow_mul]
    _ = (z ^ (p : ℤ)) ^ i := by rw [zpow_mul']
    _ = (z ^ p) ^ i := by rw [zpow_natCast]
    _ = 1 := by rw [hz, one_zpow]

private theorem w16g_inf_zpowers_eq_bot {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hzk : Commute z k)
    (hkz : k ∉ Subgroup.zpowers z) :
    Subgroup.zpowers z ⊓ Subgroup.zpowers k = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  rw [Subgroup.mem_bot] at hx1
  have hxord : orderOf x = p := by
    have hdvd : orderOf x ∣ p := hz ▸ orderOf_dvd_of_mem_zpowers hx.1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have hAz : Nat.card ↥(Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hBk : Nat.card ↥(Subgroup.zpowers k) = p := by rw [Nat.card_zpowers, hk]
  have hxx : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  haveI : Finite ↥(Subgroup.zpowers z) :=
    Nat.finite_of_card_ne_zero (by rw [hAz]; exact hp.ne_zero)
  haveI : Finite ↥(Subgroup.zpowers k) :=
    Nat.finite_of_card_ne_zero (by rw [hBk]; exact hp.ne_zero)
  haveI : Finite ↥(Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [hxx]; exact hp.ne_zero)
  have hxA : Subgroup.zpowers x ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hx.1
  have hxAeq : Subgroup.zpowers x = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hxA (by rw [hAz, hxx])
  have hxleB : Subgroup.zpowers x ≤ Subgroup.zpowers k := Subgroup.zpowers_le.mpr hx.2
  have hAle : Subgroup.zpowers z ≤ Subgroup.zpowers k := hxAeq ▸ hxleB
  have hAeqB : Subgroup.zpowers z = Subgroup.zpowers k :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hBk, hAz])
  exact hkz (hAeqB ▸ Subgroup.mem_zpowers k)

private theorem w16g_card_sup_of_le_normalizer_of_inf_eq_bot {G : Type*} [Group G]
    {N T : Subgroup G} (hT : T ≤ Subgroup.normalizer (N : Set G)) (hNT : N ⊓ T = ⊥) :
    Nat.card ↥(N ⊔ T) = Nat.card N * Nat.card T := by
  let f : N × T → ↥(N ⊔ T) := fun q =>
    ⟨q.1 * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨n, t⟩ ⟨n', t'⟩ heq
      have e : (n : G) * t = n' * t' := congrArg Subtype.val heq
      have h1 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
        calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
          _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [e]
          _ = t' * (t : G)⁻¹ := by group
      have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2) n.2,
          h1 ▸ Subgroup.mul_mem _ t'.2 (Subgroup.inv_mem _ t.2)⟩
      rw [hNT, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hn : n = n' := Subtype.ext hmem.symm
      subst hn
      have ht : t = t' := Subtype.ext (mul_left_cancel e)
      rw [ht]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N T hT] at hx'
      obtain ⟨n, hn, t, ht, rfl⟩ := hx'
      exact ⟨(⟨n, hn⟩, ⟨t, ht⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem w16g_isElemAbelian_sup_zpowers {G : Type*} [Group G] {p : ℕ} {z k : G} (hz : z ^ p = 1)
    (hk : k ^ p = 1) (hzk : Commute z k) :
    IsElemAbelian p (Subgroup.zpowers z ⊔ Subgroup.zpowers k) := by
  have hpair : (({z, k} : Set G)).Pairwise Commute := by
    intro a ha b hb _
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · simpa [ha, hb] using Commute.refl z
      · simpa [ha, hb] using hzk
    · rcases hb with hb | hb
      · simpa [ha, hb] using hzk.symm
      · simpa [ha, hb] using Commute.refl k
  have hEc : IsMulCommutative ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers k) := by
    have hcl : Subgroup.closure ({z, k} : Set G) =
        Subgroup.zpowers z ⊔ Subgroup.zpowers k := by
      rw [Subgroup.zpowers_eq_closure z, Subgroup.zpowers_eq_closure k,
        ← Subgroup.closure_union]
      congr 1
    exact hcl ▸ Subgroup.isMulCommutative_closure hpair
  refine ⟨hEc, ?_⟩
  intro x hx
  have hmem : x ∈ ((Subgroup.zpowers z ⊔ Subgroup.zpowers k : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (w16g_zpowers_le_normalizer hzk)] at hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem
  rw [Commute.mul_pow (w16g_commute_zpowers hzk ha hb) p, w16g_zpow_pow_eq_one hz ha,
    w16g_zpow_pow_eq_one hk hb, one_mul]

theorem w16g_card_sup_zpowers {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hzk : Commute z k)
    (hkz : k ∉ Subgroup.zpowers z) :
    Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers k) = p ^ 2 := by
  have hAz : Nat.card ↥(Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hBk : Nat.card ↥(Subgroup.zpowers k) = p := by rw [Nat.card_zpowers, hk]
  have hinf := w16g_inf_zpowers_eq_bot hp hz hk hzk hkz
  rw [w16g_card_sup_of_le_normalizer_of_inf_eq_bot (w16g_zpowers_le_normalizer hzk) hinf,
    hAz, hBk, sq]

private theorem w16g_orderOf_mul_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hzk : Commute z k)
    (hkz : k ∉ Subgroup.zpowers z) (i : Fin p) : orderOf (k * z ^ (i : ℕ)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz1 : z ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hk1 : k ^ p = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hne : k * z ^ (i : ℕ) ≠ 1 := by
    intro h
    apply hkz
    have hk_eq : k = (z ^ (i : ℕ))⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hk_eq, ← zpow_natCast]
    simpa [zpow_neg] using Subgroup.zpow_mem_zpowers z (-(i : ℤ))
  refine orderOf_eq_prime ?_ hne
  rw [Commute.mul_pow ((hzk.symm).pow_right (i : ℕ)) p, hk1, ← pow_mul, Nat.mul_comm,
    pow_mul, hz1, one_pow, mul_one]

theorem w16g_zpowers_mul_pow_injective {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hzk : Commute z k)
    (hkz : k ∉ Subgroup.zpowers z) :
    Function.Injective (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ))) ∧
      ∀ i : Fin p, Subgroup.zpowers (k * z ^ (i : ℕ)) ≠ Subgroup.zpowers z := by
  have hinf := w16g_inf_zpowers_eq_bot hp hz hk hzk hkz
  constructor
  · intro i j hij
    change Subgroup.zpowers (k * z ^ (i : ℕ)) = Subgroup.zpowers (k * z ^ (j : ℕ)) at hij
    have hmem : k * z ^ (i : ℕ) ∈ Subgroup.zpowers (k * z ^ (j : ℕ)) := by
      rw [← hij]
      exact Subgroup.mem_zpowers _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : k ^ m * z ^ ((j : ℤ) * m) = k * z ^ (i : ℕ) := by
      rw [← hm, Commute.mul_zpow ((hzk.symm).pow_right (j : ℕ)) m]
      congr 1
      rw [← zpow_natCast, zpow_mul]
    have hkey : k ^ (1 - m) * z ^ ((i : ℤ) - (j : ℤ) * m) = 1 := by
      calc k ^ (1 - m) * z ^ ((i : ℤ) - (j : ℤ) * m)
          = k ^ (-m) * (k * z ^ (i : ℕ)) * (z ^ ((j : ℤ) * m))⁻¹ := by group
        _ = k ^ (-m) * (k ^ m * z ^ ((j : ℤ) * m)) * (z ^ ((j : ℤ) * m))⁻¹ := by rw [← h2]
        _ = 1 := by group
    have hmemA : k ^ (1 - m) ∈ Subgroup.zpowers z := by
      have h : k ^ (1 - m) = (z ^ ((i : ℤ) - (j : ℤ) * m))⁻¹ :=
        eq_inv_of_mul_eq_one_left hkey
      rw [h]
      simpa [zpow_neg] using Subgroup.zpow_mem_zpowers z (-((i : ℤ) - (j : ℤ) * m))
    have hmemB : k ^ (1 - m) ∈ Subgroup.zpowers k := Subgroup.zpow_mem_zpowers k _
    have hkone : k ^ (1 - m) = 1 := by
      have hmem : k ^ (1 - m) ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers k :=
        Subgroup.mem_inf.mpr ⟨hmemA, hmemB⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hz_eq : z ^ ((i : ℤ) - (j : ℤ) * m) = 1 := by
      have h := hkey
      rw [hkone, one_mul] at h
      exact h
    have hdvd1 : (p : ℤ) ∣ (1 - m) := by
      have h := (orderOf_dvd_iff_zpow_eq_one (x := k) (i := 1 - m)).mpr hkone
      rwa [hk] at h
    have hdvd2 : (p : ℤ) ∣ ((i : ℤ) - (j : ℤ) * m) := by
      have h := (orderOf_dvd_iff_zpow_eq_one (x := z) (i := (i : ℤ) - (j : ℤ) * m)).mpr hz_eq
      rwa [hz] at h
    rw [show (1 : ℤ) - m = -(m - 1) by ring, Int.dvd_neg] at hdvd1
    obtain ⟨c, hc⟩ := hdvd1
    obtain ⟨d, hd⟩ := hdvd2
    have hmc : m = 1 + (p : ℤ) * c := by omega
    rw [hmc] at hd
    have hsub : (p : ℤ) ∣ ((i : ℤ) - (j : ℤ)) := by
      have h1 : (i : ℤ) - (j : ℤ) =
          ((i : ℤ) - (j : ℤ) * (1 + (p : ℤ) * c)) + (j : ℤ) * ((p : ℤ) * c) := by ring
      rw [h1, hd]
      exact ⟨d + (j : ℤ) * c, by ring⟩
    have hmod : i.val ≡ j.val [MOD p] := by
      rw [Nat.modEq_iff_dvd]
      rw [show ((j : ℤ) - (i : ℤ)) = -((i : ℤ) - (j : ℤ)) by ring]
      exact Int.dvd_neg.mpr hsub
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt)
  · intro i hi
    have hmem : k * z ^ (i : ℕ) ∈ Subgroup.zpowers z := by
      rw [← hi]
      exact Subgroup.mem_zpowers _
    have hzi : z ^ (i : ℕ) ∈ Subgroup.zpowers z := Subgroup.npow_mem_zpowers z _
    have : k = (k * z ^ (i : ℕ)) * (z ^ (i : ℕ))⁻¹ := by group
    exact hkz (this ▸ Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hzi))

theorem w16g_hyperplanes_sup_zpowers {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {z k : G}
    (hz : orderOf z = p) (hk : orderOf k = p) (hzk : Commute z k)
    (hkz : k ∉ Subgroup.zpowers z) :
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
        (Subgroup.zpowers z ⊔ Subgroup.zpowers k) =
      {Subgroup.zpowers z} ∪ Set.range (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup G := Subgroup.zpowers z with hA
  set B : Subgroup G := Subgroup.zpowers k with hB
  set E : Subgroup G := A ⊔ B with hE
  have hAz : Nat.card ↥A = p := by rw [Nat.card_zpowers, hz]
  have hz1 : z ^ p = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hk1 : k ^ p = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hEelem : IsElemAbelian p E := w16g_isElemAbelian_sup_zpowers hz1 hk1 hzk
  have hcardE : Nat.card ↥E = p ^ 2 := w16g_card_sup_zpowers hp hz hk hzk hkz
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcardE]; exact pow_ne_zero 2 hp.ne_zero)
  have hsub : ({A} ∪ Set.range (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ)))) ⊆
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p E := by
    rintro D (hD | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hD
      subst hD
      refine ⟨le_sup_left, ?_⟩
      have h := Subgroup.relIndex_mul_card (H := A) (K := E)
      rw [inf_of_le_left le_sup_left, hAz, hcardE] at h
      exact Nat.eq_of_mul_eq_mul_right hp.pos (h.trans (sq p))
    · have hWi : Nat.card ↥(Subgroup.zpowers (k * z ^ (i : ℕ))) = p := by
        rw [Nat.card_zpowers, w16g_orderOf_mul_pow hp hz hk hzk hkz i]
      have hWle : Subgroup.zpowers (k * z ^ (i : ℕ)) ≤ E := by
        rw [Subgroup.zpowers_le]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers k))
          (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers z (i : ℕ)))
      refine ⟨hWle, ?_⟩
      have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers (k * z ^ (i : ℕ))) (K := E)
      rw [inf_of_le_left hWle, hWi, hcardE] at h
      exact Nat.eq_of_mul_eq_mul_right hp.pos (h.trans (sq p))
  have hpair := w16g_zpowers_mul_pow_injective hp hz hk hzk hkz
  have hdisj : Disjoint ({A} : Set (Subgroup G))
      (Set.range (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ)))) := by
    rw [Set.disjoint_singleton_left]
    rintro ⟨i, hi⟩
    exact hpair.2 i hi
  have hrange : (Set.range (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ)))).ncard = p := by
    rw [Set.ncard_range_of_injective hpair.1, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrhs : ({A} ∪ Set.range (fun i : Fin p => Subgroup.zpowers (k * z ^ (i : ℕ)))).ncard =
      1 + p := by
    rw [Set.ncard_union_eq hdisj (Set.finite_singleton A) (Set.finite_range _),
      Set.ncard_singleton, hrange]
  have hcardHyp : Nat.card (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p E) =
      p + 1 := by
    rw [CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.card_hyperplanes
      hEelem (n := 2) (by norm_num) hcardE]
    simp [Finset.sum_range_succ, add_comm]
  have hfinHyp : (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p E).Finite := by
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero (by rw [hcardHyp]; omega)
  symm
  apply Set.eq_of_subset_of_ncard_le hsub _ hfinHyp
  rw [Nat.card_coe_set_eq] at hcardHyp
  omega

end CFSG.LocalAnalysis.WeakClosure81
