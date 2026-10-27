module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Facts
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Group

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

open scoped Pointwise
open Subgroup CFSG.Sporadic.Schreier.Co3

theorem exists_conj_pow {G : Type*} [Group G] [Finite G] {x y : G} {r : ℕ} (hr : r.Prime)
    (hG : ¬ r ^ 2 ∣ Nat.card G) (hx : orderOf x = r) (hy : orderOf y = r) :
    ∃ g : G, ∃ n : ℕ, ¬ r ∣ n ∧ x = g * y ^ n * g⁻¹ := by
  have : Fact r.Prime := ⟨hr⟩
  have hP : ∀ w : G, orderOf w = r → IsPGroup r (zpowers w) := fun w hw =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
  have hI : ∀ w : G, orderOf w = r → ¬ r ∣ (zpowers w).index := fun w hw h => by
    apply hG
    have e := (zpowers w).card_mul_index
    rw [Nat.card_zpowers, hw] at e
    rw [← e, pow_two]
    exact Nat.mul_dvd_mul_left r h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ((hP y hy).toSylow (hI y hy))
    ((hP x hx).toSylow (hI x hx))
  have hg' : MulAut.conj g • zpowers y = zpowers x := by
    have h1 := congrArg (fun S : Sylow r G => (S : Subgroup G)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1
  have hxm : x ∈ MulAut.conj g • zpowers y := hg' ▸ mem_zpowers x
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← mem_powers_iff_mem_zpowers] at hxm
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 hxm
  rw [MulAut.smul_def, MulAut.conj_inv_apply] at hn
  refine ⟨g, n, fun h => ?_, ?_⟩
  · have h1 : y ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 (hy ▸ h)
    rw [h1] at hn
    have hx1 : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [← hn]; group
    rw [hx1, orderOf_one] at hx
    exact hr.one_lt.ne hx
  · rw [hn]
    group

theorem card_centralizer_of_support {σ : Equiv.Perm (Fin 36)} {r k : ℕ} (hr : r.Prime)
    (hσ : orderOf σ = r) (hs : σ.support.card = 35) (hk : k * r = 35) :
    Nat.card (centralizer {σ}) = r ^ k * k.factorial := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hσ ▸ hr)
  rw [hσ] at hn
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, hs] at hsum
  have hnk : n + 1 = k := Nat.eq_of_mul_eq_mul_right hr.pos (hsum.trans hk.symm)
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  rw [Equiv.Perm.nat_card_centralizer, hn, hnk, Multiset.sum_replicate, smul_eq_mul, hk,
    Multiset.prod_replicate, Multiset.toFinset_replicate, if_neg hk0, Finset.prod_singleton,
    Multiset.count_replicate_self, Fintype.card_fin]
  simp

theorem orderOf_co3Kx5M :
    orderOf (⟨co3Kx5, co3Kx5_mem⟩ : co3M) = 5 := by
  rw [orderOf_mk]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime co3Kx5_pow co3Kx5_ne_one

theorem orderOf_co3Kx7M :
    orderOf (⟨co3Kx7, co3Kx7_mem⟩ : co3M) = 7 := by
  rw [orderOf_mk]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime co3Kx7_pow co3Kx7_ne_one

theorem kappa_support_of_orderOf
    {x : co3M} {r : ℕ} (hr : r = 5 ∨ r = 7)
    (hx : orderOf x = r) : (co3Kappa x).support.card = 35 ∧ orderOf (co3Kappa x) = r := by
  obtain ⟨xr, hxr, hs⟩ : ∃ xr : co3M, orderOf xr = r ∧ (co3Kappa xr).support.card = 35 := by
    rcases hr with rfl | rfl
    · exact ⟨_, orderOf_co3Kx5M, co3Kx5_support⟩
    · exact ⟨_, orderOf_co3Kx7M, co3Kx7_support⟩
  have hrp : r.Prime := by
    rcases hr with rfl | rfl <;> norm_num
  have : Fact r.Prime := ⟨hrp⟩
  have hG : ¬ r ^ 2 ∣ Nat.card co3M := by
    rw [card_co3M]
    rcases hr with rfl | rfl <;> decide
  obtain ⟨g, n, hn, hxg⟩ := exists_conj_pow hrp hG hx hxr
  have hne : ∀ σ : Equiv.Perm (Fin 36), σ.support.card = 35 → σ ≠ 1 := fun σ h h1 => by
    rw [h1, Equiv.Perm.support_one, Finset.card_empty] at h
    exact absurd h (by norm_num)
  have hκo : orderOf (co3Kappa xr) = r :=
    orderOf_eq_prime (by rw [← map_pow, ← hxr, pow_orderOf_eq_one, map_one]) (hne _ hs)
  have hsupp : (co3Kappa xr ^ n).support = (co3Kappa xr).support :=
    Equiv.Perm.support_pow_coprime (by
      rw [hκo]
      exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hrp).2 hn))
  have hcx : co3Kappa x = co3Kappa g * co3Kappa xr ^ n * (co3Kappa g)⁻¹ := by
    rw [hxg, map_mul, map_mul, map_inv, map_pow]
  have hsx : (co3Kappa x).support.card = 35 := by
    rw [hcx, Equiv.Perm.card_support_conj, hsupp, hs]
  exact ⟨hsx, orderOf_eq_prime (by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one])
    (hne _ hsx)⟩

theorem card_le_thirtyTwo_of_le_centralizer
    {x : Equiv.Perm (Fin 276)} (hx : x ∈ co3M) {r : ℕ}
    (hr : r = 5 ∨ r = 7) (hxr : orderOf x = r) {D : Subgroup (Equiv.Perm (Fin 276))}
    (hDM : D ≤ co3M) (hDx : D ≤ centralizer {x}) (hD : Nat.card D ∣ 1024) :
    Nat.card D ≤ 32 := by
  classical
  set x' : co3M := ⟨x, hx⟩ with hx'def
  have hx' : orderOf x' = r := by rw [hx'def, orderOf_mk, hxr]
  obtain ⟨hs, ho⟩ := kappa_support_of_orderOf hr hx'
  set σ := co3Kappa x' with hσ
  have hC : Nat.card (centralizer {σ}) = 393750000 ∨ Nat.card (centralizer {σ}) = 2016840 := by
    rcases hr with rfl | rfl
    · left
      rw [card_centralizer_of_support (k := 7) (by norm_num) ho hs (by norm_num)]
      decide
    · right
      rw [card_centralizer_of_support (k := 5) (by norm_num) ho hs (by norm_num)]
      decide
  set D' := D.subgroupOf co3M with hD'
  have hcardD : Nat.card D' = Nat.card D := by
    rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
  let ψ : D' →* Equiv.Perm (Fin 36) := co3Kappa.comp D'.subtype
  have hker : Nat.card ψ.ker ≤ 2 := by
    have e : ψ.ker = co3Kappa.ker.subgroupOf D' := by
      ext d
      rfl
    rw [e, ← card_map_of_injective (K := co3Kappa.ker.subgroupOf D') D'.subtype_injective,
      subgroupOf_map_subtype, ← card_ker_co3Kappa]
    exact card_le_of_le inf_le_left
  have hrange : ψ.range ≤ centralizer {σ} := by
    rintro _ ⟨d, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hd : ((d : co3M) : Equiv.Perm (Fin 276)) * x = x * (d : co3M) :=
      mem_centralizer_singleton_iff.1 (hDx (mem_subgroupOf.1 d.2))
    have hd' : (d : co3M) * x' = x' * (d : co3M) := Subtype.ext hd
    change co3Kappa (d : co3M) * co3Kappa x' = co3Kappa x' * co3Kappa (d : co3M)
    rw [← map_mul, ← map_mul, hd']
  have hmul := card_ker_mul_card_range ψ
  have h1 : Nat.card ψ.range ∣ 1024 := (Dvd.intro_left _ hmul).trans (hcardD ▸ hD)
  have h2 := card_dvd_of_le hrange
  have h16 : Nat.card ψ.range ≤ 16 := by
    rcases hC with h | h
    · rw [h] at h2
      have h3 := Nat.dvd_gcd h1 h2
      rw [show Nat.gcd 1024 393750000 = 16 by norm_num] at h3
      exact Nat.le_of_dvd (by norm_num) h3
    · rw [h] at h2
      have h3 := Nat.dvd_gcd h1 h2
      rw [show Nat.gcd 1024 2016840 = 8 by norm_num] at h3
      exact (Nat.le_of_dvd (by norm_num) h3).trans (by norm_num)
  rw [← hcardD, ← hmul]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 2 * 16 := Nat.mul_le_mul hker h16
    _ = 32 := by norm_num

theorem false_of_le_normalizer
    {Q L : Subgroup (Equiv.Perm (Fin 276))} (hQM : Q ≤ co3M)
    (hLM : L ≤ co3M) (hQL : Q ≤ normalizer (L : Set (Equiv.Perm (Fin 276)))) (hL : L ≠ ⊥)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hLr : ∀ x ∈ L, x ^ r = 1)
    (hQ : Nat.card Q ∣ 1024) (hQ256 : 256 ≤ Nat.card Q) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hLp : IsPGroup r L := fun g => ⟨1, Subtype.ext (by simp [hLr _ g.2])⟩
  obtain ⟨k, hk⟩ := hLp.exists_card_eq
  have hLM' : r ^ k ∣ 2903040 := by
    rw [← hk, ← card_co3M]
    exact card_dvd_of_le hLM
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact hL hk
  have hr57 : r = 5 ∨ r = 7 := by
    have hdvd : r ∣ 2 ^ 10 * 3 ^ 4 * 5 * 7 := by
      have h := (dvd_pow_self r hk0).trans hLM'
      norm_num
      exact h
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
            hr2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
            (hr.dvd_of_dvd_pow h)) hr3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
  have hk1 : k = 1 := by
    by_contra hk1
    have h2 : r ^ 2 ∣ 2903040 := (pow_dvd_pow r (by omega)).trans hLM'
    rcases hr57 with rfl | rfl <;> norm_num at h2
  rw [hk1, pow_one] at hk
  obtain ⟨⟨x, hxL⟩, hx1⟩ := ne_bot_iff_exists_ne_one.1 hL
  have hxo : orderOf x = r :=
    orderOf_eq_prime (hLr x hxL) (fun h => hx1 (Subtype.ext h))
  have hdiv := card_dvd_pred_mul_card_inf_centralizer (hk ▸ hr : (Nat.card L).Prime) hQL
  rw [hk] at hdiv
  have hD32 : Nat.card ↥(Q ⊓ centralizer (L : Set (Equiv.Perm (Fin 276)))) ≤ 32 :=
    card_le_thirtyTwo_of_le_centralizer (hLM hxL) hr57 hxo (inf_le_left.trans hQM)
      (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.2 hxL)))
      ((card_dvd_of_le inf_le_left).trans hQ)
  have hpos : 0 < (r - 1) * Nat.card ↥(Q ⊓ centralizer (L : Set (Equiv.Perm (Fin 276)))) :=
    Nat.mul_pos (by rcases hr57 with rfl | rfl <;> norm_num) Nat.card_pos
  have hle := Nat.le_of_dvd hpos hdiv
  rcases hr57 with rfl | rfl <;> omega

theorem mem_normalizer_inf_centralizer {G : Type*} [Group G] {A : Subgroup G} {c t : G}
    (htA : t ∈ normalizer (A : Set G)) (htc : t * c = c * t) :
    t ∈ normalizer ((A ⊓ centralizer {c} : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at htA ⊢
  have hc : t * c * t⁻¹ = c := by rw [htc, mul_inv_cancel_right]
  intro y
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← htA y]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · calc t * y * t⁻¹ * c = t * y * t⁻¹ * (t * c * t⁻¹) := by rw [hc]
      _ = t * (y * c) * t⁻¹ := by group
      _ = t * (c * y) * t⁻¹ := by rw [h]
      _ = t * c * t⁻¹ * (t * y * t⁻¹) := by group
      _ = c * (t * y * t⁻¹) := by rw [hc]
  · have h' : t * (y * c) * t⁻¹ = t * (c * y) * t⁻¹ := by
      calc t * (y * c) * t⁻¹ = t * y * t⁻¹ * (t * c * t⁻¹) := by group
        _ = t * y * t⁻¹ * c := by rw [hc]
        _ = c * (t * y * t⁻¹) := h
        _ = t * c * t⁻¹ * (t * y * t⁻¹) := by rw [hc]
        _ = t * (c * y) * t⁻¹ := by group
    simpa using h'

theorem card_co3T_inf_centralizer_e :
    512 ≤ Nat.card ↥(co3T ⊓ centralizer {co3Ke}) := by
  classical
  set e' : co3T := ⟨co3Ke, co3Ke_mem⟩
  set ez' : co3T := ⟨co3Ke * co3Z, co3T.mul_mem co3Ke_mem co3Z_mem_T⟩
  have hconj : conjugatesOf e' ⊆ {e', ez'} := by
    intro y hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 (show IsConj e' y from hy)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases co3Ke_conj c.2 with h | h
    · left
      refine Subtype.ext ?_
      change (c : Equiv.Perm (Fin 276)) * co3Ke * (c : Equiv.Perm (Fin 276))⁻¹ = co3Ke
      rw [h, mul_inv_cancel_right]
    · right
      refine Subtype.ext ?_
      change (c : Equiv.Perm (Fin 276)) * co3Ke * (c : Equiv.Perm (Fin 276))⁻¹ = co3Ke * co3Z
      rw [h, mul_inv_cancel_right]
  have hidx : (centralizer {e'}).index ≤ 2 := by
    rw [index_centralizer_eq_ncard]
    calc (conjugatesOf e').ncard ≤ ({e', ez'} : Set co3T).ncard := Set.ncard_le_ncard hconj
      _ ≤ ({ez'} : Set co3T).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hmul := (centralizer {e'}).card_mul_index
  rw [card_co3T] at hmul
  have hle : (centralizer {e'}).map co3T.subtype ≤ co3T ⊓ centralizer {co3Ke} := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
  have h1 := card_le_of_le hle
  rw [card_map_of_injective co3T.subtype_injective] at h1
  have h2 : 1024 ≤ Nat.card (centralizer {e'}) * 2 := hmul ▸ Nat.mul_le_mul_left _ hidx
  omega

theorem false_of_normal_odd
    {R : Subgroup (Equiv.Perm (Fin 276))} (hRP : R ≤ co3P)
    (hR : R ≠ ⊥) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hRr : ∀ x ∈ R, x ^ r = 1)
    (hTR : co3T ≤ normalizer (R : Set (Equiv.Perm (Fin 276)))) : False := by
  have hconj : ∀ t ∈ co3T, ∀ y ∈ R, t * y * t⁻¹ ∈ R := fun t ht y hy =>
    (mem_normalizer_iff.1 (hTR ht) y).1 hy
  have hconj' : ∀ t ∈ co3T, ∀ y ∈ R, t⁻¹ * y * t ∈ R := fun t ht y hy => by
    have := hconj t⁻¹ (co3T.inv_mem ht) y hy
    rwa [inv_inv] at this
  have hRM : ∀ c ∈ co3T, R ⊓ centralizer {c} ≤ co3P := fun _ _ => inf_le_left.trans hRP
  have hz : R ⊓ centralizer {co3Z} = ⊥ := by
    by_contra hne
    refine false_of_le_normalizer (Q := co3T) (L := R ⊓ centralizer {co3Z})
      (by rw [co3M_eq_centralizer]; exact le_inf co3T_le_P co3T_le_centralizer_Z) ?_
      ?_ hne hr hr2 hr3 (fun x hx => hRr x (mem_inf.1 hx).1) (dvd_of_eq card_co3T)
      (by rw [card_co3T]; norm_num)
    · rw [co3M_eq_centralizer]
      exact inf_le_inf_right _ hRP
    · intro t ht
      exact mem_normalizer_inf_centralizer (hTR ht)
        (mem_centralizer_singleton_iff.1 (co3T_le_centralizer_Z ht))
  have hinv : ∀ s ∈ co3T, s * s = 1 → R ⊓ centralizer {s} = ⊥ → ∀ y ∈ R, s * y * s⁻¹ = y⁻¹ := by
    intro s hs hss hRs y hy
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hsy : s * y * s⁻¹ ∈ R := hconj s hs y hy
    have hw : y * (s * y * s⁻¹) ∈ R ⊓ centralizer {s} := by
      refine mem_inf.2 ⟨R.mul_mem hy hsy, mem_centralizer_singleton_iff.2 ?_⟩
      calc y * (s * y * s⁻¹) * s = y * s * y := by group
        _ = s * (s * y * s⁻¹ * y) := by
          have e : s * (s * y * s⁻¹ * y) = s * s * y * s⁻¹ * y := by group
          rw [e, hss, one_mul, hs1]
        _ = s * (y * (s * y * s⁻¹)) := by rw [hRc _ hsy _ hy]
    rw [hRs, mem_bot] at hw
    exact eq_inv_of_mul_eq_one_right hw
  have he : R ⊓ centralizer {co3Ke} ≠ ⊥ := by
    intro he
    obtain ⟨⟨y, hyR⟩, hy1⟩ := ne_bot_iff_exists_ne_one.1 hR
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hzinv := hinv co3Z co3Z_mem_T co3Z_mul_self hz y hyR
    have heinv := hinv co3Ke co3Ke_mem co3Ke_mul_self he y⁻¹ (R.inv_mem hyR)
    rw [inv_inv] at heinv
    have hezy : co3Ke * co3Z * y = y * (co3Ke * co3Z) := by
      calc co3Ke * co3Z * y = co3Ke * (co3Z * y * co3Z⁻¹) * co3Z := by group
        _ = co3Ke * y⁻¹ * co3Z := by rw [hzinv]
        _ = co3Ke * y⁻¹ * co3Ke⁻¹ * (co3Ke * co3Z) := by group
        _ = y * (co3Ke * co3Z) := by rw [heinv]
    have h1 : co3Kt1 * co3Ke * co3Kt1⁻¹ = co3Ke * co3Z := by
      rw [co3Kt1_mul_e, mul_inv_cancel_right]
    have h2 : co3Ke = co3Kt1⁻¹ * (co3Ke * co3Z) * co3Kt1 := by
      rw [← h1]
      group
    have hw : co3Kt1⁻¹ * y * co3Kt1 ∈ R ⊓ centralizer {co3Ke} := by
      refine mem_inf.2 ⟨hconj' _ co3Kt1_mem y hyR, mem_centralizer_singleton_iff.2 ?_⟩
      rw [h2]
      calc co3Kt1⁻¹ * y * co3Kt1 * (co3Kt1⁻¹ * (co3Ke * co3Z) * co3Kt1)
          = co3Kt1⁻¹ * (y * (co3Ke * co3Z)) * co3Kt1 := by group
        _ = co3Kt1⁻¹ * (co3Ke * co3Z * y) * co3Kt1 := by rw [hezy]
        _ = co3Kt1⁻¹ * (co3Ke * co3Z) * co3Kt1 * (co3Kt1⁻¹ * y * co3Kt1) := by group
    rw [he, mem_bot] at hw
    apply hy1'
    calc y = co3Kt1 * (co3Kt1⁻¹ * y * co3Kt1) * co3Kt1⁻¹ := by group
      _ = 1 := by rw [hw]; group
  set c : Equiv.Perm (Fin 276) ≃* Equiv.Perm (Fin 276) := MulAut.conj co3Kg1 with hc
  have hcz : co3Kg1 * co3Ke * co3Kg1⁻¹ = co3Z := by rw [co3Kg1_mul_e, mul_inv_cancel_right]
  have hmapM : ∀ H : Subgroup (Equiv.Perm (Fin 276)), H ≤ co3P → H ≤ centralizer {co3Ke} →
      H.map c.toMonoidHom ≤ co3M := by
    intro H hHP hHe
    rintro _ ⟨y, hy, rfl⟩
    rw [co3M_eq_centralizer]
    have hye : y * co3Ke = co3Ke * y := mem_centralizer_singleton_iff.1 (hHe hy)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.2 ⟨co3P.mul_mem (co3P.mul_mem co3Kg1_mem (hHP hy)) (co3P.inv_mem co3Kg1_mem),
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hcz]
    calc co3Kg1 * y * co3Kg1⁻¹ * (co3Kg1 * co3Ke * co3Kg1⁻¹)
        = co3Kg1 * (y * co3Ke) * co3Kg1⁻¹ := by group
      _ = co3Kg1 * (co3Ke * y) * co3Kg1⁻¹ := by rw [hye]
      _ = co3Kg1 * co3Ke * co3Kg1⁻¹ * (co3Kg1 * y * co3Kg1⁻¹) := by group
  have hcinj : Function.Injective c.toMonoidHom := c.injective
  set L₁ := R ⊓ centralizer {co3Ke}
  set Q₁ := co3T ⊓ centralizer {co3Ke}
  have hQL : Q₁ ≤ normalizer (L₁ : Set (Equiv.Perm (Fin 276))) := fun t ht =>
    mem_normalizer_inf_centralizer (hTR (mem_inf.1 ht).1)
      (mem_centralizer_singleton_iff.1 (mem_inf.1 ht).2)
  refine false_of_le_normalizer (Q := Q₁.map c.toMonoidHom) (L := L₁.map c.toMonoidHom)
    (hmapM Q₁ (inf_le_left.trans co3T_le_P) inf_le_right) (hmapM L₁ (inf_le_left.trans hRP)
      inf_le_right) ?_ ?_ hr hr2 hr3 ?_ ?_ ?_
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hQL
  · rwa [Ne, map_eq_bot_iff_of_injective L₁ hcinj]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hRr y (mem_inf.1 hy).1, map_one]
  · rw [card_map_of_injective hcinj, ← card_co3T]
    exact card_dvd_of_le inf_le_left
  · rw [card_map_of_injective hcinj]
    exact le_trans (by norm_num) card_co3T_inf_centralizer_e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
