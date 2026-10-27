module

public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

theorem eq_one_of_mem_isPGroup_of_coprime [Finite G] {r : ℕ} {P K : Subgroup G}
    (hP : IsPGroup r P) (hK : Nat.Coprime r (Nat.card K)) {x : G} (hxP : x ∈ P) (hxK : x ∈ K) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hK.pow_left k) h1 h2)

theorem coprime_card_inSubgroup_pPrimeCore [Finite G] {r : ℕ} [Fact r.Prime] (H : Subgroup G) :
    Nat.Coprime r (Nat.card (CFSG.inSubgroup (CFSG.pPrimeCore r) H)) := by
  rw [CFSG.inSubgroup, card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

theorem le_normalizer_inSubgroup_pPrimeCore (r : ℕ) (H : Subgroup G) :
    H ≤ normalizer ((CFSG.inSubgroup (CFSG.pPrimeCore r) H : Subgroup G) : Set G) :=
  le_normalizer_of_forall_conj_mem fun k hk _ ⟨y, hy, hyx⟩ => hyx ▸
    ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (CFSG.pPrimeCore_normal (p := r) (G := H)).conj_mem y hy _, rfl⟩

theorem cross_prime_local_core_intersection [Finite G] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hG : CFSG.IsCharacteristicPType G r) {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian p E) (hEcard : p ^ 2 ≤ Nat.card E)
    (hrank : 2 ≤ CFSG.pRank r (centralizer (E : Set G))) :
    ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      CFSG.inSubgroup (CFSG.pPrimeCore r) (centralizer ({e} : Set G)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  set K : G → Subgroup G := fun e =>
    CFSG.inSubgroup (CFSG.pPrimeCore r) (centralizer ({e} : Set G)) with hKdef
  set X := ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1), K e with hXdef
  have hmemX : ∀ x, x ∈ X ↔ ∀ e ∈ E, e ≠ 1 → x ∈ K e := fun x => by
    simp only [hXdef, mem_iInf]
  have hKC : ∀ e, K e ≤ centralizer ({e} : Set G) := fun e => map_subtype_le _
  have hE1 : ∃ e₀ ∈ E, e₀ ≠ 1 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hEb : E = ⊥ := eq_bot_iff.mpr fun x hx => h x hx
    rw [hEb, card_bot] at hEcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨e₀, he₀, he₀1⟩ := hE1
  have hXr : ¬ r ∣ Nat.card X := by
    have hXK : X ≤ K e₀ := fun x hx => (hmemX x).mp hx e₀ he₀ he₀1
    intro hdvd
    have hcop := coprime_card_inSubgroup_pPrimeCore (r := r) (centralizer ({e₀} : Set G))
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hcop (hdvd.trans (card_dvd_of_le hXK))
  obtain ⟨V₀, hV₀, hV₀card⟩ :=
    CFSG.Quasithin.SteinbergBM.exists_card_eq_pow_pRank (X := centralizer (E : Set G)) hr.one_lt
  set V := V₀.map (centralizer (E : Set G)).subtype with hVdef
  have hVe : CFSG.IsElementaryAbelian r V := CFSG.IsElementaryAbelian.map_subtype
  have hVcard : r ^ 2 ≤ Nat.card V := by
    rw [hVdef, card_map_of_injective (centralizer (E : Set G)).subtype_injective, hV₀card]
    exact Nat.pow_le_pow_right hr.pos hrank
  have hVC : V ≤ centralizer (E : Set G) := map_subtype_le _
  have hVe' : ∀ v ∈ V, ∀ e ∈ E, v ∈ centralizer ({e} : Set G) := fun v hv e he =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hVC hv) e he).symm
  have hVX : V ≤ normalizer (X : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun v hv x hx => ?_
    rw [hmemX] at hx ⊢
    intro e he he1
    exact (mem_normalizer_iff.mp (le_normalizer_inSubgroup_pPrimeCore r _ (hVe' v hv e he))
      x).mp (hx e he he1)
  by_contra hX
  obtain ⟨v, hv, hv1, hY⟩ : ∃ v ∈ V, v ≠ 1 ∧ X ⊓ centralizer ({v} : Set G) ≠ ⊥ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hX (le_bot_iff.mp (le_of_forall_inf_centralizer_le hVe hVcard hXr hVX
      fun v hv hv1 => (hcon v hv hv1).le))
  set Y := X ⊓ centralizer ({v} : Set G) with hYdef
  have hvr : v ^ r = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) v hv
  have hZ : IsPGroup r (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hvr hv1, pow_one])
  have hZ1 : zpowers v ≠ ⊥ := fun h => hv1 (zpowers_eq_bot.mp h)
  set N := normalizer ((zpowers v : Subgroup G) : Set G) with hNdef
  set R := CFSG.inSubgroup (CFSG.pCore r) N with hRdef
  have hR : IsPGroup r R := (CFSG.pCore_isPGroup (p := r) (G := N)).map N.subtype
  have hcent_le_N : centralizer ({v} : Set G) ≤ N := by
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hcv : c * v = v * c := mem_centralizer_singleton_iff.mp hc
    have hcvk : c * v ^ k * c⁻¹ = v ^ k := by
      rw [(Commute.zpow_right hcv k).eq, mul_inv_cancel_right]
    rw [hcvk]
    exact zpow_mem (mem_zpowers v) k
  have hEN : E ≤ N := fun e he =>
    hcent_le_N (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hVC hv) e he))
  have hYN : Y ≤ N := inf_le_right.trans hcent_le_N
  have hNR : N ≤ normalizer (R : Set G) := le_normalizer_inSubgroup_pCore r N
  have hpR : ¬ p ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    rw [hk]
    intro h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h))
  have hRY : R ≤ centralizer (Y : Set G) := by
    refine le_of_forall_inf_centralizer_le hE hEcard hpR (hEN.trans hNR) fun e he he1 => ?_
    intro c ⟨hcR, hce⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hyK : y ∈ K e := (hmemX y).mp hy.1 e he he1
    have h1 : c * y * c⁻¹ * y⁻¹ ∈ K e :=
      (K e).mul_mem ((mem_normalizer_iff.mp (le_normalizer_inSubgroup_pPrimeCore r _ hce)
        y).mp hyK) ((K e).inv_mem hyK)
    have h2 : c * y * c⁻¹ * y⁻¹ ∈ R := by
      have : y * c⁻¹ * y⁻¹ ∈ R := (mem_normalizer_iff.mp (hNR (hYN hy)) c⁻¹).mp (R.inv_mem hcR)
      have h3 : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
      rw [h3]
      exact R.mul_mem hcR this
    have h4 := eq_one_of_mem_isPGroup_of_coprime hR
      (coprime_card_inSubgroup_pPrimeCore (r := r) (centralizer ({e} : Set G))) h2 h1
    calc y * c = c * y * c⁻¹ * y⁻¹ * (y * c) := by rw [h4, one_mul]
      _ = c * y := by group
  apply hY
  rw [eq_bot_iff]
  intro y hy
  have hyR : y ∈ R := mem_inSubgroup_pCore_of_isCharacteristicPType hG hZ hZ1 (hYN hy)
    fun s hs => (mem_centralizer_iff.mp (hRY hs) y hy).symm
  have hcopX : Nat.Coprime r (Nat.card X) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hXr
  exact mem_bot.mpr (eq_one_of_mem_isPGroup_of_coprime hR hcopX hyR hy.1)

end CFSG.RankThree.GroupTheory.SteinbergBM
