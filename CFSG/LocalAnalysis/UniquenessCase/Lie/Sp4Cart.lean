module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4Act

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K]

open CFSG.Open Subgroup

theorem uc22pwI2_prime_dvd_prod_iff (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ S, q ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hpq]
  · intro h
    exact Finset.dvd_prod_of_mem _ h

theorem uc22pwI2_card_rootsOfUnity_le [Finite K] {p : ℕ} (hp : 0 < p) :
    Nat.card {u : Kˣ // u ^ p = 1} ≤ p := by
  classical
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hp

theorem uc22pwI2_card_le_of_exp [Finite K] {H : Type} [Group H] (φ : H →* (Fin 2 → Kˣ))
    (hφ : Function.Injective φ) {p : ℕ} (hp : 0 < p) (Q : Subgroup H) (hQ : ∀ x ∈ Q, x ^ p = 1) :
    Nat.card Q ≤ p ^ 2 := by
  let f : Q → (Fin 2 → {u : Kˣ // u ^ p = 1}) := fun x i => ⟨φ x i, by
    have h1 : φ (x : H) ^ p = 1 := by rw [← map_pow, hQ x x.2, map_one]
    simpa using congrFun h1 i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hφ
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  calc Nat.card Q ≤ Nat.card (Fin 2 → {u : Kˣ // u ^ p = 1}) := Nat.card_le_card_of_injective f hf
    _ = Nat.card {u : Kˣ // u ^ p = 1} ^ 2 := by simp [Nat.card_fun]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (uc22pwI2_card_rootsOfUnity_le hp) 2

@[expose] def uc22pwI2SylowMap {p : ℕ} {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (P : Sylow p G) :
    Sylow p G' where
  toSubgroup := P.1.map e.toMonoidHom
  isPGroup' := P.2.map e.toMonoidHom
  is_maximal' := fun {Q'} hQ' hle => by
    have hQ : IsPGroup p (Q'.comap e.toMonoidHom) :=
      hQ'.comap_of_injective e.toMonoidHom e.injective
    have hPQ : P.1 ≤ Q'.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hle
    have h1 := P.3 hQ hPQ
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q', h1]

@[expose] def uc22pwI2Ep (Y : Type) [Group Y] (E : Subgroup Y) : Prop :=
  IsMulCommutative E ∧ Odd (Nat.card E) ∧
    ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2

theorem coe_uc22pwI2SylowMap {p : ℕ} {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (P : Sylow p G) :
    (uc22pwI2SylowMap e P : Subgroup G') = (P : Subgroup G).map e.toMonoidHom := rfl

theorem uc22pwI2Ep.map {Y Z : Type} [Group Y] [Group Z] (φ : Y →* Z) (hφ : Function.Injective φ)
    {E : Subgroup Y} (h : uc22pwI2Ep Y E) : uc22pwI2Ep Z (E.map φ) := by
  obtain ⟨hc, hodd, hsyl⟩ := h
  let e : E ≃* E.map φ := E.equivMapOfInjective φ hφ
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_, fun p hp => ?_⟩
  · obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hc.is_comm.comm a' b']
  · rw [← Nat.card_congr e.toEquiv]
    exact hodd
  · obtain ⟨Q, ⟨hQc, hQe⟩, hQcard⟩ := hsyl p hp
    refine ⟨uc22pwI2SylowMap e Q, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
    · have ha : (a : E.map φ) ∈ (Q : Subgroup E).map e.toMonoidHom := a.2
      have hb : (b : E.map φ) ∈ (Q : Subgroup E).map e.toMonoidHom := b.2
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      have hab : a' * b' = b' * a' :=
        congrArg Subtype.val (hQc.is_comm.comm (⟨a', ha'⟩ : (Q : Subgroup E)) ⟨b', hb'⟩)
      apply Subtype.ext
      show (a : E.map φ) * (b : E.map φ) = (b : E.map φ) * (a : E.map φ)
      rw [← ha'', ← hb'']
      show e a' * e b' = e b' * e a'
      rw [← map_mul, ← map_mul, hab]
    · intro x hx
      have hx' : x ∈ (Q : Subgroup E).map e.toMonoidHom := hx
      obtain ⟨x', hx'', rfl⟩ := hx'
      show e x' ^ p = 1
      rw [← map_pow, hQe x' hx'', map_one]
    · rw [coe_uc22pwI2SylowMap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      exact hQcard

theorem uc22pwI2Ep_torus [Finite K] {d : ℕ} (hd : Squarefree d) (ET : Subgroup (Fin 2 → Kˣ))
    (hE : ∀ t ∈ ET, t ^ d = 1) (hodd : Odd (Nat.card ET)) : uc22pwI2Ep (Fin 2 → Kˣ) ET := by
  refine ⟨inferInstance, hodd, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let Q : Sylow p ET := default
  have hexp : ∀ x ∈ (Q : Subgroup ET), x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨x, hx⟩
    have hk' : orderOf x = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hxd : x ^ d = 1 := Subtype.ext (hE x x.2)
    have hdvd : p ^ k ∣ d := hk' ▸ orderOf_dvd_of_pow_eq_one hxd
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have hk2' : 2 ≤ k := by omega
      have h2 : p * p ∣ d := by
        rw [← pow_two]
        exact (pow_dvd_pow p hk2').trans hdvd
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hd p h2))
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    exact (pow_dvd_pow p hk1).trans (by simp)
  exact ⟨Q, ⟨inferInstance, hexp⟩,
    uc22pwI2_card_le_of_exp ET.subtype Subtype.coe_injective hp.pos _ hexp⟩

theorem uc22pwI2_dvd_card_of_mem {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {x : G} (H : Subgroup G)
    (hx : x ∈ H) (hxp : x ^ p = 1) (hx1 : x ≠ 1) : p ∣ Nat.card H := by
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : H)
  rwa [Subgroup.orderOf_mk, hord] at h

theorem uc22pwI2_exists_torus_subgroup [Finite K] {ι : Type} {n e m' : ℕ} (hm' : Odd m')
    (hn : Nat.card K = 2 ^ n) (hnem : n = 2 ^ e * m') (a : ι → Monoid.End (Fin 2 → Kˣ))
    (ha : ∀ i, ∃ m : ℕ, m' ∣ m ∧ ∀ t, a i t = ((uc22pwI2RhoE K) ^ m) t) :
    ∃ ET : Subgroup (Fin 2 → Kˣ), uc22pwI2Ep (Fin 2 → Kˣ) ET ∧
      {p | p.Prime ∧ p ∣ Nat.card ET} = {p | p.Prime ∧ p ∣ 2 ^ n - 1} ∧
      (∀ i, ∀ t ∈ ET, a i t ∈ ET) ∧
      (∀ i, ∀ t ∈ ET, (∀ p : ℕ, p.Prime → p ∣ orderOf t → p ∣ 2 ^ m' - 1) → a i t = t) := by
  classical
  obtain ⟨k, rfl⟩ := hm'
  set Q := Nat.card Kˣ with hQ
  have hQ' : Q = 2 ^ n - 1 := by rw [hQ, Nat.card_units, hn]
  have hn1 : 1 ≤ n := by
    have : 1 ≤ 2 ^ e * (2 * k + 1) := Nat.mul_pos (pow_pos (by norm_num) e) (by omega)
    omega
  have hQodd : Odd Q := by
    rw [hQ']
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hj, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    exact ⟨2 ^ j - 1, by omega⟩
  have hQ0 : Q ≠ 0 := hQodd.pos.ne'
  set M := 2 ^ (2 * k + 1) - 1 with hM
  set S : Finset ℕ := Q.primeFactors with hS
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hmemS : ∀ p, p.Prime → (p ∈ S ↔ p ∣ Q) := fun p hp => by
    simp [hS, Nat.mem_primeFactors, hp, hQ0]
  set S₁ := S.filter (· ∣ M) with hS₁
  set S₂ := S.filter (fun p => ¬ p ∣ M) with hS₂
  set d₁ := ∏ p ∈ S₁, p with hd₁
  set d₂ := ∏ p ∈ S₂, p with hd₂
  have hd12 : d₁ * d₂ = ∏ p ∈ S, p := Finset.prod_filter_mul_prod_filter_not S (· ∣ M) (fun p => p)
  have hsqf : Squarefree (d₁ * d₂) := hd12 ▸ uc22pwlie_squarefree_prod_primes S hSp
  have hd1 : ∀ p, p.Prime → (p ∣ d₁ ↔ p ∣ Q ∧ p ∣ M) := fun p hp => by
    rw [hd₁, uc22pwI2_prime_dvd_prod_iff S₁ (fun q hq => hSp q (Finset.mem_filter.1 hq).1) hp,
      hS₁, Finset.mem_filter, hmemS p hp]
  have hd2 : ∀ p, p.Prime → (p ∣ d₂ ↔ p ∣ Q ∧ ¬ p ∣ M) := fun p hp => by
    rw [hd₂, uc22pwI2_prime_dvd_prod_iff S₂ (fun q hq => hSp q (Finset.mem_filter.1 hq).1) hp,
      hS₂, Finset.mem_filter, hmemS p hp]
  have hcop : Nat.Coprime d₁ d₂ := Nat.coprime_of_dvd fun p hp h1 h2 =>
    ((hd2 p hp).1 h2).2 ((hd1 p hp).1 h1).2
  let A : Subgroup (Fin 2 → Kˣ) := (powMonoidHom d₂ : (Fin 2 → Kˣ) →* (Fin 2 → Kˣ)).ker
  let Tα : Subgroup (Fin 2 → Kˣ) := (powMonoidHom d₁ : (Fin 2 → Kˣ) →* (Fin 2 → Kˣ)).ker
  let Fix : Subgroup (Fin 2 → Kˣ) :=
    { carrier := {t | ∀ i, a i t = t}
      mul_mem' := fun {x y} hx hy i => by rw [map_mul, hx i, hy i]
      one_mem' := fun i => map_one _
      inv_mem' := fun {x} hx i => by rw [map_inv, hx i] }
  have hA : ∀ t, t ∈ A ↔ t ^ d₂ = 1 := fun t => by simp [A]
  have hTα : ∀ t, t ∈ Tα ↔ t ^ d₁ = 1 := fun t => by simp [Tα]
  have hFix : ∀ t, t ∈ Fix ↔ ∀ i, a i t = t := fun t => Iff.rfl
  have e1 : ∀ i, ∀ t ∈ A ⊔ (Tα ⊓ Fix), a i t ∈ A ⊔ (Tα ⊓ Fix) := by
    intro i t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp ht
    have hxA : a i x ∈ A := by
      rw [hA] at hx ⊢
      rw [← map_pow, hx, map_one]
    have hyFix : a i y = y := (hFix y).1 hy.2 i
    rw [map_mul, hyFix]
    exact Subgroup.mul_mem_sup hxA hy
  have e2 : ∀ i, ∀ t ∈ A ⊔ (Tα ⊓ Fix), (∀ p : ℕ, p.Prime → p ∣ orderOf t → p ∣ M) → a i t = t := by
    intro i t ht hα
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp ht
    have hxd₂ : x ^ d₂ = 1 := (hA x).1 hx
    have hyd₁ : y ^ d₁ = 1 := (hTα y).1 hy.1
    have hx1 : x ^ (d₁ * orderOf (x * y)) = 1 := by
      have hxe : x = (x * y) * y⁻¹ := by group
      calc x ^ (d₁ * orderOf (x * y)) = ((x * y) * y⁻¹) ^ (d₁ * orderOf (x * y)) := by rw [← hxe]
        _ = (x * y) ^ (d₁ * orderOf (x * y)) * (y⁻¹) ^ (d₁ * orderOf (x * y)) := mul_pow _ _ _
        _ = 1 := by
          rw [pow_mul', pow_orderOf_eq_one, one_pow, inv_pow, pow_mul, hyd₁, one_pow, inv_one, one_mul]
    have hr : Nat.Coprime (orderOf (x * y)) d₂ := Nat.coprime_of_dvd fun p hp h1 h2 =>
      ((hd2 p hp).1 h2).2 (hα p hp h1)
    have hcop2 : Nat.Coprime (d₁ * orderOf (x * y)) d₂ := Nat.Coprime.mul_left hcop hr
    have hxo : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop2 (orderOf_dvd_of_pow_eq_one hx1)
      (orderOf_dvd_of_pow_eq_one hxd₂)
    have hx_eq : x = 1 := orderOf_eq_one_iff.mp hxo
    rw [hx_eq, one_mul, (hFix y).1 hy.2 i]
  have hexp : ∀ t ∈ A ⊔ (Tα ⊓ Fix), t ^ (d₁ * d₂) = 1 := by
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp ht
    rw [mul_pow, pow_mul' x d₁ d₂, (hA x).1 hx, one_pow, pow_mul y d₁ d₂, (hTα y).1 hy.1, one_pow,
      one_mul]
  have hTcard : Nat.card (Fin 2 → Kˣ) = Q ^ 2 := by simp [Nat.card_fun, hQ]
  have hdvdQ : Nat.card ↥(A ⊔ (Tα ⊓ Fix)) ∣ Q ^ 2 :=
    hTcard ▸ Subgroup.card_subgroup_dvd_card _
  have hodd : Odd (Nat.card ↥(A ⊔ (Tα ⊓ Fix))) := (hQodd.pow (n := 2)).of_dvd_nat hdvdQ
  refine ⟨A ⊔ (Tα ⊓ Fix), uc22pwI2Ep_torus hsqf _ hexp hodd, ?_, e1, fun i t ht hα => e2 i t ht fun p hp h => ?_⟩
  · ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, hQ' ▸ hp.dvd_of_dvd_pow (hdvd.trans hdvdQ)⟩
    · rintro ⟨hp, hdvd⟩
      refine ⟨hp, ?_⟩
      rw [← hQ'] at hdvd
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
      have hbp : b ^ p = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
      have hb1 : b ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hb
        exact hp.one_lt.ne hb
      by_cases hpM : p ∣ M
      · have hbM : b ^ 2 ^ (2 * k + 1) = b := by
          have h1 : b ^ M = 1 := by
            obtain ⟨c, hc⟩ := hpM
            rw [hc, pow_mul, hbp, one_pow]
          have h2 : 2 ^ (2 * k + 1) = M + 1 := by
            rw [hM]
            have : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
            omega
          rw [h2, pow_succ, h1, one_mul]
        have hbd₁ : b ^ d₁ = 1 := by
          have : p ∣ d₁ := (hd1 p hp).2 ⟨hdvd, hpM⟩
          obtain ⟨c, hc⟩ := this
          rw [hc, pow_mul, hbp, one_pow]
        have hs : uc22pwI2Fixed K k b ∈ A ⊔ (Tα ⊓ Fix) := by
          refine Subgroup.mem_sup_right ⟨(hTα _).2 ?_, fun i => ?_⟩
          · funext j
            fin_cases j
            · show (b ^ (1 + 2 ^ k)) ^ d₁ = 1
              rw [← pow_mul, mul_comm, pow_mul, hbd₁, one_pow]
            · show (b ^ 2 ^ k) ^ d₁ = 1
              rw [← pow_mul, mul_comm, pow_mul, hbd₁, one_pow]
          · obtain ⟨m, hmdvd, hai⟩ := ha i
            rw [hai]
            exact uc22pwI2_rho_pow_fixed hmdvd hbM
        have hsp : uc22pwI2Fixed K k b ^ p = 1 := by
          funext j
          fin_cases j
          · show (b ^ (1 + 2 ^ k)) ^ p = 1
            rw [← pow_mul, mul_comm, pow_mul, hbp, one_pow]
          · show (b ^ 2 ^ k) ^ p = 1
            rw [← pow_mul, mul_comm, pow_mul, hbp, one_pow]
        have hs1 : uc22pwI2Fixed K k b ≠ 1 := by
          intro h
          have h1 : b ^ 2 ^ k = 1 := congrFun h 1
          have h2 : p ∣ 2 ^ k := hb ▸ orderOf_dvd_of_pow_eq_one h1
          have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
          have h4 : 2 ∣ Q := h3 ▸ hdvd
          exact (Nat.not_even_iff_odd.mpr hQodd) (even_iff_two_dvd.mpr h4)
        exact uc22pwI2_dvd_card_of_mem _ hs hsp hs1
      · have hbd₂ : b ^ d₂ = 1 := by
          have : p ∣ d₂ := (hd2 p hp).2 ⟨hdvd, hpM⟩
          obtain ⟨c, hc⟩ := this
          rw [hc, pow_mul, hbp, one_pow]
        have ht0 : (![b, 1] : Fin 2 → Kˣ) ∈ A ⊔ (Tα ⊓ Fix) := by
          refine Subgroup.mem_sup_left ((hA _).2 ?_)
          funext j
          fin_cases j
          · exact hbd₂
          · simp
        have ht0p : (![b, 1] : Fin 2 → Kˣ) ^ p = 1 := by
          funext j
          fin_cases j
          · exact hbp
          · simp
        have ht01 : (![b, 1] : Fin 2 → Kˣ) ≠ 1 := fun h => hb1 (congrFun h 0)
        exact uc22pwI2_dvd_card_of_mem _ ht0 ht0p ht01
  · exact hα p hp h

end CFSG.LocalAnalysis.UniquenessCase.UC22
