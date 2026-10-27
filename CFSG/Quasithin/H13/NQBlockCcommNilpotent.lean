module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem mem_zpowers_pow_of_coprime {x : H} {r k : ℕ} (hx : (orderOf x).Coprime (r ^ k)) :
    x ∈ zpowers (x ^ r ^ k) := by
  have hle : zpowers (x ^ r ^ k) ≤ zpowers x := zpowers_le.mpr (pow_mem (mem_zpowers x) _)
  have heq : zpowers (x ^ r ^ k) = zpowers x := by
    refine eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hx]
  rw [heq]
  exact mem_zpowers x

theorem eq_top_of_forall_sylow_le {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ (r : ℕ) [Fact r.Prime] (S : Sylow r G), (S : Subgroup G) ≤ K) : K = ⊤ := by
  refine eq_top_of_card_eq K (Nat.dvd_antisymm (card_subgroup_dvd_card K) ?_)
  refine (Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp fun r hr => ?_
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S⟩ : Nonempty (Sylow r G) := inferInstance
  have h1 : r ^ (Nat.card G).factorization r ∣ Nat.card K := by
    rw [← S.card_eq_multiplicity]
    exact card_dvd_of_le (hK r S)
  exact (Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').mp h1

theorem nilpotent_primewise_action_criterion (N : Subgroup H) [N.Normal]
    (hN : Group.IsNilpotent N) (hC : centralizer (N : Set H) ≤ N)
    (himg : ∀ r : ℕ, r.Prime → r ∣ Nat.card N → ∀ Q : Sylow r N, ∀ h : H, ∃ k : ℕ,
      ∀ x ∈ (Q : Subgroup N).map N.subtype, h ^ r ^ k * x * (h ^ r ^ k)⁻¹ = x) :
    Group.IsNilpotent H := by
  classical
  set Qr : ∀ r : ℕ, Sylow r N → Subgroup H := fun _ Q => (Q : Subgroup N).map N.subtype
    with hQr
  have hQnorm : ∀ (r : ℕ) [Fact r.Prime] (Q : Sylow r N), ∀ h : H, ∀ y ∈ Qr r Q,
      h * y * h⁻¹ ∈ Qr r Q := by
    intro r _ Q h y hy
    have hQn : (Q : Subgroup N).Normal := inferInstance
    have := Sylow.characteristic_of_normal Q hQn
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (Q : Subgroup N) (show h ∈ normalizer (N : Set H) by
        rw [normalizer_eq_top]; exact mem_top h)
    exact (mem_normalizer_iff.mp h1 y).mp hy
  have hQbot : ∀ (r : ℕ) [Fact r.Prime] (Q : Sylow r N), ¬ r ∣ Nat.card N → Qr r Q = ⊥ := by
    intro r _ Q hr
    have h1 : Nat.card (Q : Subgroup N) = 1 := by
      rw [Q.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hr, pow_zero]
    rw [hQr]
    simp only
    rw [(Subgroup.card_eq_one.mp h1), Subgroup.map_bot]
  have hcop : ∀ (r : ℕ) [Fact r.Prime] (Q : Sylow r N) (x : H), (orderOf x).Coprime r →
      ∀ y ∈ Qr r Q, x * y * x⁻¹ = y := by
    intro r hr Q x hx y hy
    by_cases hrN : r ∣ Nat.card N
    · obtain ⟨k, hk⟩ := himg r hr.out hrN Q x
      have hx' : x ∈ zpowers (x ^ r ^ k) :=
        mem_zpowers_pow_of_coprime (Nat.Coprime.pow_right k hx)
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hx'
      have h1 : x ^ r ^ k ∈ centralizer ({y} : Set H) := by
        rw [mem_centralizer_singleton_iff]
        have h2 := hk y hy
        calc x ^ r ^ k * y = x ^ r ^ k * y * (x ^ r ^ k)⁻¹ * x ^ r ^ k := by group
          _ = y * x ^ r ^ k := by rw [h2]
      have h2 := zpow_mem h1 m
      rw [mem_centralizer_singleton_iff, hm] at h2
      rw [h2, mul_inv_cancel_right]
    · rw [hQbot r Q hrN, mem_bot] at hy
      rw [hy, mul_one, mul_inv_cancel]
  have hcentN : ∀ x : H, (∀ (r : ℕ) [Fact r.Prime] (Q : Sylow r N), ∀ y ∈ Qr r Q,
      x * y * x⁻¹ = y) → x ∈ centralizer (N : Set H) := by
    intro x hx
    set K : Subgroup N := (centralizer ({x} : Set H)).comap N.subtype with hK
    have hKtop : K = ⊤ := eq_top_of_forall_sylow_le K fun r _ S => by
      intro n hn
      have h1 := hx r S n ⟨n, hn, rfl⟩
      show (n : H) ∈ centralizer ({x} : Set H)
      rw [mem_centralizer_singleton_iff]
      calc (n : H) * x = x * n * x⁻¹ * x := by rw [h1]
        _ = x * n := by group
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : (⟨y, hy⟩ : N) ∈ K := by rw [hKtop]; exact mem_top _
    have h2 : y ∈ centralizer ({x} : Set H) := h1
    rw [mem_centralizer_singleton_iff] at h2
    exact h2
  refine (Group.isNilpotent_of_finite_tfae.out 1 4).mpr fun p hp P => ?_
  have : Fact p.Prime := hp
  have hPord : ∀ x ∈ (P : Subgroup H), ∀ r : ℕ, r.Prime → r ≠ p → (orderOf x).Coprime r := by
    intro x hx r hr hrp
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have h1 : orderOf x ∣ p ^ k := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_left h1
      (Nat.Coprime.pow_left k ((Nat.coprime_primes hp.out hr).mpr (Ne.symm hrp)))
  by_cases hpN : p ∣ Nat.card N
  ·
    set M : Subgroup H := ⨅ (r : ℕ) (_ : Fact r.Prime) (_ : r ≠ p) (Q : Sylow r N),
      centralizer (Qr r Q : Set H) with hM
    have hmemM : ∀ x, x ∈ M ↔ ∀ (r : ℕ) [Fact r.Prime], r ≠ p → ∀ (Q : Sylow r N),
        ∀ y ∈ Qr r Q, x * y * x⁻¹ = y := by
      intro x
      simp only [hM, mem_iInf, mem_centralizer_iff]
      constructor
      · intro h r _ hrp Q y hy
        rw [← h r inferInstance hrp Q y hy, mul_inv_cancel_right]
      · intro h r _ hrp Q y hy
        have h1 := h r hrp Q y hy
        calc y * x = x * y * x⁻¹ * x := by rw [h1]
          _ = x * y := by group
    have hPM : (P : Subgroup H) ≤ M := fun x hx => (hmemM x).mpr fun r _ hrp Q y hy =>
      hcop r Q x (hPord x hx r Fact.out hrp) y hy
    have hMnorm : M.Normal := by
      refine ⟨fun x hx h => (hmemM _).mpr fun r _ hrp Q y hy => ?_⟩
      have hy' : h⁻¹ * y * h ∈ Qr r Q := by
        have := hQnorm r Q h⁻¹ y hy
        simpa using this
      have h1 := (hmemM x).mp hx r hrp Q _ hy'
      calc h * x * h⁻¹ * y * (h * x * h⁻¹)⁻¹ = h * (x * (h⁻¹ * y * h) * x⁻¹) * h⁻¹ := by group
        _ = y := by rw [h1]; group
    have hrel : ∀ (r : ℕ) [Fact r.Prime] (S : Subgroup H), S ≤ N → IsPGroup r S →
        ∃ Q : Sylow r N, S ≤ Qr r Q := by
      intro r _ S hSN hS
      have hS' : IsPGroup r (S.subgroupOf N) :=
        hS.of_equiv (subgroupOfEquivOfLe hSN).symm
      obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
      refine ⟨Q, fun x hx => ⟨⟨x, hSN hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩⟩
    let Z : Subgroup H :=
      { carrier := {z | z ∈ N ∧ z ∈ centralizer (N : Set H) ∧ (orderOf z).Coprime p}
        mul_mem' := fun {a b} ha hb => by
          obtain ⟨haN, haC, hao⟩ := ha
          obtain ⟨hbN, hbC, hbo⟩ := hb
          refine ⟨mul_mem haN hbN, mul_mem haC hbC, ?_⟩
          have hc : Commute a b := (mem_centralizer_iff.mp haC b hbN).symm
          exact (Nat.coprime_mul_iff_left.mpr ⟨hao, hbo⟩).coprime_dvd_left
            ((Commute.orderOf_mul_dvd_lcm hc).trans (Nat.lcm_dvd_mul _ _))
        one_mem' := ⟨one_mem _, one_mem _, by rw [orderOf_one]; exact Nat.coprime_one_left p⟩
        inv_mem' := fun {a} ha => by
          obtain ⟨haN, haC, hao⟩ := ha
          exact ⟨inv_mem haN, inv_mem haC, by rwa [orderOf_inv]⟩ }
    have hmemZ : ∀ z, z ∈ Z ↔ z ∈ N ∧ z ∈ centralizer (N : Set H) ∧ (orderOf z).Coprime p :=
      fun _ => Iff.rfl
    have hZM : ∀ z ∈ Z, ∀ m ∈ M, m * z = z * m := by
      intro z hz m hm
      obtain ⟨hzN, -, hzo⟩ := (hmemZ z).mp hz
      set C := (centralizer ({m} : Set H)).subgroupOf (zpowers z) with hCdef
      have hCtop : C = ⊤ := eq_top_of_forall_sylow_le C fun r _ S => by
        intro x hx
        rw [hCdef, mem_subgroupOf, mem_centralizer_singleton_iff]
        set S' := (S : Subgroup (zpowers z)).map (zpowers z).subtype with hS'
        have hS'N : S' ≤ N := (map_subtype_le _).trans (zpowers_le.mpr hzN)
        have hS'r : IsPGroup r S' := S.isPGroup'.map _
        have hxS' : (x : H) ∈ S' := ⟨x, hx, rfl⟩
        by_cases hrp : r = p
        ·
          subst hrp
          obtain ⟨k, hk⟩ := hS'r ⟨x, hxS'⟩
          have h1 : orderOf (x : H) ∣ r ^ k := by
            rw [← Subgroup.orderOf_mk (x : H) hxS']
            exact orderOf_dvd_of_pow_eq_one hk
          have h2 : orderOf (x : H) ∣ orderOf z := by
            have := Subgroup.orderOf_dvd_natCard (zpowers z) x.2
            rwa [Nat.card_zpowers] at this
          have h3 : orderOf (x : H) = 1 :=
            Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hzo |>.pow_right k) h1
          rw [orderOf_eq_one_iff.mp h3, one_mul, mul_one]
        · obtain ⟨Q, hQ⟩ := hrel r S' hS'N hS'r
          have h1 := (hmemM m).mp hm r hrp Q _ (hQ hxS')
          calc (x : H) * m = m * x * m⁻¹ * m := by rw [h1]
            _ = m * x := by group
      have hzC : (⟨z, mem_zpowers z⟩ : zpowers z) ∈ C := by rw [hCtop]; exact mem_top _
      rw [hCdef, mem_subgroupOf, mem_centralizer_singleton_iff] at hzC
      exact hzC.symm
    have hMZ : ∀ m ∈ M, ∃ j : ℕ, m ^ p ^ j ∈ Z := by
      intro m hm
      obtain ⟨Q⟩ : Nonempty (Sylow p N) := inferInstance
      obtain ⟨k, hk⟩ := himg p hp.out hpN Q m
      have hwN : m ^ p ^ k ∈ centralizer (N : Set H) := hcentN _ fun r _ Q' y hy => by
        by_cases hrp : r = p
        · subst hrp
          have : Q' = Q := by
            have := Sylow.unique_of_normal Q inferInstance
            exact Subsingleton.elim _ _
          subst this
          exact hk y hy
        · exact (hmemM _).mp (pow_mem hm _) r hrp Q' y hy
      have hwNN : m ^ p ^ k ∈ N := hC hwN
      refine ⟨k + (orderOf (m ^ p ^ k)).factorization p, ?_⟩
      rw [pow_add, pow_mul]
      refine (hmemZ _).mpr ⟨pow_mem hwNN _, pow_mem hwN _, ?_⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) (Nat.ordProj_dvd _ _)]
      exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (Nat.not_dvd_ordCompl hp.out (orderOf_pos _).ne')).symm
    have hZle : Z ≤ M := by
      intro z hz
      obtain ⟨-, hzC, -⟩ := (hmemZ z).mp hz
      refine (hmemM z).mpr fun r _ _ Q y hy => ?_
      have hyN : y ∈ N := map_subtype_le _ hy
      rw [← mem_centralizer_iff.mp hzC y hyN, mul_inv_cancel_right]
    have hZnorm : (Z.subgroupOf M).Normal := by
      refine ⟨fun z hz m => ?_⟩
      rw [mem_subgroupOf] at hz ⊢
      have h1 := hZM z hz m m.2
      simp only [coe_mul, coe_inv]
      rw [h1, mul_inv_cancel_right]
      exact hz
    have hquot : IsPGroup p (M ⧸ Z.subgroupOf M) := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨j, hj⟩ := hMZ m m.2
      refine ⟨j, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_pow]
      exact hj
    set P' : Sylow p M := P.subtype hPM with hP'
    have hsurj := QuotientGroup.mk'_surjective (Z.subgroupOf M)
    have htop := (P'.mapSurjective hsurj).is_maximal' (hquot.to_subgroup ⊤) le_top
    have hPZ : ∀ m ∈ M, ∃ x ∈ (P : Subgroup H), x⁻¹ * m ∈ Z := by
      intro m hm
      have h1 : QuotientGroup.mk' (Z.subgroupOf M) ⟨m, hm⟩ ∈
          ((P'.mapSurjective hsurj : Sylow p _) : Subgroup (M ⧸ Z.subgroupOf M)) := by
        rw [← htop]
        exact mem_top _
      rw [Sylow.coe_mapSurjective, hP', Sylow.coe_subtype] at h1
      obtain ⟨x, hx, hxm⟩ := h1
      refine ⟨x, mem_subgroupOf.mp hx, ?_⟩
      have h2 := QuotientGroup.eq.mp hxm
      rw [mem_subgroupOf] at h2
      simpa using h2
    have hMN : M ≤ normalizer ((P : Subgroup H) : Set H) := by
      intro m hm
      obtain ⟨x, hx, hxz⟩ := hPZ m hm
      have hm' : m = x * (x⁻¹ * m) := by group
      rw [mem_normalizer_iff]
      intro y
      have hzc : ∀ w, (x⁻¹ * m) * w * (x⁻¹ * m)⁻¹ = w → True := fun _ _ => trivial
      constructor
      · intro hy
        have hyM := hPM hy
        have h1 := hZM _ hxz y hyM
        have e : m * y * m⁻¹ = x * y * x⁻¹ := by
          conv_lhs => rw [hm']
          calc x * (x⁻¹ * m) * y * (x * (x⁻¹ * m))⁻¹
              = x * ((x⁻¹ * m) * y) * (x⁻¹ * m)⁻¹ * x⁻¹ := by group
            _ = x * (y * (x⁻¹ * m)) * (x⁻¹ * m)⁻¹ * x⁻¹ := by rw [← h1]
            _ = x * y * x⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem hx hy) (inv_mem hx)
      · intro hy
        have hyM : m * y * m⁻¹ ∈ M := hPM hy
        have hyM' : y ∈ M := by
          have := mul_mem (mul_mem (inv_mem hm) hyM) hm
          simpa [mul_assoc] using this
        have h1 := hZM _ hxz y hyM'
        have e : m * y * m⁻¹ = x * y * x⁻¹ := by
          conv_lhs => rw [hm']
          calc x * (x⁻¹ * m) * y * (x * (x⁻¹ * m))⁻¹
              = x * ((x⁻¹ * m) * y) * (x⁻¹ * m)⁻¹ * x⁻¹ := by group
            _ = x * (y * (x⁻¹ * m)) * (x⁻¹ * m)⁻¹ * x⁻¹ := by rw [← h1]
            _ = x * y * x⁻¹ := by group
        rw [e] at hy
        have := mul_mem (mul_mem (inv_mem hx) hy) hx
        simpa [mul_assoc] using this
    have hF := Sylow.normalizer_sup_eq_top' P hPM
    have hNtop : normalizer ((P : Subgroup H) : Set H) = ⊤ := by
      rw [eq_top_iff, ← hF]
      exact sup_le le_rfl hMN
    exact normalizer_eq_top_iff.mp hNtop
  ·
    have hPC : (P : Subgroup H) ≤ centralizer (N : Set H) := fun x hx =>
      hcentN x fun r hr Q y hy => by
        by_cases hrp : r = p
        · subst hrp
          rw [hQbot r Q hpN, mem_bot] at hy
          rw [hy, mul_one, mul_inv_cancel]
        · exact hcop r Q x (hPord x hx r hr.out hrp) y hy
    have hPN : (P : Subgroup H) ≤ N := hPC.trans hC
    have hP1 : (P : Subgroup H) = ⊥ := by
      obtain ⟨k, hk⟩ := (P.isPGroup').exists_card_eq
      rw [← card_eq_one, hk]
      rcases k with _ | k
      · rfl
      · exfalso
        apply hpN
        have h1 : Nat.card (P : Subgroup H) ∣ Nat.card N := by
          rw [← Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv]
          exact card_subgroup_dvd_card _
        rw [hk] at h1
        exact (dvd_pow_self p k.succ_ne_zero).trans h1
    rw [hP1]
    infer_instance

end CFSG.Quasithin.H13.NQBlock
