module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22V
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_isPGroup {p : ℕ} [Fact p.Prime] {H P R : Subgroup G} (hPH : P ≤ H)
    (hPp : IsPGroup p ↥P) (hPi : ¬ p ∣ P.relIndex H) (hRH : R ≤ H) (hRp : IsPGroup p ↥R) :
    ∃ g ∈ H, ∀ r ∈ R, g * r * g⁻¹ ∈ P := by
  have hP' : IsPGroup p ↥(P.subgroupOf H) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hR' : IsPGroup p ↥(R.subgroupOf H) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  have hPi' : ¬ p ∣ (P.subgroupOf H).index := hPi
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H S (hP'.toSylow hPi')
  refine ⟨g, g.2, fun r hr => ?_⟩
  have h1 : (⟨r, hRH hr⟩ : ↥H) ∈ (S : Subgroup ↥H) := hS (Subgroup.mem_subgroupOf.mpr hr)
  have h2 : MulAut.conj g (⟨r, hRH hr⟩ : ↥H) ∈ ((g • S : Sylow p ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hg, IsPGroup.toSylow_coe] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa [MulAut.conj_apply] using h3

omit [Finite G] in
theorem pow_mul_inv_mem {Q : Subgroup G} {e p : G} (he : e ∈ Q)
    (hp : p ∈ Subgroup.normalizer (Q : Set G)) : ∀ k : ℕ, (e * p) ^ k * (p ^ k)⁻¹ ∈ Q := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : (e * p) ^ (k + 1) * (p ^ (k + 1))⁻¹ =
        ((e * p) ^ k * (p ^ k)⁻¹) * (p ^ k * e * (p ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e1]
    exact Q.mul_mem ih ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hp k) e).mp he)

omit [Finite G] in
theorem mem_of_pow_two_pow_mem {R : Subgroup G} {y : G} (hy : y ^ 3 = 1) :
    ∀ k : ℕ, y ^ 2 ^ k ∈ R → y ∈ R := by
  intro k
  induction k generalizing y with
  | zero => intro h; simpa using h
  | succ k ih =>
    intro h
    have hy2 : (y ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
    have h1 : (y ^ 2) ^ 2 ^ k ∈ R := by rw [← pow_mul, ← pow_succ']; exact h
    have h2 := ih hy2 h1
    have e : y = y ^ 2 * y ^ 2 * (y ^ 3)⁻¹ := by group
    rw [e, hy, inv_one, mul_one]
    exact R.mul_mem h2 h2

theorem exists_grow {H P Q V Φ R : Subgroup G} (hPH : P ≤ H) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hPi : ¬ 3 ∣ P.relIndex H) (hQ2 : IsPGroup 2 ↥Q) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hΦP : Φ ≤ P) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ)
    (hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G))
    (hVH : V ≤ H) (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x * x = 1)
    (hinv : ∀ t ∈ V, t ∉ Q → ∃ n : G, n * t⁻¹ ∈ Q ∧ n ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x ∈ P, n * x * n⁻¹ * x ∈ Φ)
    (hRP : R ≤ P) (hΦR : Φ ≤ R) (hRne : R ≠ P) {t : G} (htV : t ∈ V) (htQ : t ∉ Q)
    (htR : t ∈ Subgroup.normalizer (R : Set G)) :
    ∃ R' : Subgroup G, R' ≤ P ∧ Φ ≤ R' ∧ Nat.card R < Nat.card R' ∧
      ∃ t' ∈ V, t' ∉ Q ∧ t' ∈ Subgroup.normalizer (R' : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 ↥P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hPQ : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyQ =>
    eq_one_of_mem_of_mem Nat.prime_three (by norm_num) hP3 hQ2 hyP hyQ
  have hconjQ : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hHQ hg) q).mp hq
  have hconjR : ∀ a ∈ P, ∀ g ∈ R, a * g * a⁻¹ ∈ R := by
    intro a ha g hg
    have e : a * g * a⁻¹ = (a * g * a⁻¹ * g⁻¹) * g := by group
    rw [e]
    exact R.mul_mem (hΦR (hcomm a ha g (hRP hg))) hg
  have hPNR : ∀ a ∈ P, a ∈ Subgroup.normalizer (R : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconjR a ha g, fun hg => ?_⟩
    have := hconjR a⁻¹ (P.inv_mem ha) _ hg
    simpa [mul_assoc] using this
  obtain ⟨x, hxP, hxR⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hRP hRne)
  obtain ⟨n, hnt, hnP, hninv⟩ := hinv t htV htQ
  obtain ⟨q₀, hq₀, rfl⟩ : ∃ q₀ ∈ Q, q₀ * n = t :=
    ⟨t * n⁻¹, by simpa using Q.inv_mem hnt, by group⟩
  set t := q₀ * n with ht
  have htH : t ∈ H := hVH htV
  have ht2 : t * t = 1 := hV2 t htV
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  set a := n * x * n⁻¹ with ha
  have haP : a ∈ P := (Subgroup.mem_normalizer_iff.mp hnP x).mp hxP
  have haΦ : a * x ∈ Φ := hninv x hxP
  set c := t * x * t⁻¹ * x⁻¹ with hc
  set p₁ := a * x⁻¹ with hp₁
  have hp₁P : p₁ ∈ P := P.mul_mem haP (P.inv_mem hxP)
  set e := q₀ * (a * q₀⁻¹ * a⁻¹) with he
  have heQ : e ∈ Q := Q.mul_mem hq₀ (hconjQ a (hPH haP) _ (Q.inv_mem hq₀))
  have hce : c = e * p₁ := by
    rw [hc, he, hp₁, ha, ht]
    group
  have hp₁R : p₁ ∉ R := by
    intro h0
    have h1 : x⁻¹ * x⁻¹ ∈ R := by
      have := R.mul_mem (R.inv_mem (hΦR haΦ)) h0
      have e2 : (a * x)⁻¹ * p₁ = x⁻¹ * x⁻¹ := by rw [hp₁]; group
      rwa [e2] at this
    have hx3 := hexp x hxP
    have e3 : x⁻¹ = (x⁻¹ * x⁻¹) * (x⁻¹ * x⁻¹) * x ^ 3 := by group
    rw [hx3, mul_one] at e3
    have h5 : x⁻¹ ∈ R := by
      rw [e3]
      exact R.mul_mem h1 h1
    exact hxR (by simpa using R.inv_mem h5)
  have hp₁N : p₁ ∈ Subgroup.normalizer (Q : Set G) := hHQ (hPH hp₁P)
  have hp₁3 : p₁ ^ 3 = 1 := hexp p₁ hp₁P
  have hc3 : c ^ 3 ∈ Q := by
    have := pow_mul_inv_mem heQ hp₁N 3
    rwa [hp₁3, inv_one, mul_one, ← hce] at this
  set N := Nat.card ↥Q with hN
  set y := c ^ N with hy
  have hy3 : y ^ 3 = 1 := by
    have h1 : (⟨c ^ 3, hc3⟩ : ↥Q) ^ N = 1 := pow_card_eq_one'
    have h2 : (c ^ 3) ^ N = 1 := by simpa using congrArg Subtype.val h1
    rw [hy, ← pow_mul, mul_comm, pow_mul, h2]
  have hyR : y ∉ R := by
    intro h0
    have h1 := pow_mul_inv_mem heQ hp₁N N
    rw [← hce, ← hy] at h1
    have h2 : y * (p₁ ^ N)⁻¹ ∈ P := P.mul_mem (hRP h0) (P.inv_mem (P.pow_mem hp₁P N))
    have h3 := hPQ _ h2 h1
    have h4 : y = p₁ ^ N := mul_inv_eq_one.mp h3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ2)
    rw [h4, hN, hk] at h0
    exact hp₁R (mem_of_pow_two_pow_mem hp₁3 k h0)
  have hy1 : y ≠ 1 := fun h0 => hyR (h0 ▸ R.one_mem)
  have hty : t * y * t⁻¹ = y⁻¹ := by
    have h1 : t * c * t⁻¹ = c⁻¹ := by
      rw [hc]
      calc t * (t * x * t⁻¹ * x⁻¹) * t⁻¹ = (t * t) * x * t⁻¹ * x⁻¹ * t⁻¹ := by group
        _ = x * t⁻¹ * x⁻¹ * t⁻¹ := by rw [ht2, one_mul]
        _ = x * t * x⁻¹ * t⁻¹ := by rw [htinv]
        _ = (t * x * t⁻¹ * x⁻¹)⁻¹ := by group
    rw [hy, ← conj_pow, h1, inv_pow]
  have hcN : c ∈ Subgroup.normalizer (R : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htR (hPNR x hxP))
      (Subgroup.inv_mem _ htR)) (Subgroup.inv_mem _ (hPNR x hxP))
  have hyN : y ∈ Subgroup.normalizer (R : Set G) := Subgroup.pow_mem _ hcN N
  have hcH : c ∈ H := by
    rw [hc]
    exact H.mul_mem (H.mul_mem (H.mul_mem htH (hPH hxP)) (H.inv_mem htH))
      (H.inv_mem (hPH hxP))
  have hyH : y ∈ H := H.pow_mem hcH N
  set R₁ := R ⊔ Subgroup.zpowers y with hR₁
  have hY3 : IsPGroup 3 ↥(Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1, pow_one]
  have hR₁3 : IsPGroup 3 ↥R₁ :=
    IsPGroup.to_sup_of_normal_left' (hP3.to_le hRP) hY3 (Subgroup.zpowers_le.mpr hyN)
  have hR₁H : R₁ ≤ H := sup_le (hRP.trans hPH) (Subgroup.zpowers_le.mpr hyH)
  have hRR₁ : R < R₁ := lt_of_le_of_ne le_sup_left fun h0 => hyR (by
    rw [h0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have htY : t ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← conj_zpow, hty]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) k
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have e5 : g = t * (t * g * t⁻¹) * t⁻¹ := by
        rw [htinv]
        calc g = (t * t) * g * (t * t) := by rw [ht2, one_mul, mul_one]
          _ = _ := by group
      rw [e5, ← hk, ← conj_zpow, hty]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) k
  have htR₁ : t ∈ Subgroup.normalizer (R₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup R (Subgroup.zpowers y) ⟨htR, htY⟩
  obtain ⟨g, hgH, hg⟩ := exists_conj_mem_of_isPGroup hPH hP3 hPi hR₁H hR₁3
  obtain ⟨q, hqQ, hqN⟩ := hfr g⁻¹ (H.inv_mem hgH)
  have hqR : ∀ r ∈ R₁, q * r * q⁻¹ ∈ P := by
    intro r hr
    have h1 := (Subgroup.mem_normalizer_iff.mp hqN _).mp (hg r hr)
    have e6 : q * g⁻¹ * (g * r * g⁻¹) * (q * g⁻¹)⁻¹ = q * r * q⁻¹ := by group
    rwa [e6] at h1
  set R' := R₁.map (MulAut.conj q).toMonoidHom with hR'
  have hmemR' : ∀ g' : G, g' ∈ R' ↔ q⁻¹ * g' * q ∈ R₁ := by
    intro g'
    rw [hR', Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨R', ?_, ?_, ?_, q * t * q⁻¹, ?_, ?_, ?_⟩
  · intro g' hg'
    have h1 := hqR _ ((hmemR' g').mp hg')
    have e7 : q * (q⁻¹ * g' * q) * q⁻¹ = g' := by group
    rwa [e7] at h1
  · intro f hf
    rw [hmemR']
    have hfR₁ : f ∈ R₁ := Subgroup.mem_sup_left (hΦR hf)
    have h1 := hqR f hfR₁
    have h2 : q * f * q⁻¹ * f⁻¹ ∈ Q := by
      have e8 : q * f * q⁻¹ * f⁻¹ = q * (f * q⁻¹ * f⁻¹) := by group
      rw [e8]
      exact Q.mul_mem hqQ (hconjQ f (hPH (hΦP hf)) _ (Q.inv_mem hqQ))
    have h3 : q * f * q⁻¹ * f⁻¹ ∈ P := P.mul_mem h1 (P.inv_mem (hΦP hf))
    have h4 : q * f * q⁻¹ = f := mul_inv_eq_one.mp (hPQ _ h3 h2)
    have e9 : q⁻¹ * f * q = f := by
      calc q⁻¹ * f * q = q⁻¹ * (q * f * q⁻¹) * q := by rw [h4]
        _ = f := by group
    rw [e9]
    exact hfR₁
  · have h1 : Nat.card R' = Nat.card R₁ :=
      Subgroup.card_map_of_injective (MulAut.conj q).injective
    rw [h1]
    exact Subgroup.card_lt_of_lt hRR₁
  · exact (Subgroup.mem_normalizer_iff.mp (hQV hqQ) t).mp htV
  · intro h0
    apply htQ
    have e10 : t = q⁻¹ * (q * t * q⁻¹) * q := by group
    rw [e10]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hqQ) h0) hqQ
  · rw [Subgroup.mem_normalizer_iff]
    intro g'
    rw [hmemR', hmemR']
    have e11 : q⁻¹ * (q * t * q⁻¹ * g' * (q * t * q⁻¹)⁻¹) * q = t * (q⁻¹ * g' * q) * t⁻¹ := by
      group
    rw [e11]
    exact Subgroup.mem_normalizer_iff.mp htR₁ _

theorem exists_mem_normalizer {H P Q V Φ : Subgroup G} (hPH : P ≤ H) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hPi : ¬ 3 ∣ P.relIndex H) (hQ2 : IsPGroup 2 ↥Q) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hΦP : Φ ≤ P) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ)
    (hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G))
    (hVH : V ≤ H) (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x * x = 1)
    (hinv : ∀ t ∈ V, t ∉ Q → ∃ n : G, n * t⁻¹ ∈ Q ∧ n ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x ∈ P, n * x * n⁻¹ * x ∈ Φ)
    (hP27 : Nat.card P = 27) (hΦ3 : Nat.card Φ = 3) {t₀ : G} (ht₀V : t₀ ∈ V) (ht₀Q : t₀ ∉ Q)
    (ht₀Φ : t₀ ∈ Subgroup.normalizer (Φ : Set G)) :
    ∃ t ∈ V, t ∉ Q ∧ t ∈ Subgroup.normalizer (P : Set G) := by
  have hΦne : Φ ≠ P := fun h0 => by rw [h0, hP27] at hΦ3; norm_num at hΦ3
  have hdvd : ∀ R ≤ P, ∃ k ≤ 3, Nat.card R = 3 ^ k := fun R hR => by
    have h1 : Nat.card R ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP27]
      exact Subgroup.card_dvd_of_le hR
    exact (Nat.dvd_prime_pow Nat.prime_three).mp h1
  obtain ⟨R₁, hR₁P, hΦR₁, hc1, t₁, ht₁V, ht₁Q, ht₁N⟩ := exists_grow hPH hexp hPi hQ2 hHQ hΦP
    hcomm hfr hVH hQV hV2 hinv hΦP le_rfl hΦne ht₀V ht₀Q ht₀Φ
  by_cases hR₁ : R₁ = P
  · subst hR₁
    exact ⟨t₁, ht₁V, ht₁Q, ht₁N⟩
  · obtain ⟨R₂, hR₂P, -, hc2, t₂, ht₂V, ht₂Q, ht₂N⟩ := exists_grow hPH hexp hPi hQ2 hHQ hΦP
      hcomm hfr hVH hQV hV2 hinv hR₁P hΦR₁ hR₁ ht₁V ht₁Q ht₁N
    have hR₂ : R₂ = P := by
      refine Subgroup.eq_of_le_of_card_ge hR₂P ?_
      have hne : Nat.card R₁ ≠ 27 := fun h0 =>
        hR₁ (Subgroup.eq_of_le_of_card_ge hR₁P (by rw [h0, hP27]))
      obtain ⟨k₁, hk₁, e₁⟩ := hdvd R₁ hR₁P
      obtain ⟨k₂, hk₂, e₂⟩ := hdvd R₂ hR₂P
      rw [hΦ3, e₁] at hc1
      rw [e₁, e₂] at hc2
      rw [e₁] at hne
      rw [hP27, e₂]
      interval_cases k₁ <;> interval_cases k₂ <;> simp_all
    subst hR₂
    exact ⟨t₂, ht₂V, ht₂Q, ht₂N⟩

omit [Finite G] in
theorem exists_mem_centralizer_of_norm {V Q : Subgroup G} {z v : G} (hz3 : z ^ 3 = 1)
    (hzV : z ∈ Subgroup.normalizer (V : Set G)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hvV : v ∈ V) (hvQ : v ∉ Q) (hv2 : v * v = 1) (hvQn : v ∈ Subgroup.normalizer (Q : Set G))
    (hzv : z * v * z⁻¹ * v⁻¹ ∈ Q) (hzv' : z⁻¹ * v * z * v⁻¹ ∈ Q) :
    ∃ w ∈ V, w ∉ Q ∧ z * w = w * z := by
  have hzz : z * z = z⁻¹ := by
    have h1 : z * z * z = 1 := by rw [← pow_three']; exact hz3
    exact eq_inv_of_mul_eq_one_left h1
  have ha : z * v * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hzV v).mp hvV
  have hb : z⁻¹ * v * z ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzV) v).mp hvV
    simpa using this
  refine ⟨v * (z * v * z⁻¹) * (z⁻¹ * v * z), V.mul_mem (V.mul_mem hvV ha) hb, ?_, ?_⟩
  · intro h0
    have h1 : v⁻¹ * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) =
        (z * v * z⁻¹ * v⁻¹) * (v * (z⁻¹ * v * z * v⁻¹) * v⁻¹) * (v * v) := by group
    rw [hv2, mul_one] at h1
    have h2 : v⁻¹ * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) ∈ Q := by
      rw [h1]
      exact Q.mul_mem hzv ((Subgroup.mem_normalizer_iff.mp hvQn _).mp hzv')
    apply hvQ
    have e : v = (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) *
        (v⁻¹ * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)))⁻¹ := by group
    rw [e]
    exact Q.mul_mem h0 (Q.inv_mem h2)
  · have h1 : z * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) * z⁻¹ =
        (z * v * z⁻¹) * ((z * z) * v * (z * z)⁻¹) * v := by group
    rw [hzz, inv_inv] at h1
    have h2 : v * (z * v * z⁻¹) * (z⁻¹ * v * z) = (z * v * z⁻¹) * (z⁻¹ * v * z) * v := by
      rw [mul_assoc]
      exact hVc v hvV _ (V.mul_mem ha hb)
    have h3 : z * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) * z⁻¹ =
        v * (z * v * z⁻¹) * (z⁻¹ * v * z) := by rw [h1, h2]
    calc z * (v * (z * v * z⁻¹) * (z⁻¹ * v * z))
        = (z * (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) * z⁻¹) * z := by group
      _ = (v * (z * v * z⁻¹) * (z⁻¹ * v * z)) * z := by rw [h3]

theorem exists_gen_of_card_three {Φ : Subgroup G} (hΦ3 : Nat.card Φ = 3) :
    ∃ z ∈ Φ, z ≠ 1 ∧ z ^ 3 = 1 ∧ Subgroup.zpowers z = Φ := by
  have hΦ1 : Φ ≠ ⊥ := fun h0 => by rw [h0, Subgroup.card_bot] at hΦ3; norm_num at hΦ3
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hΦ1
  have hz1' : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hz3 : z ^ 3 = 1 := by
    have h1 : (⟨z, hz⟩ : ↥Φ) ^ Nat.card ↥Φ = 1 := pow_card_eq_one'
    rw [hΦ3] at h1
    simpa using congrArg Subtype.val h1
  refine ⟨z, hz, hz1', hz3, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [hΦ3, Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz3) with h4 | h4
  · exact absurd (orderOf_eq_one_iff.mp h4) hz1'
  · rw [h4]

omit [Finite G] in
theorem mem_centralizer_of_gen {Φ : Subgroup G} {z w : G} (hzp : Subgroup.zpowers z = Φ)
    (hzw : z * w = w * z) : w ∈ Subgroup.centralizer (Φ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  rw [← hzp] at hf
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
  exact Commute.zpow_left hzw k

theorem exists_ne_one_fix {K : Subgroup G} {z : G} (hz3 : z ^ 3 = 1)
    (hzK : ∀ w ∈ K, z * w * z⁻¹ ∈ K) (hK : ¬ 3 ∣ Nat.card K - 1) :
    ∃ w ∈ K, w ≠ 1 ∧ z * w * z⁻¹ = w := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥K := Fintype.ofFinite _
  let σ₀ : {k : ↥K // k ≠ 1} → {k : ↥K // k ≠ 1} := fun w =>
    ⟨⟨z * ((w : ↥K) : G) * z⁻¹, hzK _ (w : ↥K).2⟩, fun h0 => w.2 (Subtype.ext (by
      have h1 : z * ((w : ↥K) : G) * z⁻¹ = 1 := congrArg Subtype.val h0
      have e : ((w : ↥K) : G) = z⁻¹ * (z * ((w : ↥K) : G) * z⁻¹) * z := by group
      rw [e, h1]
      simp))⟩
  have hσ₀ : Function.Injective σ₀ := by
    intro a b hab
    have h1 : z * ((a : ↥K) : G) * z⁻¹ = z * ((b : ↥K) : G) * z⁻¹ :=
      congrArg (fun x : {k : ↥K // k ≠ 1} => ((x : ↥K) : G)) hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  let σ : Equiv.Perm {k : ↥K // k ≠ 1} :=
    Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hσ₀)
  have hσpow : ∀ (m : ℕ) (w : {k : ↥K // k ≠ 1}),
      (((σ ^ m) w : ↥K) : G) = z ^ m * ((w : ↥K) : G) * (z ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ w)]
      show z ^ m * (z * ((w : ↥K) : G) * z⁻¹) * (z ^ m)⁻¹ = _
      rw [pow_succ]
      group
  have hσ : σ ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    rw [pow_one, hσpow, hz3]
    simp
  have hcard : ¬ 3 ∣ Fintype.card {k : ↥K // k ≠ 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨w, hw⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨((w : ↥K) : G), (w : ↥K).2, fun h0 => w.2 (Subtype.ext h0), ?_⟩
  exact congrArg (fun x : {k : ↥K // k ≠ 1} => ((x : ↥K) : G)) hw

theorem false_of_fix (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {T L V H P U I : Subgroup G}
    {h : G} {n : ℕ} (hyp : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Concl12_2_20 T L V n) (hpre : Pre12_2_21 T L V H P U I h 3) (hUO : U ≤ pCoreOf 2 H)
    (hcard : Nat.card P = 27) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hΦ3 : Nat.card ((frattini ↥P).map P.subtype) = 3)
    (hΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G))
    (hVΦ : ∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H)
    {w : G} (hw : w ∈ (V ⊓ pCoreOf 2 H) ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G)) (hw1 : w ≠ 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hPΦ, hhP, hhM, -, -, -, -, -, -, -, hidx,
    -, -⟩ := hpre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hΦP : Φ ≤ P := frattini_map_le P
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hV2m : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hV2 x hx
  obtain ⟨-, -, -, ⟨hcommV, -⟩, -⟩ := hC
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcommV.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  have hVL := le_pCoreOf_L hyp hVT hV2
  have hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G) := fun g hg =>
    exists_mul_mem_normalizer h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg
  have hinv : ∀ t ∈ V, t ∉ Q → ∃ n : G, n * t⁻¹ ∈ Q ∧ n ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ x ∈ P, n * x * n⁻¹ * x ∈ Φ := by
    intro t htV htQ
    obtain ⟨m, hmt, hmP, -, hminv⟩ := exists_inv_conj_frattini h331 hyp hHs hsol hp hp2 hPp
      hPH hPi hHPT hPΦ hVT hTV hVL hidx' hP1 htV (hV2 t htV) htQ
    exact ⟨m, hmt, hmP, hminv⟩
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Φ := fun x hx y hy =>
    commutator_mem_frattini_map Nat.prime_three hPp hx hy
  have hPQ : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyQ =>
    eq_one_of_mem_of_mem Nat.prime_three (by norm_num) hPp hO2 hyP hyQ
  obtain ⟨z, hz, -, hz3, hzp⟩ := exists_gen_of_card_three hΦ3
  obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hzv : z * v * z⁻¹ * v⁻¹ ∈ Q := by
    have := Q.inv_mem (hVΦ v hvV z hz)
    have e : (v * z * v⁻¹ * z⁻¹)⁻¹ = z * v * z⁻¹ * v⁻¹ := by group
    rwa [e] at this
  have hzv' : z⁻¹ * v * z * v⁻¹ ∈ Q := by
    have := Q.inv_mem (hVΦ v hvV z⁻¹ (Φ.inv_mem hz))
    have e : (v * z⁻¹ * v⁻¹ * z⁻¹⁻¹)⁻¹ = z⁻¹ * v * z * v⁻¹ := by group
    rwa [e] at this
  obtain ⟨t₀, ht₀V, ht₀Q, ht₀z⟩ := exists_mem_centralizer_of_norm hz3 (hΦV hz) hVc hvV hvQ
    (hV2m v hvV) (hHO (hTH (hVT hvV))) hzv hzv'
  have ht₀Φ : t₀ ∈ Subgroup.normalizer (Φ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_of_gen hzp ht₀z)
  obtain ⟨t, htV, htQ, htP⟩ := exists_mem_normalizer hPH hexp hPi hO2 hHO hΦP hcomm hfr
    (hVT.trans hTH) (hQT.trans hTV) hV2m hinv hcard hΦ3 ht₀V ht₀Q ht₀Φ
  obtain ⟨n₁, hn₁t, hn₁P, hn₁inv⟩ := hinv t htV htQ
  have htn : t * n₁⁻¹ ∈ Q := by simpa using Q.inv_mem hn₁t
  have htnP : t * n₁⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ htP (Subgroup.inv_mem _ hn₁P)
  have htinv : ∀ x ∈ P, t * x * t⁻¹ * x ∈ Φ := by
    intro x hx
    have haP : n₁ * x * n₁⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn₁P x).mp hx
    have h1 : (t * n₁⁻¹) * (n₁ * x * n₁⁻¹) * (t * n₁⁻¹)⁻¹ * (n₁ * x * n₁⁻¹)⁻¹ = 1 := by
      refine hPQ _ ?_ ?_
      · exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp htnP _).mp haP) (P.inv_mem haP)
      · have e : (t * n₁⁻¹) * (n₁ * x * n₁⁻¹) * (t * n₁⁻¹)⁻¹ * (n₁ * x * n₁⁻¹)⁻¹ =
            (t * n₁⁻¹) * ((n₁ * x * n₁⁻¹) * (t * n₁⁻¹)⁻¹ * (n₁ * x * n₁⁻¹)⁻¹) := by group
        rw [e]
        exact Q.mul_mem htn
          ((Subgroup.mem_normalizer_iff.mp (hHO (hPH haP)) _).mp (Q.inv_mem htn))
    have h2 : t * x * t⁻¹ = n₁ * x * n₁⁻¹ := by
      have e : t * x * t⁻¹ = (t * n₁⁻¹) * (n₁ * x * n₁⁻¹) * (t * n₁⁻¹)⁻¹ := by group
      rw [e]
      exact mul_inv_eq_one.mp h1
    rw [h2]
    exact hn₁inv x hx
  have hPnc : ¬ IsCyclic ↥P := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h1 : orderOf g = Nat.card ↥P := orderOf_eq_card_of_forall_mem_zpowers hg
    have h2 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [h1, hcard] at h3
    norm_num at h3
  have hcM : ∀ w' ∈ Q, w' * (t * w' * t⁻¹)⁻¹ ≠ 1 →
      Subgroup.centralizer ({w' * (t * w' * t⁻¹)⁻¹} : Set G) ≤
        Subgroup.normalizer (L : Set G) := by
    intro w' hw' hne
    refine hNE _ ?_ hne
    have e : w' * (t * w' * t⁻¹)⁻¹ = (w' * t * w'⁻¹) * t⁻¹ := by group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTV (hQT hw')) t).mp htV) (V.inv_mem htV)
  have hDP := le_centralizer_of_inv_frattini Nat.prime_three (by norm_num) hPp hPnc hPΦ hO2
    (hPH.trans hHO) htP htinv hcM
  have hwP : w ∈ Subgroup.centralizer (P : Set G) := hDP ⟨hw.1.2, hw.2⟩
  have hPM : P ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    apply hNE w hw.1.1 hw1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hwP) x hx
  have hPΦ' : P ≤ Φ := by
    intro x hx
    rw [← hPΦ]
    exact ⟨hx, hPM hx⟩
  have h1 := Subgroup.card_le_of_le hPΦ'
  rw [hcard, hΦ3] at h1
  norm_num at h1

theorem false_of_four_fpf {T L V H P U I : Subgroup G} {h : G} (hC : Concl12_2_20 T L V 4)
    (hpre : Pre12_2_21 T L V H P U I h 3) (hUO : U ≤ pCoreOf 2 H)
    (hΦ3 : Nat.card ((frattini ↥P).map P.subtype) = 3)
    (hΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G))
    (hfpf : (V ⊓ pCoreOf 2 H) ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥) : False := by
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨-, -, -, -, -, hPH, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := hpre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hΦP : Φ ≤ P := frattini_map_le P
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  have hcard8 : Nat.card ↥(V ⊓ Q) = 8 := by
    have h1 := Subgroup.relIndex_mul_card (V ⊓ Q) V
    rw [hidx', inf_right_comm, inf_idem, hC.2.1] at h1
    omega
  obtain ⟨z, hz, -, hz3, hzp⟩ := exists_gen_of_card_three hΦ3
  have hzK : ∀ w ∈ V ⊓ Q, z * w * z⁻¹ ∈ V ⊓ Q := fun w hw =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hΦV hz) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp (hHO (hPH (hΦP hz))) w).mp hw.2⟩
  obtain ⟨w, hw, hw1, hzw⟩ := exists_ne_one_fix hz3 hzK (by rw [hcard8]; norm_num)
  have hwC : w ∈ (V ⊓ Q) ⊓ Subgroup.centralizer (Φ : Set G) := by
    refine ⟨hw, mem_centralizer_of_gen hzp ?_⟩
    calc z * w = (z * w * z⁻¹) * z := by group
      _ = w * z := by rw [hzw]
  rw [hfpf, Subgroup.mem_bot] at hwC
  exact hw1 hwC

theorem lem12223ExtraN45_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) : Lem12223ExtraN45 := by
  intro G _ _ T L V H P U I h n hn hyp hNE hC hpre hUO hcard hexp hΦ3 _ hΦV hVΦ _ _
  by_cases hfpf : (V ⊓ pCoreOf 2 H) ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥
  · rcases hn with rfl | rfl
    · exact false_of_four_fpf hC hpre hUO hΦ3 hΦV hfpf
    · exact false_of_five_fpf h331 h1222 hyp hC hpre hUO hexp hΦ3 hΦV hfpf
  · obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfpf
    exact false_of_fix h331 h1222 hyp hNE hC hpre hUO hcard hexp hΦ3 hΦV hVΦ hw
      fun h0 => hw1 (Subtype.ext h0)

end Lem22

end CFSG.Quasithin.H13
