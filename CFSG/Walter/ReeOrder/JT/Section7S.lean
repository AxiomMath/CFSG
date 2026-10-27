module

public import CFSG.Walter.ReeOrder.JT.Section7R

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_six {r : ℕ} (hr : r.Prime) (h6 : r ∣ 6) : r = 2 ∨ r = 3 := by
  have := Nat.le_of_dvd (by norm_num) h6
  have := hr.two_le
  interval_cases r <;> simp_all
  all_goals exact absurd hr (by decide)

theorem eq_six_or_twelve {n : ℕ} (hπ : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = 3)
    (h6 : 6 ∣ n) (h8 : ¬ 8 ∣ n) (h9 : ¬ 9 ∣ n) : n = 6 ∨ n = 12 := by
  obtain ⟨m, rfl⟩ := h6
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h8 (dvd_zero 8)
  have h3 : ¬ 3 ∣ m := fun h3 => h9 (by
    obtain ⟨k, rfl⟩ := h3
    exact ⟨2 * k, by ring⟩)
  have h4 : ¬ 4 ∣ m := fun h4 => h8 (by
    obtain ⟨k, rfl⟩ := h4
    exact ⟨3 * k, by ring⟩)
  have hm2 : m = 2 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0
    (fun {d} hd hdm => by
      rcases hπ d hd (Dvd.dvd.mul_left hdm 6) with h2 | h3'
      · exact h2
      · exact absurd (h3' ▸ hdm) h3)
  have hv : m.primeFactorsList.length ≤ 1 := by
    by_contra hv
    exact h4 (hm2 ▸ (pow_dvd_pow 2 (by omega : 2 ≤ m.primeFactorsList.length)))
  interval_cases hk : m.primeFactorsList.length
  · left
    rw [hm2]
    norm_num
  · right
    rw [hm2]
    norm_num

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_10
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    {K : Subgroup G} (hK : IsPGroup p K) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {u : G} (hu : orderOf u = 2)
    (huK : u ∈ Subgroup.normalizer (K : Set G)) (huQ : u ∈ Subgroup.normalizer (Q : Set G)) :
    ∀ x ∈ Q, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomQ : ∀ x ∈ Q, x * u * x⁻¹ * u⁻¹ ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp huQ x⁻¹).mp (Q.inv_mem hx)
    rw [show x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) by group]
    exact Q.mul_mem hx this
  set D := omegaOne K p with hDdef
  have hDK : D ≤ K := omegaOne_le K p
  suffices hD : ∀ x ∈ Q, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.centralizer (D : Set G) by
    intro x hx
    set y := x * u * x⁻¹ * u⁻¹
    have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQK hx) huK)
        (Subgroup.inv_mem _ (hQK hx))) (Subgroup.inv_mem _ huK)
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers y)) (Nat.card K) := by
      obtain ⟨a, ha⟩ := (hQ.to_le ((Subgroup.zpowers_le).mpr (hcomQ x hx))).exists_card_eq
      obtain ⟨b, hb⟩ := hK.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega))
    have hfix : ∀ z ∈ Subgroup.zpowers y, ∀ w ∈ K, w ^ p = 1 → z * w = w * z := by
      intro z hz w hw hwp
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hwD : w ∈ D := mem_omegaOne hw hwp
      have := Subgroup.mem_centralizer_iff.mp (hD x hx) w hwD
      exact ((Commute.zpow_left (this.symm : Commute y w) k)).eq
    exact le_centralizer_of_forall_pow_eq_one hp2 hK hcop ((Subgroup.zpowers_le).mpr hyN) hfix
      (Subgroup.mem_zpowers y)
  intro x hx
  by_cases hK1 : K = ⊥
  · have hD1 : D = ⊥ := le_bot_iff.mp (hK1 ▸ hDK)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hD1, Subgroup.coe_bot, Set.mem_singleton_iff] at hz
    rw [hz, one_mul, mul_one]
  obtain ⟨P', hKP'⟩ := hK.exists_le_sylow
  obtain ⟨h4, h8, h9, hsolv, hcent⟩ := h.sylow_facts hp3 c hpq P'
  set NP := Subgroup.normalizer ((P' : Subgroup G) : Set G) with hNPdef
  set CD := Subgroup.centralizer (D : Set G) with hCDdef
  have hP'D : (P' : Subgroup G) ≤ CD := by
    intro g hg
    have hle : D ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hDdef, omegaOne, Subgroup.closure_le]
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent w (hKP' hw.1) hw.2 g hg)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hDp : IsPGroup p D := hK.to_le hDK
  have hD1 : D ≠ ⊥ := by
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hK1 (Subgroup.card_eq_one.mp hn)
    have hpK : p ∣ Nat.card K := hn ▸ dvd_pow_self p hn0
    obtain ⟨⟨w, hwK⟩, hw⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
    have hw' : orderOf w = p := by rw [← hw, Subgroup.orderOf_mk]
    intro h0
    have : w ∈ D := mem_omegaOne hwK (by rw [← hw', pow_orderOf_eq_one])
    rw [h0, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hw'
    exact hp.out.one_lt.ne hw'
  set ND := Subgroup.normalizer (D : Set G) with hNDdef
  have hNDs : Group.IsSolvable ND := h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq hDp hD1
  have hQND : Q ≤ ND := hQK.trans (normalizer_le_normalizer_omegaOne K p)
  have huND : u ∈ ND := normalizer_le_normalizer_omegaOne K p huK
  have hCDND : CD ≤ ND := Subgroup.centralizer_le_normalizer _
  set ρ := conjHom D with hρdef
  have hρ1 : ∀ n : ND, ρ n = 1 ↔ (n : G) ∈ CD := fun n => conjHom_eq_one_iff D n
  have hCDN : ∀ n : ND, (n : G) ∈ Subgroup.normalizer (CD : Set G) := by
    intro n
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro d hd
    have hd' : (n : G)⁻¹ * d * n ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) d).mp hd
      simpa using this
    have := hz _ hd'
    calc d * (n * z * (n : G)⁻¹) = n * (((n : G)⁻¹ * d * n) * z) * (n : G)⁻¹ := by group
      _ = n * (z * ((n : G)⁻¹ * d * n)) * (n : G)⁻¹ := by rw [this]
      _ = n * z * (n : G)⁻¹ * d := by group
  let S' : Sylow p CD := P'.subtype hP'D
  have hS'map : (S' : Subgroup CD).map CD.subtype = P' := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP'D]
  have hfrat : ∀ n : ND, ∃ m : ND, (m : G) ∈ NP ∧ ρ m = ρ n := by
    intro n
    obtain ⟨y, hyCD, hyn⟩ := exists_mul_mem_normalizer_of_sylow S' (hCDN n)
    rw [hS'map] at hyn
    refine ⟨⟨y, hCDND hyCD⟩ * n, hyn, ?_⟩
    rw [map_mul, (hρ1 ⟨y, hCDND hyCD⟩).mpr hyCD, one_mul]
  set x' : ND := ⟨x, hQND hx⟩
  set u' : ND := ⟨u, huND⟩
  suffices hcomm : ρ u' * ρ x' = ρ x' * ρ u' by
    have h1 : ρ (x' * u' * x'⁻¹ * u'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact (hρ1 _).mp h1
  have hsubdvd : ∀ H K : Subgroup G, Nat.card (H.subgroupOf K) ∣ Nat.card H := by
    intro H K
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  set Q₁ := (Q.subgroupOf ND).map ρ with hQ₁def
  have hQ₁p : IsPGroup 3 Q₁ := (hQ.comap_subtype (K := ND)).map ρ
  have hQ₁dvd : Nat.card Q₁ ∣ Nat.card NP := by
    have hle : Q₁ ≤ (NP.subgroupOf ND).map ρ := by
      rintro _ ⟨q, -, rfl⟩
      obtain ⟨m, hmP, hm⟩ := hfrat q
      exact ⟨m, hmP, hm⟩
    exact (Subgroup.card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans (hsubdvd _ _))
  have hρx : ρ x' ∈ Q₁ := ⟨x', hx, rfl⟩
  have hu'Q₁ : ∀ a ∈ Q₁, ρ u' * a * (ρ u')⁻¹ ∈ Q₁ := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨u' * q * u'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp huQ q).mp hq
  by_cases hρx1 : ρ x' = 1
  · rw [hρx1, mul_one, one_mul]
  set yb := ρ x' with hybdef
  have hQ₁card : Nat.card Q₁ = 3 := by
    obtain ⟨a, ha⟩ := hQ₁p.exists_card_eq
    have ha1 : a ≤ 1 := by
      by_contra ha1
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ a)).trans (ha ▸ hQ₁dvd))
    interval_cases a
    · exfalso
      rw [pow_zero] at ha
      have := (Subgroup.card_eq_one.mp ha) ▸ hρx
      exact hρx1 (Subgroup.mem_bot.mp this)
    · rw [ha, pow_one]
  have hybo : orderOf yb = 3 := by
    have hd : orderOf yb ∣ 3 := hQ₁card ▸ Subgroup.orderOf_dvd_natCard Q₁ hρx
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hρx1
    · exact h1
  have hQ₁z : Q₁ = Subgroup.zpowers yb := (Subgroup.eq_of_le_of_card_ge
    ((Subgroup.zpowers_le).mpr hρx) (by rw [Nat.card_zpowers, hybo, hQ₁card])).symm
  set ub := ρ u' with hubdef
  have hubyb : ub * yb * ub⁻¹ ∈ Subgroup.zpowers yb := hQ₁z ▸ hu'Q₁ _ hρx
  rw [mem_zpowers_iff_mem_range_orderOf, hybo] at hubyb
  simp only [Finset.mem_image, Finset.mem_range] at hubyb
  obtain ⟨k, hk3, hk⟩ := hubyb
  have hub2 : ub * ub = 1 := by
    rw [← map_mul, show u' * u' = 1 from Subtype.ext (by
      change u * u = 1
      rw [← pow_two, ← hu, pow_orderOf_eq_one]), map_one]
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    have : yb = 1 := by
      have := congrArg (fun a => ub⁻¹ * a * ub) hk
      simpa [mul_assoc] using this.symm
    exact hρx1 this
  · rw [pow_one] at hk
    calc ub * yb = ub * yb * ub⁻¹ * ub := by group
      _ = yb * ub := by rw [← hk]
  exfalso
  have hinv : ub * yb * ub⁻¹ = yb⁻¹ := by
    rw [← hk, eq_inv_iff_mul_eq_one, ← pow_succ, show 2 + 1 = orderOf yb by rw [hybo],
      pow_orderOf_eq_one]
  have hub1 : ub ≠ 1 := by
    intro h0
    rw [h0, one_mul, inv_one, mul_one] at hinv
    have : yb ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [hinv]; exact mul_inv_cancel yb
    have := orderOf_dvd_of_pow_eq_one this
    rw [hybo] at this
    omega
  have hubo : orderOf ub = 2 := orderOf_eq_prime (by rw [pow_two]; exact hub2) hub1
  set Yb := Subgroup.zpowers ub ⊔ Subgroup.zpowers yb with hYbdef
  have hYbcard : Nat.card Yb = 6 := by
    have hN : Subgroup.zpowers ub ≤ Subgroup.normalizer (Subgroup.zpowers yb : Set (MulAut D)) := by
      rw [Subgroup.zpowers_le]
      refine mem_normalizer_of_conj_mem fun a ha => ?_
      rw [← hQ₁z] at ha ⊢
      exact hu'Q₁ a ha
    have hdisj : Disjoint (Subgroup.zpowers ub) (Subgroup.zpowers yb) := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [Nat.card_zpowers, Nat.card_zpowers, hubo, hybo]
      norm_num
    rw [hYbdef, card_sup_eq_mul_of_disjoint hN hdisj, Nat.card_zpowers, Nat.card_zpowers, hubo,
      hybo]
  have hYbrange : Yb ≤ ρ.range :=
    sup_le ((Subgroup.zpowers_le).mpr ⟨u', rfl⟩) ((Subgroup.zpowers_le).mpr ⟨x', rfl⟩)
  set X : Subgroup ND := NP.subgroupOf ND ⊓ Yb.comap ρ with hXdef
  let f : X →* Yb := (ρ.comp X.subtype).codRestrict Yb (fun x => x.2.2)
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := hYbrange ha
    obtain ⟨m, hmP, hm⟩ := hfrat n
    refine ⟨⟨m, hmP, ?_⟩, Subtype.ext hm⟩
    show ρ m ∈ Yb
    rw [hm]
    exact ha
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}
  obtain ⟨Z, hZ⟩ := SolvableHall.solvable_hall_existence (inferInstance : Group.IsSolvable X) π
  have hZmap : Z.map f = ⊤ := map_eq_top_of_isHallSubgroup hf hZ (fun q hq => by
    rw [hYbcard] at hq
    rcases prime_dvd_six q.2 hq with h2 | h3
    · left; exact Subtype.ext h2
    · right; exact Subtype.ext h3)
  let ι : Z →* G := ND.subtype.comp (X.subtype.comp Z.subtype)
  have hι : Function.Injective ι :=
    ND.subtype_injective.comp (X.subtype_injective.comp Z.subtype_injective)
  have hιNP : ∀ z : Z, ι z ∈ NP := fun z => (z : X).2.1
  have hZG : Nat.card ι.range = Nat.card Z := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hι, Subgroup.card_top]
  have hZGNP : ι.range ≤ NP := by
    rintro _ ⟨z, rfl⟩
    exact hιNP z
  have hZdvd : Nat.card Z ∣ Nat.card NP := hZG ▸ Subgroup.card_dvd_of_le hZGNP
  have hZ6 : 6 ∣ Nat.card Z := by
    have := Subgroup.card_map_dvd Z f
    rwa [hZmap, Subgroup.card_top, hYbcard] at this
  have hZπ : ∀ r : ℕ, r.Prime → r ∣ Nat.card Z → r = 2 ∨ r = 3 := by
    intro r hr hrd
    rcases hZ.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  have hZ12 : Nat.card Z = 6 ∨ Nat.card Z = 12 :=
    eq_six_or_twelve hZπ hZ6 (fun h8' => h8 (h8'.trans hZdvd)) (fun h9' => h9 (h9'.trans hZdvd))
  let f' : Z →* Yb := f.comp Z.subtype
  have hf' : Function.Surjective f' := by
    intro a
    have : a ∈ Z.map f := hZmap ▸ Subgroup.mem_top a
    obtain ⟨z, hz, hza⟩ := this
    exact ⟨⟨z, hz⟩, hza⟩
  have hy3 : yb ^ 3 = 1 := by rw [← hybo, pow_orderOf_eq_one]
  set yb' : Yb := ⟨yb, Subgroup.mem_sup_right (Subgroup.mem_zpowers yb)⟩ with hyb'def
  set ub' : Yb := ⟨ub, Subgroup.mem_sup_left (Subgroup.mem_zpowers ub)⟩ with hub'def
  rcases hZ12 with hZ6' | hZ12'
  ·
    obtain ⟨e⟩ := Finite.card_eq.mp (hZ6'.trans hYbcard.symm)
    have hf'i : Function.Injective f' := (Finite.injective_iff_surjective_of_equiv e).mpr hf'
    obtain ⟨y₁, hy₁⟩ := hf' yb'
    obtain ⟨z₁, hz₁⟩ := hf' ub'
    have hrel : z₁ * y₁ * z₁⁻¹ = y₁⁻¹ := by
      apply hf'i
      rw [map_mul, map_mul, map_inv, map_inv, hy₁, hz₁]
      apply Subtype.ext
      show ub * yb * ub⁻¹ = yb⁻¹
      exact hinv
    have hy₁o : orderOf y₁ = 3 := by
      rw [← orderOf_injective f' hf'i y₁, hy₁, hyb'def, Subgroup.orderOf_mk, hybo]
    have hrelG : ι z₁ * ι y₁ * (ι z₁)⁻¹ = (ι y₁)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, hrel, map_inv]
    have hyGo : orderOf (ι y₁) = 3 := by rw [orderOf_injective ι hι y₁, hy₁o]
    exact h.ne_inv_of_mem_normalizer_sylow hp3 c hpq P' (hιNP y₁) hyGo (ι z₁) hrelG
  ·
    have h4Z : 4 ∣ Nat.card ι.range := by rw [hZG, hZ12']; norm_num
    obtain ⟨⟨V, hVn⟩, -⟩ := h.lemma_7_2 hp3 (H := ι.range)
      (fun r hr hrd => hZπ r hr (hZG ▸ hrd)) h4Z
    let e : Z ≃* ι.range := MonoidHom.ofInjective hι
    set V' : Subgroup Z := (V : Subgroup ι.range).comap e.toMonoidHom with hV'def
    have hV'n : V'.Normal := hVn.comap _
    have hV'p : IsPGroup 2 V' := V.isPGroup'.comap_of_injective _ e.injective
    have hV'card : Nat.card V' = 4 := by
      have hc : Nat.card V' = Nat.card (V : Subgroup ι.range) := by
        calc Nat.card V' = Nat.card (V'.map e.toMonoidHom) :=
              (Subgroup.card_map_of_injective e.injective).symm
          _ = Nat.card (V : Subgroup ι.range) := by
              rw [hV'def, Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
      rw [hc, V.card_eq_multiplicity, hZG, hZ12',
        factorization_two_eq_two (by norm_num) (by norm_num)]
      norm_num
    have hV'idx : V'.index = 3 := by
      have := V'.card_mul_index
      rw [hV'card, hZ12'] at this
      omega
    obtain ⟨w₀, hw₀⟩ := hf' ub'
    have hw₀3 : w₀ ^ 3 ∈ V' := by
      have : V'.Normal := hV'n
      have := Subgroup.pow_index_mem V' w₀
      rwa [hV'idx] at this
    set Vb := V'.map f' with hVbdef
    have hVbn : Vb.Normal := hV'n.map f' hf'
    have hVbp : IsPGroup 2 Vb := hV'p.map f'
    have hubinv : ub⁻¹ = ub := inv_eq_of_mul_eq_one_right hub2
    have hubV : ub' ∈ Vb := by
      refine ⟨w₀ ^ 3, hw₀3, ?_⟩
      rw [map_pow, hw₀]
      apply Subtype.ext
      show ub ^ 3 = ub
      rw [pow_succ, pow_two, hub2, one_mul]
    have h1 : yb' * ub' * yb'⁻¹ ∈ Vb := hVbn.conj_mem _ hubV yb'
    have h2 : ub' * (yb' * ub' * yb'⁻¹) ∈ Vb := Vb.mul_mem hubV h1
    have h3 : ub' * (yb' * ub' * yb'⁻¹) = yb' := by
      apply Subtype.ext
      show ub * (yb * ub * yb⁻¹) = yb
      calc ub * (yb * ub * yb⁻¹) = (ub * yb * ub⁻¹) * yb⁻¹ := by rw [hubinv]; group
        _ = yb⁻¹ * yb⁻¹ := by rw [hinv]
        _ = yb⁻¹ * yb⁻¹ * yb ^ 3 := by rw [hy3, mul_one]
        _ = yb := by group
    rw [h3] at h2
    obtain ⟨k, hk⟩ := hVbp ⟨yb', h2⟩
    have hk' : yb ^ (2 ^ k) = 1 := by
      have := congrArg (fun a : Vb => ((a : Yb) : MulAut D)) hk
      exact this
    have := orderOf_dvd_of_pow_eq_one hk'
    rw [hybo] at this
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)

end JTHyp

end CFSG.Walter.JT
