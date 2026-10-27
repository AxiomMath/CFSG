module

import CFSG.Walter.W67.W2Cor32A
import CFSG.Walter.W67.Lemma26ii
import CFSG.Walter.W67.W2Lemma26B
import CFSG.Walter.W67.Prop31
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem Frame.H_le_normalizer_F {h : Hyp G} (fr : Frame h) :
    h.H ≤ Subgroup.normalizer (h.F : Set G) :=
  fun _ hy => JT.mem_normalizer_of_conj_mem fun _ hx => fr.conj_mem_F hy hx

theorem exists_sylow_le_of_mem {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) {u : G} (huM : u ∈ M) {k : ℕ} (hu : orderOf u = p ^ k) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ M ∧ u ∈ (Q : Subgroup G) := by
  have hW : IsPGroup p (Subgroup.zpowers (⟨u, huM⟩ : M)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu])
  obtain ⟨Q₀, hQ₀⟩ := hW.exists_le_sylow
  set Q' := (Q₀ : Subgroup M).map M.subtype
  have hQ' : Nat.card Q' = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity,
      ← Sylow.card_eq_multiplicity (P.subtype hPM), Sylow.coe_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, Sylow.card_eq_multiplicity]
  refine ⟨Sylow.ofCard Q' hQ', ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _
  · rw [Sylow.coe_ofCard]
    exact ⟨⟨u, huM⟩, hQ₀ (Subgroup.mem_zpowers _), rfl⟩

theorem cor32_arith {M H L E LE CL D DH Y F e LD t j N₀ : ℕ}
    (h1 : M * LE = L * E) (h2 : H * LE = CL * E) (h3 : M * DH = D * H) (h4 : LD * Y = L * D)
    (h4' : LD * t = M) (h5 : DH = F * j) (h6 : E = e * F) (h7 : N₀ * CL = L)
    (hLE : 0 < LE) (hCL : 0 < CL) (hH : 0 < H) (hF : 0 < F) (hL : 0 < L) : N₀ ∣ Y * e := by
  have hMH : M = N₀ * H := by
    have : M * CL * LE = N₀ * H * CL * LE := by
      calc M * CL * LE = (M * LE) * CL := by ring
        _ = (N₀ * CL) * E * CL := by rw [h1, h7]
        _ = N₀ * (CL * E) * CL := by ring
        _ = N₀ * (H * LE) * CL := by rw [h2]
        _ = N₀ * H * CL * LE := by ring
    have h' := Nat.eq_of_mul_eq_mul_right hLE this
    exact Nat.eq_of_mul_eq_mul_right hCL h'
  have hD : D = N₀ * DH := by
    have : D * H = N₀ * DH * H := by rw [← h3, hMH]; ring
    exact Nat.eq_of_mul_eq_mul_right hH this
  have hEY : E * Y = t * D * LE := by
    have : L * (E * Y) = L * (t * D * LE) := by
      calc L * (E * Y) = (L * E) * Y := by ring
        _ = M * LE * Y := by rw [h1]
        _ = (LD * t) * LE * Y := by rw [h4']
        _ = t * (LD * Y) * LE := by ring
        _ = t * (L * D) * LE := by rw [h4]
        _ = L * (t * D * LE) := by ring
    exact Nat.eq_of_mul_eq_mul_left hL this
  refine ⟨j * t * LE, ?_⟩
  have : F * (Y * e) = F * (N₀ * (j * t * LE)) := by
    calc F * (Y * e) = (e * F) * Y := by ring
      _ = E * Y := by rw [h6]
      _ = t * (N₀ * (F * j)) * LE := by rw [hEY, hD, h5]
      _ = F * (N₀ * (j * t * LE)) := by ring
  exact Nat.eq_of_mul_eq_mul_left hF this

theorem ree_arith {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    let q := 3 ^ n
    let m := 3 ^ ((n + 1) / 2)
    m ^ 2 = 3 * q ∧ m ≤ q ∧ q ^ 2 - q + 1 = (q + 1 + m) * (q + 1 - m) ∧ n < q + 1 - m ∧
      Nat.Coprime 6 (q + 1 + m) ∧ Nat.Coprime 6 (q + 1 - m) ∧
      Nat.Coprime (q + 1 + m) (q + 1 - m) := by
  intro q m
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have hk2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [m, hk2]
  have hq : q = 3 * 3 ^ k * 3 ^ k := by
    simp only [q]
    rw [show 2 * k + 1 = 1 + k + k by ring, pow_add, pow_add, pow_one]
  have hm : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ]; ring
  set a := (3 : ℕ) ^ k with ha
  have ha3 : 3 ≤ a := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) hk
    simpa [a] using this
  have hka : k < a := Nat.lt_pow_self (by norm_num)
  rw [hm]
  have h1 : (3 * a) ^ 2 = 3 * q := by rw [hq]; ring
  have h2 : 3 * a ≤ q := by rw [hq]; nlinarith
  have h3 : q ^ 2 - q + 1 = (q + 1 + 3 * a) * (q + 1 - 3 * a) := by
    have hqq : q ≤ q ^ 2 := by nlinarith
    have e1 : (q + 1 + 3 * a) * (q + 1 - 3 * a) + 9 * a ^ 2 = (q + 1) ^ 2 := by
      have : 3 * a ≤ q + 1 := by omega
      zify [this]
      ring
    have e2 : 9 * a ^ 2 = 3 * q := by rw [hq]; ring
    zify [hqq] at e1 e2 ⊢
    nlinarith
  have h4 : 2 * k + 1 < q + 1 - 3 * a := by
    rw [hq]
    have : 9 * a ≤ 3 * a * a := by nlinarith
    omega
  have hodd : ∀ x, x = q + 1 + 3 * a ∨ x = q + 1 - 3 * a → Nat.Coprime 6 x := by
    intro x hx
    have hq3 : q % 3 = 0 := by rw [hq]; simp [Nat.mul_assoc, Nat.mul_mod_right]
    have ha_odd : a % 2 = 1 := by
      simp only [a]
      exact Nat.odd_iff.mp (Odd.pow (by decide))
    have hq_odd : q % 2 = 1 := by rw [hq]; simp [Nat.mul_mod, ha_odd]
    have hx2 : x % 2 = 1 := by omega
    have hx3 : x % 3 = 1 := by omega
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_left (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hx2))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  refine ⟨h1, by omega, h3, h4, hodd _ (Or.inl rfl), hodd _ (Or.inr rfl), ?_⟩
  set u := q + 1 + 3 * a
  set v := q + 1 - 3 * a
  have hu6 := hodd u (Or.inl rfl)
  have hv6 := hodd v (Or.inr rfl)
  have hd : Nat.gcd u v ∣ 2 * (3 * a) := by
    have h5 : u - v = 2 * (3 * a) := by omega
    rw [← h5]
    exact Nat.dvd_sub (Nat.gcd_dvd_left u v) (Nat.gcd_dvd_right u v)
  have hcop : Nat.Coprime (Nat.gcd u v) (2 * (3 * a)) := by
    have h23 : Nat.Coprime u (2 * (3 * a)) := by
      have h2' : Nat.Coprime u 2 := (Nat.Coprime.coprime_dvd_left (by norm_num) hu6).symm
      have h3' : Nat.Coprime u 3 := (Nat.Coprime.coprime_dvd_left (by norm_num) hu6).symm
      have h3a : Nat.Coprime u a := by
        simp only [a]
        exact Nat.Coprime.pow_right k h3'
      exact Nat.Coprime.mul_right h2' (Nat.Coprime.mul_right h3' h3a)
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left u v) h23
  exact Nat.Coprime.eq_one_of_dvd hcop hd

theorem cor_3_2 :
    ∀ (G : Type) [Group G] [Finite G] (m : MinCE G), Frame m.toHyp → 3 < m.q → commutator G = ⊤ →
      JFacts → RFacts → RMult → m.F = ⊥ := by
  intro G _ _ m fr hq hperf hJ hR hM
  by_contra hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := index_ne_two_of_perfect hperf
  obtain ⟨L, hL⟩ := lemma_2_6_ii G m fr hq hperf hJ hR hM fr.F_le_E hF
  have heF : m.eX m.F = 1 := by rw [Hyp.eX, sup_idem, Nat.div_self Nat.card_pos]
  have hKC : m.K ≤ Subgroup.centralizer (m.F : Set G) :=
    Subgroup.le_centralizer_iff.mpr (m.F_le_CK.trans inf_le_right)
  have hKF : m.KX m.F = m.K := inf_eq_left.mpr hKC
  obtain ⟨K', hJR, hK'eq⟩ := hL.jr
  rw [heF, Nat.div_one] at hJR hK'eq
  have hK' : K' = m.K := (hK'eq hq).trans hKF
  subst hK'
  have hLC : L ≤ Subgroup.centralizer (m.F : Set G) := hL.le_centralizer
  have hFCL : m.F ≤ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.mpr hLC
  obtain ⟨hLN, hLn⟩ := hL.normal
  set M := Subgroup.normalizer (m.F : Set G)
  have hNF : M = L ⊔ fr.E := hL.normalizer_eq le_rfl
  have hMNL : M ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLN hLn
  have hHM : m.H ≤ M := fr.H_le_normalizer_F
  have hEM : fr.E ≤ M := fr.E_le_H.trans hHM
  have hFM : m.F ≤ M := Subgroup.le_normalizer
  have hSM : (fr.S : Subgroup G) ≤ M := fr.S_le_H.trans hHM
  have hELN : fr.E ≤ Subgroup.normalizer (L : Set G) := hEM.trans hMNL
  obtain ⟨hL', hp, hf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup G m.p_ne_two m.f_pos hJR
  have hqL : hL'.q = m.q := by rw [JRGroup.q, hp, hf]; rfl
  have hCL : L ⊓ m.H = Subgroup.zpowers m.J ⊔ m.K := hJR.centralizer_eq
  have hCLcard : Nat.card (L ⊓ m.H : Subgroup G) = 2 * Nat.card m.K := by
    rw [hCL]
    exact m.card_zpowers_J_sup le_rfl
  have hMne : M ≠ ⊤ := by
    intro htop
    apply m.not_case2
    have hLG : L.Normal := ⟨fun x hx g =>
      (Subgroup.mem_normalizer_iff.mp (hMNL (htop ▸ Subgroup.mem_top g)) x).mp hx⟩
    have hc := card_sup_mul_card_inf_of_le_normalizer hELN
    rw [← hNF, htop, Subgroup.card_top] at hc
    have hodd : Odd L.index := by
      have h1 := L.card_mul_index
      have hpos : 0 < Nat.card L := Nat.card_pos
      have : L.index * Nat.card (L ⊓ fr.E : Subgroup G) = Nat.card fr.E := by
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [← mul_assoc, h1, hc]
      exact Odd.of_dvd_nat fr.odd_card_E (Dvd.intro _ this)
    obtain ⟨g, -, hg⟩ := fr.exists_generator_E
    refine ⟨L, hLG, hodd, ⟨g, ?_⟩, ⟨m.K, hJR.K_le, hJR.J_not_mem, hJR.centralizer_eq, hJR.iso⟩,
      m.mod_eight⟩
    rw [eq_top_iff, ← htop, hNF, ← hg]
    exact sup_le (le_sup_left.trans le_sup_right)
      (sup_le le_sup_left (hFCL.trans (le_sup_right.trans le_sup_right)))
  have hNSM : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ≤ M := by
    rw [fr.normalizer_S_eq hidx]
    exact sup_le ((fr.cover_le_centralizer fr.F_le_E).trans
      (Subgroup.centralizer_le_normalizer _)) (fr.CS_le_H.trans hHM)
  have hcent : ∀ u ∈ M, orderOf u = 2 → Subgroup.centralizer ({u} : Set G) ≤ M := by
    intro u huM hu2
    obtain ⟨Q, hQM, huQ⟩ := exists_sylow_le_of_mem fr.S hSM huM (k := 1)
      (by rw [pow_one]; exact hu2)
    obtain ⟨x, hxM, hx⟩ := exists_conj_le_of_sylow fr.S Q hSM hQM
    have hs : x * u * x⁻¹ ∈ (fr.S : Subgroup G) := hx u huQ
    have hs1 : x * u * x⁻¹ ≠ 1 := by
      intro h1
      have hu1 : u = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      rw [hu1, orderOf_one] at hu2
      omega
    obtain ⟨c, hc, hcs⟩ := fr.exists_conj_of_cover hidx hs hs1
    have hyM : c * x ∈ M := M.mul_mem (hNSM hc.1) hxM
    have hyu : c * x * u * (c * x)⁻¹ = m.J :=
      calc c * x * u * (c * x)⁻¹ = c * (x * u * x⁻¹) * c⁻¹ := by group
        _ = m.J := hcs
    intro z hz
    have hz' : c * x * z * (c * x)⁻¹ ∈ m.H := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      rw [← hyu]
      calc c * x * z * (c * x)⁻¹ * (c * x * u * (c * x)⁻¹) = c * x * (z * u) * (c * x)⁻¹ := by
            group
        _ = c * x * (u * z) * (c * x)⁻¹ := by rw [hz]
        _ = c * x * u * (c * x)⁻¹ * (c * x * z * (c * x)⁻¹) := by group
    have := M.mul_mem (M.mul_mem (M.inv_mem hyM) (hHM hz')) hyM
    simpa [mul_assoc] using this
  obtain ⟨D, hDM, hDodd, hDsupp⟩ := prop_3_1 M hMne hcent ⟨fr.S, hNSM⟩ fr.S hSM m.orderOf_J
    fr.J_mem (fun s hs => fr.comm_of_mem_S hs fr.J_mem)
  set D' := m.F ⊔ D
  have hD'M : D' ≤ M := sup_le hFM hDM
  have hD'odd : Odd (Nat.card D') := by
    have hc := card_sup_mul_card_inf_of_le_normalizer (A := m.F) (B := D) hDM
    exact Odd.of_dvd_nat (m.odd_card_F.mul hDodd) (Dvd.intro _ hc)
  have hsupp : ∀ x ∈ M, ∃ d ∈ D', ∃ c ∈ m.H, x = d * c := fun x hx => by
    obtain ⟨d, hd, c, hc, hx⟩ := hDsupp x hx
    exact ⟨d, Subgroup.mem_sup_right hd, c, hc.2, hx⟩
  set Y := L ⊓ D'
  have hYL : Y ≤ L := inf_le_left
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hD'odd (Subgroup.card_dvd_of_le inf_le_right)
  have c1 := card_sup_mul_card_inf_of_le_normalizer hELN
  rw [← hNF] at c1
  have hH : m.H = (L ⊓ m.H) ⊔ fr.E := by
    rw [hCL, sup_assoc]
    exact fr.isInternalDirectProduct_H.1.symm
  have hEN' : fr.E ≤ Subgroup.normalizer ((L ⊓ m.H : Subgroup G) : Set G) := fun e he =>
    normalizer_inf_normalizer_le L m.H ⟨hELN he, Subgroup.le_normalizer (fr.E_le_H he)⟩
  have c2 := card_sup_mul_card_inf_of_le_normalizer hEN'
  rw [← hH, inf_assoc, inf_eq_right.mpr fr.E_le_H] at c2
  have c3 := card_mul_card_inf_of_supplement hD'M hHM hsupp
  have c4 := card_sup_mul_card_inf_of_le_normalizer (hD'M.trans hMNL)
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le (sup_le hLN hD'M : L ⊔ D' ≤ M)
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le
    (le_inf le_sup_left (fr.F_le_E.trans fr.E_le_H) : m.F ≤ D' ⊓ m.H)
  set e := m.eX fr.E
  have hEe : Nat.card fr.E = e * Nat.card m.F := by
    simp only [e, Hyp.eX, sup_eq_left.mpr fr.F_le_E]
    exact (Nat.div_mul_cancel (Subgroup.card_dvd_of_le fr.F_le_E)).symm
  obtain ⟨N₀, hN₀⟩ := Subgroup.card_dvd_of_le (inf_le_left : L ⊓ m.H ≤ L)
  have key : N₀ ∣ Nat.card Y * e := cor32_arith c1 c2 c3 c4 ht.symm hj hEe
    (by rw [hN₀]; ring) Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos
  have hepos : 0 < e := by
    have := fr.odd_card_E.pos
    rw [hEe] at this
    exact Nat.pos_of_mul_pos_right this
  have hedvd : e ∣ m.f := (fr.eX_dvd_and_KX_iso le_rfl).1
  have hKcard := PSL2Sub.card_eq m.iso m.odd_p m.f_pos
  set Y' := Y.subgroupOf L
  have hY'card : Nat.card Y' = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  by_cases h5 : hL'.q = 5
  ·
    obtain ⟨hJ1, hJ2, hJ2e, -, -⟩ := hJ L hL' h5
    have hq5 : m.p ^ m.f = 5 := by rw [← Hyp.q, ← hqL, h5]
    obtain ⟨hp5, hf1⟩ := (Nat.prime_five.pow_eq_iff).mp hq5
    have he1 : e = 1 := Nat.eq_one_of_dvd_one (hf1 ▸ hedvd)
    have hLcard : Nat.card L = 175560 := by
      have := hJ1.2.1
      norm_num at this
      exact this
    rw [hp5, hf1] at hKcard
    norm_num at hKcard
    rw [hCLcard, hKcard, hLcard] at hN₀
    have hN : N₀ = 1463 := by omega
    rw [hN, he1, mul_one] at key
    exact jGroup_no_odd_subgroup hJ1 hJ2 hJ2e Y' (hY'card ▸ hYodd)
      (by rw [hY'card]; norm_num; exact key)
  ·
    obtain ⟨⟨⟨n, hn, hqn⟩, hord, -, hsolv⟩, -, -, -, -, hR6, -⟩ := hR L hL' h5
    have hq3 : 3 < hL'.q := hqL ▸ hq
    have hR6' := hR6 hq3
    have hnsolv : ¬ Group.IsSolvable L := fun hs => by
      have := (hsolv hs).1
      omega
    have hLcard := hord hnsolv
    clear hord hsolv hR6
    generalize hqq : hL'.q = qq at hqn hq3 hR6' hLcard hqL
    have hn1 : 1 < n := by
      by_contra hn1
      push Not at hn1
      interval_cases n
      · simp at hn
      · rw [hqn] at hq3
        norm_num at hq3
    obtain ⟨hm2, hmq, hfac, hlt, hc6a, hc6b, hcop⟩ := ree_arith hn hn1
    set mm := 3 ^ ((n + 1) / 2)
    rw [← hqn] at hm2 hmq hfac hlt hc6a hc6b hcop
    clear_value mm
    have hpf : m.p ^ m.f = 3 ^ n := by rw [← Hyp.q, ← hqL, hqn]
    have hp3 : m.p = 3 := by
      have h1 : m.p ∣ 3 ^ n := hpf ▸ dvd_pow_self _ m.f_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp
        ((Fact.out : m.p.Prime).dvd_of_dvd_pow h1)
    have hfn : m.f = n := by
      rw [hp3] at hpf
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpf
    have hen : e ≤ n := hfn ▸ Nat.le_of_dvd m.f_pos hedvd
    have hqm : m.q = qq := hqL.symm
    have hKcard' : 2 * Nat.card m.K = qq * (qq ^ 2 - 1) := by
      rw [hKcard, ← Hyp.q, hqm]
      have h2 : 2 ∣ qq * (qq ^ 2 - 1) := by
        have hodd : Odd qq := by rw [hqn]; exact Odd.pow (by decide)
        have : Even (qq ^ 2 - 1) := by
          rw [Nat.even_sub (Nat.one_le_pow _ _ (by omega))]
          simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hodd]
        exact (even_iff_two_dvd.mp this).mul_left _
      exact Nat.mul_div_cancel' h2
    have hN : N₀ = qq ^ 2 * (qq ^ 2 - qq + 1) := by
      rw [hCLcard, hKcard', hLcard] at hN₀
      have h0 : 0 < qq := by omega
      have hq2 : 1 < qq ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      have hpos : 0 < qq * (qq ^ 2 - 1) := Nat.mul_pos h0 (by omega)
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [← hN₀]
      have h1 : 1 ≤ qq := h0
      have h2 : 1 ≤ qq ^ 2 := hq2.le
      have h3 : qq ≤ qq ^ 2 := Nat.le_self_pow (by norm_num) qq
      clear hN₀ key
      zify [h1, h2, h3]
      ring
    rw [hN, hfac] at key
    have hprime : ∀ x : ℕ, n < x → x ∣ Nat.card Y * e → ∃ r, r.Prime ∧ r ∣ x ∧ r ∣ Nat.card Y := by
      intro x hx hxd
      have hg : Nat.gcd x (Nat.card Y) ≠ 1 := by
        intro h1
        have := Nat.Coprime.dvd_of_dvd_mul_left h1 hxd
        have := Nat.le_of_dvd hepos this
        omega
      exact ⟨(Nat.gcd x (Nat.card Y)).minFac, Nat.minFac_prime hg,
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _),
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)⟩
    obtain ⟨p₁, hp₁, hp₁C, hp₁Y⟩ := hprime (qq + 1 + mm) (by omega)
      ((dvd_mul_right _ _).trans ((dvd_mul_left _ _).trans key))
    obtain ⟨p₂, hp₂, hp₂C, hp₂Y⟩ := hprime (qq + 1 - mm) hlt
      ((dvd_mul_left _ _).trans ((dvd_mul_left _ _).trans key))
    have hR6'' := hR6' mm hm2
    choose C hC using hR6''
    have hCcard : ∀ s, Nat.card (C s) = if s then qq + 1 + mm else qq + 1 - mm :=
      fun s => (hC s).2.1
    refine no_odd_subgroup_of_hall_pair (L := L) C (fun s => (hC s).1) (fun s => ?_)
      (fun s => (hC s).2.2.1) (fun s => (hC s).2.2.2.2.1) (fun s => (hC s).2.2.2.2.2) ?_
      (fun s => ?_) Y' (hY'card ▸ hYodd) (fun s => if s then p₁ else p₂)
      (fun s => by cases s <;> simpa) (fun s => ?_) (fun s => ?_)
    · rw [hCcard]
      cases s <;> simp <;> omega
    · rw [hCcard, hCcard]
      simpa using hcop
    · rw [hCcard]
      cases s <;> simpa
    · rw [hCcard]
      cases s <;> simpa
    · rw [hY'card]
      cases s <;> simpa

end CFSG.Walter.W67
