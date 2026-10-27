module

public import CFSG.Walter.ReeOrder.JT.Section7W
public import CFSG.Walter.ReeOrder.JT.Section7D

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

@[expose] def PiCyclic (h : JTHyp G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ (h.q - 1) / 2 → ∀ P : Subgroup G, IsPGroup p P → IsCyclic P

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem factorization_card_eq_of_piCyclic
    (c : TorusConf h) (hπ : PiCyclic h) {p : ℕ}
    [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2) :
    (Nat.card G).factorization p = ((h.q - 1) / 2).factorization p := by
  obtain ⟨P₀, hCpP₀, hT₀P₀⟩ := h.exists_sylow_invariant hp3 c hpq
  have hcyc := hπ p hp.out hpq P₀ P₀.isPGroup'
  have heq : c.Cp p = P₀ := by
    by_contra hne
    exact h.not_isCyclic_of_ne hp3 c hpq P₀ hCpP₀ hT₀P₀ hne hcyc
  have h1 := P₀.card_eq_multiplicity
  rw [← heq, c.card_Cp] at h1
  have hC : Nat.card c.C = (h.q - 1) / 2 := by
    have := c.card_C
    omega
  rw [← hC]
  exact (Nat.pow_right_injective hp.out.two_le h1).symm

theorem prime_dvd_cases
    (s : Setup h) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ h.q * (h.q ^ 2 - 1)) :
    r = 3 ∨ r ∣ Nat.card s.Q ∨ r ∣ (h.q - 1) / 2 := by
  have hp := h.p_ne_two_of_eq_three hp3
  have h4 := s.four_mul_card_Q hp
  rw [h.eps_eq_one_of_eq_three hp3] at h4
  have h4' : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hsq : h.q ^ 2 - 1 = (h.q + 1) * (2 * ((h.q - 1) / 2)) := by
    have h1 : 2 * ((h.q - 1) / 2) = h.q - 1 := by omega
    rw [h1]
    have : 1 ≤ h.q := by omega
    zify [this, Nat.one_le_pow 2 h.q (by omega)]
    ring
  rw [hsq] at hrq
  have hr2' : ¬ r ∣ 2 := fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd)
  rcases (Nat.Prime.dvd_mul hr).mp hrq with h1 | h1
  · left
    rw [JTHyp.q_eq, hp3] at h1
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h1)
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · right; left
      rw [← h4'] at h2
      rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · exact absurd (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h3)) hr2'
      · exact h3
    · right; right
      rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · exact absurd h3 hr2'
      · exact h3

theorem lemma_7_16_of_piCyclic
    (hπ : PiCyclic h) : Lemma716 h := by
  classical
  intro C hCF hC hCcard x hxC hx1
  have hp := h.p_ne_two_of_eq_three hp3
  have hS := CFSG.Walter.suzukiFourGroupTheorem
  have h712 := h.lemma_7_12_a hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hU⟩ := exists_torusData_of_isCyclic h.F h.iso hp h.five_lt
    (by rw [← JTHyp.q_eq]; omega) hCF hC hCcard
  let c : TorusConf h := ⟨C, w, hU, hCcard⟩
  have hxF : x ∈ h.F := hCF hxC
  have hwF : w ∈ h.F := hU.w_mem
  have hwx : w * x * w⁻¹ = x⁻¹ := hU.inv x hxC
  have hCodd : Odd (Nat.card C) := Nat.odd_iff.mpr (by omega)
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard C hxC)
  have hxinv : x⁻¹ ≠ x := by
    intro h0
    apply hx1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; nth_rewrite 1 [← h0]; exact inv_mul_cancel x)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)
  have htw : Commute h.t w := (h.commute_of_mem_F hwF).symm
  have htne : h.t ≠ w := fun h0 => h.t_not_mem (h0 ▸ hwF)
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ C.one_mem)
  have hwo : orderOf w = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self) hw1
  have htwo : orderOf (h.t * w) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc h.t * w * (h.t * w) = (h.t * h.t) * (w * w) := by
            rw [mul_assoc, ← mul_assoc w h.t w, ← htw.eq]; group
        _ = 1 := by rw [h.t_mul_t, hU.w_mul_self, one_mul]
    · intro h0
      apply htne
      calc h.t = h.t * (h.t * w) := by rw [h0, mul_one]
        _ = w := by rw [← mul_assoc, h.t_mul_t, one_mul]
  set Cx := Subgroup.centralizer ({x} : Set G) with hCxdef
  have htCx : h.t ∈ Cx :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem_F hxF).symm
  have hCCx : C ≤ Cx := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hC
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := C)).mul_comm ⟨y, hy⟩ ⟨x, hxC⟩)
  set N₀ := Subgroup.normalizer (Subgroup.zpowers x : Set G) with hN₀def
  obtain ⟨M, hMn, hModd, hMcard⟩ :=
    h.exists_normal_odd_normalizer_of_mem_torus hp3 hCF hC hCcard hxC hx1
  have hCxN : Cx ≤ N₀ := fun y hy =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have htN : h.t ∈ N₀ := hCxN htCx
  have hwN : w ∈ N₀ := by
    refine (conj_smul_eq_iff (K := Subgroup.zpowers x)).mp ?_
    change (Subgroup.zpowers x).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers x
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (w * x * w⁻¹) = Subgroup.zpowers x
    rw [hwx, Subgroup.zpowers_inv]
  have hwCx : w ∉ Cx := by
    intro hw
    have h1 : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    apply hxinv
    rw [← hwx, h1, mul_inv_cancel_right]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hU.w_mul_self
  have hwnCx : w ∈ Subgroup.normalizer (Cx : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have hx' : w⁻¹ * x * w = x⁻¹ := by rw [hwinv]; nth_rewrite 2 [← hwinv]; exact hwx
    have hyc : Commute y x := hy
    have hyx' : y * x⁻¹ = x⁻¹ * y := hyc.inv_right.eq
    calc w * y * w⁻¹ * x = w * y * (w⁻¹ * x * w) * w⁻¹ := by group
      _ = w * (y * x⁻¹) * w⁻¹ := by rw [hx']; group
      _ = w * (x⁻¹ * y) * w⁻¹ := by rw [hyx']
      _ = w * (w⁻¹ * x * w) * y * w⁻¹ := by rw [hx']; group
      _ = x * (w * y * w⁻¹) := by group
  have hA : ¬ 4 ∣ Nat.card Cx := by
    intro h4
    have hdisj : Disjoint (Subgroup.zpowers w) Cx := by
      rw [Subgroup.disjoint_def]
      intro y hyw hyC
      rcases (mem_zpowers_of_orderOf_eq_two hwo).mp hyw with rfl | rfl
      · rfl
      · exact absurd hyC hwCx
    have hcard := card_sup_eq_mul_of_disjoint ((Subgroup.zpowers_le).mpr hwnCx) hdisj
    rw [Nat.card_zpowers, hwo] at hcard
    have hle : Subgroup.zpowers w ⊔ Cx ≤ N₀ := sup_le ((Subgroup.zpowers_le).mpr hwN) hCxN
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, hMcard] at hdvd
    obtain ⟨k, hk⟩ := h4
    rw [hk] at hdvd
    have h2 : 2 ∣ Nat.card M := by
      have h8 : 4 * (2 * k) ∣ 4 * Nat.card M := by
        have : 2 * (4 * k) = 4 * (2 * k) := by ring
        rwa [this] at hdvd
      exact (dvd_mul_right 2 k).trans ((Nat.mul_dvd_mul_iff_left (by norm_num)).mp h8)
    exact (Nat.not_even_iff_odd.mpr hModd) (even_iff_two_dvd.mpr h2)
  have hB : ∀ r : ℕ, r.Prime → r ∣ Nat.card Cx → r ≠ 2 → r ∣ h.q * (h.q ^ 2 - 1) := by
    intro r hr hrC hr2
    have hrN : r ∣ Nat.card N₀ := hrC.trans (Subgroup.card_dvd_of_le hCxN)
    rw [hMcard] at hrN
    have hrM : r ∣ Nat.card M := by
      rcases (Nat.Prime.dvd_mul hr).mp hrN with h4 | h4
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h4))) hr2
      · exact h4
    set M' := M.map N₀.subtype with hM'def
    have hM'card : Nat.card M' = Nat.card M := Subgroup.card_map_of_injective N₀.subtype_injective
    have hM'n : ∀ g ∈ N₀, g ∈ Subgroup.normalizer (M' : Set G) := by
      intro g hg
      have hmem : (⟨g, hg⟩ : N₀) ∈ Subgroup.normalizer (M : Set N₀) := by
        have := hMn
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      exact Subgroup.le_normalizer_map N₀.subtype ⟨⟨g, hg⟩, hmem, rfl⟩
    have hBW := card_mul_card_sq_eq_mul h.t_mul_t hU.w_mul_self h.t_ne_one hw1 htne htw M'
      (hM'n _ htN) (hM'n _ hwN) (hM'card ▸ hModd)
    have hrl : r ∣ Nat.card M' * Nat.card (M' ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓
        Subgroup.centralizer ({w} : Set G) : Subgroup G) ^ 2 :=
      Dvd.dvd.mul_right (hM'card ▸ hrM) _
    rw [hBW] at hrl
    have hfac : ∀ v : G, orderOf v = 2 →
        r ∣ Nat.card (M' ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) →
          r ∣ h.q * (h.q ^ 2 - 1) := by
      intro v hv hrv
      rw [← h.card_centralizer_of_orderOf_eq_two hp hv]
      exact hrv.trans (Subgroup.card_dvd_of_le inf_le_right)
    rcases (Nat.Prime.dvd_mul hr).mp hrl with h12 | h3
    · rcases (Nat.Prime.dvd_mul hr).mp h12 with h1 | h2
      · exact hfac _ h.orderOf_t h1
      · exact hfac _ hwo h2
    · exact hfac _ htwo h3
  obtain ⟨s, -⟩ := h.exists_setup_card_normalizer hp c.isKleinFour_T₀
  have h4Q := s.four_mul_card_Q hp
  rw [h.eps_eq_one_of_eq_three hp3] at h4Q
  have h4Q' : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4Q
  have hσ : ∀ r : ℕ, r.Prime → r ∣ Nat.card s.Q → ¬ r ∣ Nat.card Cx := by
    intro r hr hrQ hrC
    have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr (s.odd_card_Q hp)) (even_iff_two_dvd.mpr hrQ)
    have hr3 : r ≠ 3 := by
      rintro rfl
      exact s.three_not_dvd_card_Q hp3 hrQ
    have hr6 : Nat.Coprime r 6 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
        ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
    obtain ⟨⟨y, hyC⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := Cx) r hrC
    have hyo : orderOf y = r := by rw [← hy, Subgroup.orderOf_mk]
    obtain ⟨⟨z, hzQ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := s.Q) r hrQ
    have hzo : orderOf z = r := by rw [← hz, Subgroup.orderOf_mk]
    have hz1 : z ≠ 1 := by
      intro h0
      rw [h0, orderOf_one] at hzo
      exact hr.one_lt.ne hzo
    have hyr : IsPGroup r (Subgroup.zpowers y) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hyo, pow_one] :
        Nat.card (Subgroup.zpowers y) = r ^ 1)
    have hzr : IsPGroup r (Subgroup.zpowers z) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hzo, pow_one] :
        Nat.card (Subgroup.zpowers z) = r ^ 1)
    obtain ⟨Ry, hRy⟩ := hyr.exists_le_sylow
    obtain ⟨Rz, hRz⟩ := hzr.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Ry Rz
    have hRzQ : (Rz : Subgroup G) ≤ s.Q :=
      s.le_Q_of_isPGroup hp3 hS hr6 Rz.isPGroup' hzQ hz1 (hRz (Subgroup.mem_zpowers z))
    have hgy : g * y * g⁻¹ ∈ s.Q := by
      apply hRzQ
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨y, hRy (Subgroup.mem_zpowers y), rfl⟩
    have hy1 : y ≠ 1 := by
      intro h0
      rw [h0, orderOf_one] at hyo
      exact hr.one_lt.ne hyo
    have hgy1 : g * y * g⁻¹ ≠ 1 := by
      intro h0
      apply hy1
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hgxy : g * x * g⁻¹ ∈ Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        _ = g * (y * x) * g⁻¹ := by rw [hyx]
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
    have hgxt := h.lemma_7_12_b_of_lemma712a hp3 hS h712 s hgy hgy1 hgxy
    have hgxo : orderOf (g * x * g⁻¹) = orderOf x := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hgxF : g * x * g⁻¹ ∈ h.F := h.mem_F_of_odd hgxt (hgxo ▸ hxodd)
    set d := s.data hp
    have hgyU : g * y * g⁻¹ ∈ d.U := s.Q_le_U hp hgy
    have hR : Subgroup.zpowers (g * y * g⁻¹) ≤ d.U := (Subgroup.zpowers_le).mpr hgyU
    have hR1 : Subgroup.zpowers (g * y * g⁻¹) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hgy1
    have hgxN : g * x * g⁻¹ ∈ h.F ⊓ Subgroup.normalizer
        ((Subgroup.zpowers (g * y * g⁻¹) : Subgroup G) : Set G) :=
      ⟨hgxF, mem_normalizer_zpowers_of_commute
        (Subgroup.mem_centralizer_singleton_iff.mp hgxy)⟩
    rw [d.torus.normalizer _ hR hR1] at hgxN
    have hgxU : g * x * g⁻¹ ∈ d.U := by
      rcases d.torus.conj_eq hgxN hgyU with ⟨h1, -⟩ | ⟨-, hinv⟩
      · exact h1
      · exfalso
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgxy, mul_inv_cancel_right] at hinv
        have hyodd : Odd (orderOf (g * y * g⁻¹)) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
          exact hr.odd_of_ne_two hr2
        have h2 : orderOf (g * y * g⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
          rw [pow_two]
          nth_rewrite 2 [hinv]
          exact mul_inv_cancel _)
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
        · exact hgy1 (orderOf_eq_one_iff.mp h1)
        · rw [h1] at hyodd
          exact absurd hyodd (by decide)
    have h1 : orderOf x ∣ 2 * Nat.card s.Q := by
      rw [← hgxo, ← s.card_U_eq hp]
      exact Subgroup.orderOf_dvd_natCard _ hgxU
    have h2 : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hxC
    have h5 : 2 * Nat.card s.Q = Nat.card C + 1 := by omega
    rw [h5] at h1
    have := (Nat.dvd_add_right h2).mp h1
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
  have hπC : ∀ r : ℕ, r.Prime → r ∣ Nat.card Cx → r ≠ 2 → r ∣ (h.q - 1) / 2 := by
    intro r hr hrC hr2
    rcases h.prime_dvd_cases hp3 s hr hr2 (hB r hr hrC hr2) with h3 | hQ | hπr
    · subst h3
      exact absurd hrC (h.lemma_7_4 hp3 hCF hC hCcard hxC hx1)
    · exact absurd hrC (hσ r hr hQ)
    · exact hπr
  have hCq : Nat.card C = (h.q - 1) / 2 := by omega
  have h2C : 2 * Nat.card C ≠ 0 := (Nat.mul_pos two_pos Nat.card_pos).ne'
  have hdvd : Nat.card Cx ∣ 2 * Nat.card C := by
    refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' h2C).mp ?_
    rw [Finsupp.le_def]
    intro r
    by_cases hr : r.Prime
    · by_cases hrC : r ∣ Nat.card Cx
      · by_cases hr2 : r = 2
        · subst hr2
          have h1 : (Nat.card Cx).factorization 2 ≤ 1 := by
            by_contra h1
            apply hA
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
              Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne']
            omega
          have h2 : 1 ≤ (2 * Nat.card C).factorization 2 :=
            (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two h2C).mp
              (dvd_mul_right 2 _)
          omega
        · have : Fact r.Prime := ⟨hr⟩
          have hrπ := hπC r hr hrC hr2
          have h1 := h.factorization_card_eq_of_piCyclic hp3 c hπ hrπ
          calc (Nat.card Cx).factorization r ≤ (Nat.card G).factorization r :=
                (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
                  (Subgroup.card_subgroup_dvd_card _) r
            _ = (Nat.card C).factorization r := by rw [h1, hCq]
            _ ≤ (2 * Nat.card C).factorization r :=
                (Nat.factorization_le_iff_dvd Nat.card_pos.ne' h2C).mpr
                  (dvd_mul_left _ _) r
      · rw [Nat.factorization_eq_zero_of_not_dvd hrC]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hr]
      exact Nat.zero_le _
  have htC : Subgroup.zpowers h.t ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [← h.commute_of_mem_F (hCF hy), mul_inv_cancel_right]
    exact hy
  have hdisj : Disjoint (Subgroup.zpowers h.t) C := by
    rw [Subgroup.disjoint_def]
    intro y hyt hyC
    rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hyt with rfl | rfl
    · rfl
    · exact absurd (hCF hyC) h.t_not_mem
  have hKcard : Nat.card (Subgroup.zpowers h.t ⊔ C : Subgroup G) = 2 * Nat.card C := by
    rw [card_sup_eq_mul_of_disjoint htC hdisj, Nat.card_zpowers, h.orderOf_t]
  have hKCx : Subgroup.zpowers h.t ⊔ C ≤ Cx := sup_le ((Subgroup.zpowers_le).mpr htCx) hCCx
  have hKeq : Subgroup.zpowers h.t ⊔ C = Cx := Subgroup.eq_of_le_of_card_ge hKCx (by
    rw [hKcard]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero h2C) hdvd)
  rw [← hKeq]
  exact sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (hCF.trans h.le_centralizer)

end JTHyp

end CFSG.Walter.JT
