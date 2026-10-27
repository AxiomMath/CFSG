module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

section General

variable {G : Type} [Group G]

theorem zpowers_eq_of_card_prime [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : Nat.card X = p) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) : Subgroup.zpowers x = X := by
  have hle : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hx
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hX, Nat.card_zpowers]
  have hdvd : orderOf x ∣ p := by
    rw [← hX, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · omega

theorem exists_ne_one_of_card_prime [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : Nat.card X = p) : ∃ x ∈ X, x ≠ 1 := by
  by_contra hc
  push Not at hc
  have hbot : X = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hc x hx)
  rw [hbot, Subgroup.card_bot] at hX
  exact hp.one_lt.ne hX

theorem eq_one_or_eq_or_eq_sq_of_card_three [Finite G] {D₃ : Subgroup G}
    (hD₃ : Nat.card D₃ = 3) {d : G} (hd : d ∈ D₃) (hd1 : d ≠ 1) {e : G} (he : e ∈ D₃) :
    e = 1 ∨ e = d ∨ e = d ^ 2 := by
  have hz := zpowers_eq_of_card_prime Nat.prime_three hD₃ hd hd1
  have hord : orderOf d = 3 := by rw [← Nat.card_zpowers, hz, hD₃]
  rw [← hz] at he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  rw [← zpow_mod_orderOf, hord]
  have : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rcases this with h0 | h1 | h2
  · left; rw [h0, zpow_zero]
  · right; left; rw [h1, zpow_one]
  · right; right; rw [h2]; norm_cast

theorem pow_three_of_mem_of_card_three {D₃ : Subgroup G} (h3 : Nat.card D₃ = 3) {d : G}
    (hd : d ∈ D₃) : d ^ 3 = 1 := by
  have : (⟨d, hd⟩ : ↥D₃) ^ 3 = 1 := by rw [← h3]; exact pow_card_eq_one'
  simpa using congrArg Subtype.val this

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem charTwo_LT : CharTwo (L ⊔ T) := by
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hTS : (S : Subgroup G) ≤ L ⊔ T := by rw [hS]; exact le_sup_right
  have hSM : (S : Subgroup G) ≤ M := by rw [hS]; exact hh.T_le
  exact charTwo_of_le hh.qtke.2.1 S hTS hh.sup_le_M
    ⟨hSM, pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1⟩

theorem omegaOneCenter_le_center_pCoreOf :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (L ⊔ T) ⊓
      Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (hh.isSylowTwoOf le_sup_right)
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hz).2 x (hPT hx)
  refine le_inf (fun z hz => h.charTwo_LT ⟨?_, hZC hz⟩) hZC
  exact (le_sup_right : T ≤ L ⊔ T) (quasithinOmegaOneCenter_le_self T hz)

theorem omegaOneCenter_conj_mem {g z : G} (hg : g ∈ L ⊔ T)
    (hz : z ∈ quasithinOmegaOneCenter T) :
    g * z * g⁻¹ ∈ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
      (g * z * g⁻¹) ^ 2 = 1 := by
  have hz' := h.omegaOneCenter_le_center_pCoreOf hz
  have hgP : g ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := le_normalizer_pCoreOf 2 _ hg
  refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hgP z).mp hz'.1, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    have hx' : g⁻¹ * x * g ∈ pCoreOf 2 (L ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgP) x).mp hx
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hz'.2 _ hx'
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * x := by group
  · have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
    rw [conj_pow, hz2, mul_one, mul_inv_cancel]

theorem conj_mem_of_cyclic (hF : L2TorusFact) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D)
    (h3 : Nat.card D₃ = 3) {t g : G} (ht : t ∈ T) (hg : g ∈ D₃) :
    ∃ s ∈ T ⊓ L, ∃ e ∈ D₃, t * g * t⁻¹ = s * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hD := h.notation59.2.1
  obtain ⟨hcyc, -⟩ := hh.isCyclic_card_of_isHall hF hD
  have hsup := hh.borelL_eq_sup hD
  have hDB : D ≤ borelL T L := hD.1
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := hDB.trans inf_le_right
  have hbot : D ⊓ (T ⊓ L) = ⊥ := Hyp5_0_1.inf_eq_bot_of_isHall hD (hh.sylow.1.to_le inf_le_left)
  have htg : t * g * t⁻¹ ∈ borelL T L :=
    (Subgroup.mem_normalizer_iff.mp (hh.T_le_normalizer_borel ht) g).mp (hDB (hD₃ hg))
  rw [← hsup, sup_comm] at htg
  have hset : ((T ⊓ L ⊔ D : Subgroup G) : Set G) = ((T ⊓ L : Subgroup G) : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDN
  have htg' : t * g * t⁻¹ ∈ ((T ⊓ L : Subgroup G) : Set G) * (D : Set G) := by
    rw [← hset]; exact htg
  obtain ⟨s, hs, e, he, hse⟩ := Set.mem_mul.mp htg'
  refine ⟨s, hs, e, ?_, hse.symm⟩
  have hg3 : g ^ 3 = 1 := by
    have : (⟨g, hg⟩ : ↥D₃) ^ 3 = 1 := by rw [← h3]; exact pow_card_eq_one'
    simpa using congrArg Subtype.val this
  have hse3 : (s * e) ^ 3 = 1 := by
    rw [hse, conj_pow, hg3, mul_one, mul_inv_cancel]
  have hs1 : e * s * e⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp (hDN he) s).mp hs
  have hs2 : e * e * s * e⁻¹ * e⁻¹ ∈ T ⊓ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hDN (D.mul_mem he he)) s).mp hs
    simpa [mul_assoc] using this
  have he3 : e ^ 3 = 1 := by
    have hse3' : (s * e) * (s * e) * (s * e) = 1 := by rw [← hse3, pow_succ, pow_succ, pow_one]
    have e1 : e ^ 3 = (s * (e * s * e⁻¹) * (e * e * s * e⁻¹ * e⁻¹))⁻¹ *
        ((s * e) * (s * e) * (s * e)) := by group
    rw [hse3', mul_one] at e1
    have hmem : e ^ 3 ∈ D ⊓ (T ⊓ L) :=
      ⟨D.pow_mem he 3, e1 ▸ (T ⊓ L).inv_mem ((T ⊓ L).mul_mem ((T ⊓ L).mul_mem hs hs1) hs2)⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hle : Subgroup.zpowers (⟨e, he⟩ : ↥D) ≤ D₃.subgroupOf D := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers]
    have hcard : Nat.card (D₃.subgroupOf D) = 3 := by
      rw [← h3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃).toEquiv
    rw [hcard]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using he3)
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_zpowers _))

theorem conj_ne (h5114 : Stmt5_1_14_first) {D₃ : Subgroup G} (h3 : Nat.card D₃ = 3)
    (hD₃M : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {z d : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hd : d ∈ D₃) (hd1 : d ≠ 1) :
    d * z * d⁻¹ ≠ z := by
  intro hdz
  apply hD₃M
  rw [← zpowers_eq_of_card_prime Nat.prime_three h3 hd hd1]
  refine Subgroup.zpowers_le.mpr ((h5114 G T M L V H B D n h.hyp h.notation59 h.module
    h.l34).2.1.2 z hz hz1 ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  calc z * d = d * z * d⁻¹ * d := by rw [hdz]
    _ = d * z := by group

theorem D₃_le_L {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) : D₃ ≤ L :=
  hD₃.trans (h.notation59.2.1.1.trans inf_le_left)

theorem conj_conj_eq (hF : L2TorusFact) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    {t z d : G} (ht : t ∈ T) (hz : z ∈ quasithinOmegaOneCenter T) (hd : d ∈ D₃) (hd1 : d ≠ 1) :
    ∃ e ∈ D₃, e ≠ 1 ∧ t * (d * z * d⁻¹) * t⁻¹ = e * z * e⁻¹ ∧
      t * (d ^ 2 * z * (d ^ 2)⁻¹) * t⁻¹ = e ^ 2 * z * (e ^ 2)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs, e, he, hse⟩ := h.conj_mem_of_cyclic hF hD₃ h3 ht hd
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    h.notation59.2.1.1.trans inf_le_right
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := (quasithinOmegaOneCenter_le_inf T hz).2
  have htz : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzC t ht]; group
  have hcomm : ∀ x ∈ D, ∀ s' ∈ T ⊓ L, s' * (x * z * x⁻¹) * s'⁻¹ = x * z * x⁻¹ := by
    intro x hx s' hs'
    have hs'' : x⁻¹ * s' * x ∈ T ⊓ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hDN (D.inv_mem hx)) s').mp hs'
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hzC _ hs''.1
    calc s' * (x * z * x⁻¹) * s'⁻¹ = x * ((x⁻¹ * s' * x) * z) * (x⁻¹ * s' * x)⁻¹ * x⁻¹ := by
          group
      _ = x * (z * (x⁻¹ * s' * x)) * (x⁻¹ * s' * x)⁻¹ * x⁻¹ := by rw [hc]
      _ = x * z * x⁻¹ := by group
  have he1 : e ≠ 1 := by
    intro he1
    rw [he1, mul_one] at hse
    have hd3 := pow_three_of_mem_of_card_three h3 hd
    obtain ⟨m, hm⟩ := (h.hyp.sylow.1.to_le inf_le_left) ⟨s, hs⟩
    have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hdm : d ^ 2 ^ m = 1 := by
      have h1 : (t * d * t⁻¹) ^ 2 ^ m = 1 := by rw [hse]; exact hsm
      rw [conj_pow] at h1
      have e2 : d ^ 2 ^ m = t⁻¹ * (t * d ^ 2 ^ m * t⁻¹) * t := by group
      rw [e2, h1]
      group
    have hord1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have hord2 : orderOf d ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hdm
    have : orderOf d ∣ Nat.gcd 3 (2 ^ m) := Nat.dvd_gcd hord1 hord2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right m (by norm_num))] at this
    exact hd1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
  refine ⟨e, he, he1, ?_, ?_⟩
  · have e1 : t * (d * z * d⁻¹) * t⁻¹ = (t * d * t⁻¹) * (t * z * t⁻¹) * (t * d * t⁻¹)⁻¹ := by
      group
    rw [e1, htz, hse]
    have := hcomm e (hD₃ he) s hs
    calc s * e * z * (s * e)⁻¹ = s * (e * z * e⁻¹) * s⁻¹ := by group
      _ = e * z * e⁻¹ := this
  · have hs1 : e * s * e⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp (hDN (hD₃ he)) s).mp hs
    have hss : s * (e * s * e⁻¹) ∈ T ⊓ L := (T ⊓ L).mul_mem hs hs1
    have e1 : t * (d ^ 2 * z * (d ^ 2)⁻¹) * t⁻¹ =
        (t * d * t⁻¹) * (t * d * t⁻¹) * (t * z * t⁻¹) * ((t * d * t⁻¹) * (t * d * t⁻¹))⁻¹ := by
      rw [sq]; group
    rw [e1, htz, hse]
    have := hcomm (e ^ 2) (D.pow_mem (hD₃ he) 2) _ hss
    calc s * e * (s * e) * z * (s * e * (s * e))⁻¹ =
        (s * (e * s * e⁻¹)) * (e ^ 2 * z * (e ^ 2)⁻¹) * (s * (e * s * e⁻¹))⁻¹ := by
          rw [sq]; group
      _ = e ^ 2 * z * (e ^ 2)⁻¹ := this

theorem norm_eq_one (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) {D₃ : Subgroup G}
    (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    (hD₃M : ¬ D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {z d : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hd : d ∈ D₃) (hd1 : d ≠ 1) :
    z * (d * z * d⁻¹) * (d ^ 2 * z * (d ^ 2)⁻¹) = 1 := by
  have hdLT : d ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) (h.D₃_le_L hD₃ hd)
  have hd3 := pow_three_of_mem_of_card_three h3 hd
  obtain ⟨ha, ha2⟩ := h.omegaOneCenter_conj_mem (Subgroup.one_mem _) hz
  obtain ⟨hb, hb2⟩ := h.omegaOneCenter_conj_mem hdLT hz
  obtain ⟨hc, hc2⟩ := h.omegaOneCenter_conj_mem ((L ⊔ T).pow_mem hdLT 2) hz
  simp only [one_mul, inv_one, mul_one] at ha ha2
  set b := d * z * d⁻¹ with hbdef
  set c := d ^ 2 * z * (d ^ 2)⁻¹ with hcdef
  have hcm : ∀ x ∈ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G),
      ∀ y ∈ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G),
      Commute x y := fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hy.2 x hx.1)
  have hab : Commute z b := hcm _ ha _ hb
  have hac : Commute z c := hcm _ ha _ hc
  have hbc : Commute b c := hcm _ hb _ hc
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (h.hyp.isSylowTwoOf le_sup_right)
  have hwT : z * b * c ∈ T := T.mul_mem (T.mul_mem (hPT ha.1) (hPT hb.1)) (hPT hc.1)
  have hw2 : (z * b * c) ^ 2 = 1 := by
    rw [(Commute.mul_left hac hbc).mul_pow, hab.mul_pow, ha2, hb2, hc2, one_mul, one_mul]
  have hwC : z * b * c ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨e, he, he1, h1, h2⟩ := h.conj_conj_eq hF hD₃ h3 ht hz hd hd1
    have hza : t * z * t⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hz).2 t ht]
      group
    have hconj : t * (z * b * c) * t⁻¹ = z * b * c := by
      have e0 : t * (z * b * c) * t⁻¹ = (t * z * t⁻¹) * (t * b * t⁻¹) * (t * c * t⁻¹) := by group
      rw [e0, hza, hbdef, hcdef, h1, h2]
      rcases eq_one_or_eq_or_eq_sq_of_card_three h3 hd hd1 he with h0 | hed | hed
      · exact absurd h0 he1
      · rw [hed]
      · rw [hed]
        have e4 : (d ^ 2) ^ 2 * z * ((d ^ 2) ^ 2)⁻¹ = d * z * d⁻¹ := by
          have : (d ^ 2) ^ 2 = d * d ^ 3 := by rw [← pow_mul, ← pow_succ']
          rw [this, hd3, mul_one]
        rw [e4, ← hbdef, ← hcdef, mul_assoc, hbc.symm.eq, ← mul_assoc]
    calc t * (z * b * c) = t * (z * b * c) * t⁻¹ * t := by group
      _ = z * b * c * t := by rw [hconj]
  have hwZ : z * b * c ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hwT, hwC, hw2⟩
  by_contra hw1
  apply h.conj_ne h5114 h3 hD₃M hwZ hw1 hd hd1
  have e1 : d * (z * b * c) * d⁻¹ = b * c * (d ^ 3 * z * (d ^ 3)⁻¹) := by
    rw [hbdef, hcdef, sq, pow_succ, sq]; group
  rw [e1, hd3, one_mul, inv_one, mul_one, ← (hab.mul_right hac).eq, ← mul_assoc]

theorem conj_gen_mem (hF : L2TorusFact) {D₃ : Subgroup G} (hD₃ : D₃ ≤ D) (h3 : Nat.card D₃ = 3)
    {t z g : G} (ht : t ∈ T) (hz : z ∈ quasithinOmegaOneCenter T) (hg : g ∈ D₃) :
    ∃ e ∈ D₃, t * (g * z * g⁻¹) * t⁻¹ = e * z * e⁻¹ := by
  by_cases hg1 : g = 1
  · refine ⟨1, D₃.one_mem, ?_⟩
    simp only [hg1, one_mul, inv_one, mul_one]
    rw [Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hz).2 t ht]
    group
  · obtain ⟨e, he, -, h1, -⟩ := h.conj_conj_eq hF hD₃ h3 ht hz hg hg1
    exact ⟨e, he, h1⟩

end Hyp5_1_14

end Setting

theorem stmt5_1_21_of_inputs (h5114 : Stmt5_1_14_first) (h520 : Stmt5_1_20)
    (hF : L2TorusFact) : Stmt5_1_21 := by
  intro G _ _ T M L V H B D D₃ Z₁ H₁ n hyp hN hV hK hnot hD₃ h3 hZ1 hHH₁ hH₁C
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  have hD₃M := (h520 G T M L V H B D n hyp hN hV hK hnot D₃ hD₃ h3).1
  obtain ⟨hZ1Z, hZ1card, -⟩ := hZ1
  obtain ⟨z, hzZ1, hz1⟩ := exists_ne_one_of_card_prime Nat.prime_two hZ1card
  have hZ1eq : Subgroup.zpowers z = Z₁ :=
    zpowers_eq_of_card_prime Nat.prime_two hZ1card hzZ1 hz1
  have hz : z ∈ quasithinOmegaOneCenter T := hZ1Z hzZ1
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp hz).2.2
  obtain ⟨d, hdD₃, hd1⟩ := exists_ne_one_of_card_prime Nat.prime_three h3
  have hd3 := pow_three_of_mem_of_card_three h3 hdD₃
  have hdLT : d ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) (h.D₃_le_L hD₃ hdD₃)
  have hZ1el : ∀ y ∈ Z₁, y = 1 ∨ y = z := by
    intro y hy
    rw [← hZ1eq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    rw [← zpow_mod_orderOf, hord]
    have : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases this with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  set b := d * z * d⁻¹ with hbdef
  set c := d ^ 2 * z * (d ^ 2)⁻¹ with hcdef
  have hnorm : z * b * c = 1 := h.norm_eq_one h5114 hF hD₃ h3 hD₃M hz hdD₃ hd1
  obtain ⟨hzP, -⟩ := h.omegaOneCenter_conj_mem (Subgroup.one_mem _) hz
  obtain ⟨hbP, hb2⟩ := h.omegaOneCenter_conj_mem hdLT hz
  simp only [one_mul, inv_one, mul_one] at hzP
  have hzb : Commute z b := Subgroup.mem_centralizer_iff.mp hbP.2 z hzP.1
  have hc : c = z * b := by
    have e1 : c = (z * b)⁻¹ := eq_inv_of_mul_eq_one_right hnorm
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
    rw [e1, mul_inv_rev, hzi, hbi]
    exact hzb.symm.eq
  have hb1 : b ≠ 1 := by
    intro hb
    apply hz1
    have : z = d⁻¹ * b * d := by rw [hbdef]; group
    rw [this, hb]; group
  have hbz : b ≠ z := h.conj_ne h5114 h3 hD₃M hz hz1 hdD₃ hd1
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set L₂ := conjClosure D₃ T with hL₂def
  have hgen : ∀ g ∈ D₃, ∀ y ∈ Z₁, g * y * g⁻¹ ∈
      pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
      (g * y * g⁻¹) ^ 2 = 1 := fun g hg y hy =>
    h.omegaOneCenter_conj_mem ((le_sup_left : L ≤ L ⊔ T) (h.D₃_le_L hD₃ hg)) (hZ1Z hy)
  have hV₂el : IsElemAbelian 2 V₂ := by
    refine F7.isElemAbelian_closure _ ?_ ?_
    · rintro _ ⟨g, hg, y, hy, rfl⟩ _ ⟨g', hg', y', hy', rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp (hgen g' hg' y' hy').1.2 _ (hgen g hg y hy).1.1)
    · rintro _ ⟨g, hg, y, hy, rfl⟩
      exact (hgen g hg y hy).2
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (hh.isSylowTwoOf le_sup_right)
  have hV₂T : V₂ ≤ T := conjClosure_le fun g hg y hy => hPT (hgen g hg y hy).1.1
  have hZ1V₂ : Z₁ ≤ V₂ := le_conjClosure Z₁ D₃
  have hbV₂ : b ∈ V₂ := mem_conjClosure hdD₃ hzZ1
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (Z₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_forall_conj_mem'
    intro y hy
    rcases hZ1el y hy with rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact Z₁.one_mem
    · rw [hzb.symm.eq, mul_assoc, mul_inv_cancel, mul_one]; exact hzZ1
  have hV₂le : V₂ ≤ Z₁ ⊔ Subgroup.zpowers b := by
    refine conjClosure_le fun g hg y hy => ?_
    rcases hZ1el y hy with rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    rcases eq_one_or_eq_or_eq_sq_of_card_three h3 hdD₃ hd1 hg with rfl | rfl | rfl
    · rw [one_mul, inv_one, mul_one]; exact Subgroup.mem_sup_left hzZ1
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · rw [← hcdef, hc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzZ1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hTZ1 : T ≤ Subgroup.normalizer (Z₁ : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro y hy
    rw [Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T (hZ1Z hy)).2 t ht,
      mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro v hv
    have hle : V₂ ≤ V₂.comap (MulAut.conj t).toMonoidHom := by
      refine conjClosure_le fun g hg y hy => ?_
      show t * (g * y * g⁻¹) * t⁻¹ ∈ V₂
      obtain ⟨e, he, he'⟩ := h.conj_gen_mem hF hD₃ h3 ht (hZ1Z hy) hg
      rw [he']
      exact mem_conjClosure he hy
    exact hle hv
  have hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    hN.2.1.1.trans inf_le_right
  have hL₂Y : L₂ ≤ T ⊓ L ⊔ D₃ := by
    refine conjClosure_le fun t ht g hg => ?_
    obtain ⟨s, hs, e, he, hse⟩ := h.conj_mem_of_cyclic hF hD₃ h3 ht hg
    rw [hse]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right he)
  have hlOne : lOne L₂ Z₁ ≤ T := by
    refine (oTwoUpper_le _).trans fun x hx => ?_
    obtain ⟨hxL₂, hxN⟩ := hx
    have hset : ((T ⊓ L ⊔ D₃ : Subgroup G) : Set G) =
        ((T ⊓ L : Subgroup G) : Set G) * (D₃ : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hD₃.trans hDN)
    have hx' : x ∈ ((T ⊓ L : Subgroup G) : Set G) * (D₃ : Set G) := by
      rw [← hset]; exact hL₂Y hxL₂
    obtain ⟨s, hs, e, he, rfl⟩ := Set.mem_mul.mp hx'
    have hsz : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hz).2 s hs.1]
      group
    have hxz : s * e * z * (s * e)⁻¹ ∈ Z₁ := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzZ1
    have hez : e * z * e⁻¹ = z := by
      rcases hZ1el _ hxz with h1 | h1
      · exfalso
        apply hz1
        have : z = (s * e)⁻¹ * (s * e * z * (s * e)⁻¹) * (s * e) := by group
        rw [this, h1]; group
      · have e2 : e * z * e⁻¹ = s⁻¹ * (s * e * z * (s * e)⁻¹) * s := by group
        rw [e2, h1]
        have : s⁻¹ * z * s = s⁻¹ * (s * z * s⁻¹) * s := by rw [hsz]
        rw [this]; group
    have he1 : e = 1 := by
      by_contra he1
      exact h.conj_ne h5114 h3 hD₃M hz hz1 he he1 hez
    rw [he1, mul_one]
    exact hs.1
  have hL₂o : L₂ = oTwoUpper L₂ := by
    refine le_antisymm ?_ (oTwoUpper_le L₂)
    refine conjClosure_le fun t ht g hg => mem_oTwoUpper_of_odd (mem_conjClosure ht hg) ?_
    have hord : orderOf (t * g * t⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      rw [conj_pow, pow_three_of_mem_of_card_three h3 hg, mul_one, mul_inv_cancel])
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1 <;> rw [h1] <;> decide
  have hTH₁ : T ≤ H₁ := hyp.hStar.1.1.trans hHH₁
  have hZ1H₁ : Z₁ ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 ((hZ1Z.trans (quasithinOmegaOneCenter_le_self T)).trans hTH₁)
      (hH₁C.trans (Subgroup.centralizer_le_normalizer _))
      (hh.sylow.1.to_le (hZ1Z.trans (quasithinOmegaOneCenter_le_self T)))
  have hO₁ : pCoreOf 2 H₁ ≠ ⊥ := fun hb => by
    have := hZ1H₁ hzZ1
    rw [hb, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hSH₁ : (S : Subgroup G) ≤ H₁ := by rw [hS]; exact hTH₁
  have hchar : CharTwo H₁ := charTwo_of_le hh.qtke.2.1 S hSH₁ le_rfl ⟨hSH₁, hO₁⟩
  have hirr : IsIrredOnSection (lOne L₂ Z₁ ⊔ T) V₂ Z₁ := by
    refine ⟨lt_of_le_of_ne hZ1V₂ fun he => ?_, (sup_le hlOne le_rfl).trans hTV₂,
      (sup_le hlOne le_rfl).trans hTZ1, fun W hW1 hW2 _ => ?_⟩
    · have hb' : b ∈ Z₁ := he ▸ hbV₂
      rcases hZ1el b hb' with h1 | h1
      · exact hb1 h1
      · exact hbz h1
    · by_cases hbW : b ∈ W
      · right
        refine le_antisymm hW2 (conjClosure_le fun g hg y hy => ?_)
        have hmem := hV₂le (mem_conjClosure hg hy)
        have hset : ((Z₁ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
            (Z₁ : Set G) * (Subgroup.zpowers b : Set G) :=
          Subgroup.coe_mul_of_right_le_normalizer_left _ _ hbN
        have hmem' : g * y * g⁻¹ ∈ (Z₁ : Set G) * (Subgroup.zpowers b : Set G) := by
          rw [← hset]; exact hmem
        obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hmem'
        rw [← huv]
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact W.mul_mem (hW1 hu) (W.zpow_mem hbW j)
      · left
        refine le_antisymm (fun x hx => ?_) hW1
        have hmem := hV₂le (hW2 hx)
        have hset : ((Z₁ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
            (Z₁ : Set G) * (Subgroup.zpowers b : Set G) :=
          Subgroup.coe_mul_of_right_le_normalizer_left _ _ hbN
        have hmem' : x ∈ (Z₁ : Set G) * (Subgroup.zpowers b : Set G) := by
          rw [← hset]; exact hmem
        obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hmem'
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        have hord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
        rcases Int.emod_two_eq_zero_or_one j with hj | hj
        · have : b ^ j = 1 := by
            rw [← zpow_mod_orderOf, hord]; push_cast; rw [hj, zpow_zero]
          rw [this, mul_one]; exact hu
        · exfalso
          apply hbW
          have hbj : b ^ j = b := by
            rw [← zpow_mod_orderOf, hord]; push_cast; rw [hj, zpow_one]
          have : b = u⁻¹ * (u * b ^ j) := by rw [hbj]; group
          rw [this]
          exact W.mul_mem (W.inv_mem (hW1 hu)) hx
  have hASH : AlmostSpecialHyp V₂ Z₁ L₂ T H₁ :=
    { elemAbelian := hV₂el
      ne_bot := fun hb => hz1 (by rw [hb] at hzZ1; exact Subgroup.mem_bot.mp hzZ1)
      le_V := hZ1V₂
      oTwo_eq := hL₂o
      V_le_T := hV₂T
      T_le_normV₁ := hTZ1
      T_le_normV := hTV₂
      T_le_normL := le_normalizer_conjClosure D₃ T
      sylow_LT := hh.isSylowTwoOf le_sup_right
      H_le := hH₁C.trans (Subgroup.centralizer_le_normalizer _)
      lOne_sup_le := sup_le (hlOne.trans hTH₁) hTH₁
      sylow_H := hh.isSylowTwoOf hTH₁
      charTwo := hchar
      irred := hirr }
  refine ⟨Subgroup.commutator_le.mpr fun u hu q hq => ?_, hASH.G22_two⟩
  have hUH₁ : conjClosure V₂ H₁ ≤ H₁ := conjClosure_le fun x hx v hv =>
    H₁.mul_mem (H₁.mul_mem hx (hTH₁ (hV₂T hv))) (H₁.inv_mem hx)
  have hN₁ : H₁ ≤ Subgroup.normalizer (Z₁ : Set G) :=
    hH₁C.trans (Subgroup.centralizer_le_normalizer _)
  have hu' := (secImg_le_iff.1 hASH.G22_one.2) ⟨u, hN₁ (hUH₁ hu)⟩ hu
  have hq' : tmk Z₁ ⟨q, hN₁ (pCoreOf_le 2 H₁ hq)⟩ ∈ tildeOf Z₁ (pCoreOf 2 H₁) :=
    secMk_mem_secImg hq
  have hcomm := mem_centralizer_of_mem_omegaOneCenterOf hu' hq'
  exact commutator_mem_of_secMk_commute hcomm.symm

end CFSG.Quasithin.H13
