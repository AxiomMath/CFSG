module

public import CFSG.Walter.ReeOrder.JT.Section6E

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace BorelData

variable {h : JTHyp G} {b : BorelData h}

namespace M1Data

variable (d : b.M1Data) (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
include d hp hq5 hp3

omit hp hp3 in
theorem P_ne_bot : d.P ≠ ⊥ := by
  intro h0
  have := d.card
  rw [h0, Subgroup.card_bot] at this
  have h5 := h.five_lt
  rw [← JTHyp.q_eq] at h5
  have : 1 < h.q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
  omega

omit hp3 in
theorem card_le_card_normalizer_R :
    4 * (h.q ^ 3 * Nat.card b.C) ≤ Nat.card (Subgroup.normalizer (b.R : Set G)) := by
  have hdisj : Disjoint b.C d.P := Subgroup.disjoint_of_coprime_natCard (by
    rw [d.card, JTHyp.q_eq, ← pow_mul]
    exact Nat.Coprime.pow_right _ b.coprime_card_C)
  have hCP := card_sup_eq_mul_of_disjoint d.C_le hdisj
  have hTCP : b.T ≤ Subgroup.normalizer ((b.C ⊔ d.P : Subgroup G) : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.normalizer (b.C : Set G) := by
      refine mem_normalizer_of_conj_mem fun y hy => ?_
      rcases b.mem_T_iff.mp hx with rfl | rfl | rfl | rfl
      · have hyc : y * (h.t * b.τ) = (h.t * b.τ) * y :=
          Subgroup.mem_centralizer_singleton_iff.mp (b.C_le_centralizer (Or.inr (Or.inr rfl)) hy)
        rw [show h.t * b.τ * y * (h.t * b.τ)⁻¹ = y by rw [← hyc, mul_inv_cancel_right]]
        exact hy
      · rw [show h.t * y * h.t⁻¹ = y by rw [← b.C_comm_t hy, mul_inv_cancel_right]]
        exact hy
      · rw [show b.τ * y * b.τ⁻¹ = y by rw [← b.C_comm y hy, mul_inv_cancel_right]]
        exact hy
      · rw [one_mul, inv_one, mul_one]
        exact hy
    exact mem_normalizer_sup hxC (b.T_le_normalizer d.t_mem d.τ_mem hx)
  have hdisj' : Disjoint b.T (b.C ⊔ d.P) := Subgroup.disjoint_of_coprime_natCard (by
    rw [b.isKleinFour_T.card_four, hCP, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ((b.odd_card_C hq5).mul
      (h.odd_card_of_isPGroup hp d.isPGroup))))
  have hcard := card_sup_eq_mul_of_disjoint hTCP hdisj'
  have hle : b.T ⊔ (b.C ⊔ d.P) ≤ Subgroup.normalizer (b.R : Set G) :=
    sup_le (b.T_le_normalizer b.t_mem_normalizer_R b.τ_mem_normalizer_R)
      (sup_le b.C_le_normalizer d.le_normalizer)
  have := Subgroup.card_le_of_le hle
  rw [hcard, b.isKleinFour_T.card_four, hCP, d.card, mul_comm (Nat.card b.C)] at this
  exact this

theorem exists_mem_normalizer_not_mem_centralizer :
    ∃ y ∈ Subgroup.normalizer (d.P : Set G), y ∈ Subgroup.normalizer (b.T : Set G) ∧
      y ∉ Subgroup.centralizer (b.T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (d.P : Set G) with hNdef
  have hTN : b.T ≤ N := b.T_le_normalizer d.t_mem d.τ_mem
  have h8 : ¬ 8 ∣ Nat.card N := h.not_eight_dvd hp d.isPGroup (d.P_ne_bot hq5)
  have hTcard : Nat.card (b.T.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, b.isKleinFour_T.card_four]
  have hfacN : (Nat.card N).factorization 2 = 2 := by
    have h4 : 2 ^ 2 ∣ Nat.card N := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← b.isKleinFour_T.card_four]
      exact Subgroup.card_dvd_of_le hTN
    have h8' : ¬ 2 ^ 3 ∣ Nat.card N := by norm_num; exact h8
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h4 h8'
    omega
  let TS : Sylow 2 N := Sylow.ofCard (b.T.subgroupOf N) (by rw [hTcard, hfacN]; norm_num)
  have hTS : (TS : Subgroup N) = b.T.subgroupOf N := Sylow.coe_ofCard _ _
  by_contra hne
  push Not at hne
  have hNC : Subgroup.normalizer ((TS : Subgroup N) : Set N) ≤
      Subgroup.centralizer ((TS : Subgroup N) : Set N) := by
    intro y hy
    have hyT : (y : G) ∈ Subgroup.normalizer (b.T : Set G) := by
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨x, hTN hx⟩).mp (by
        rw [hTS, Subgroup.mem_subgroupOf]; exact hx)
      rw [hTS, Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have hyC := hne y y.2 hyT
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro x hx
    have hx' : (x : G) ∈ b.T := by rw [hTS] at hx; exact hx
    exact Subtype.ext (hyC x hx')
  obtain ⟨K, hKn, hK2, hKmem, hKcard⟩ := exists_normal_complement_of_le_centralizer TS hNC
  set KG := K.map N.subtype with hKGdef
  have hKGcard : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective N.subtype_injective
  have hKGodd : Odd (Nat.card KG) := by
    rw [hKGcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK2)
  have hKGN : ∀ g ∈ N, g ∈ Subgroup.normalizer (KG : Set G) := by
    intro g hg
    have hmem' : (⟨g, hg⟩ : N) ∈ Subgroup.normalizer (K : Set N) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map N.subtype ⟨⟨g, hg⟩, hmem', rfl⟩
  have hKGmem : ∀ x ∈ N, Odd (orderOf x) → x ∈ KG := by
    intro x hx hodd
    refine ⟨⟨x, hx⟩, hKmem _ ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.mpr hodd
  have hCKG : b.C ≤ KG := fun x hx => hKGmem x (d.C_le hx)
    (Odd.of_dvd_nat (b.odd_card_C hq5) (Subgroup.orderOf_dvd_natCard _ hx))
  obtain ⟨PK, hPKKG, hPKp, hPKmem, hKGcard', k, hk, hPKcard⟩ := b.exists_sylow_normal hp hq5 hp3
    hKGodd (hKGN _ d.t_mem) (hKGN _ d.τ_mem) hCKG
  have hpodd : ∀ {y : G} {n : ℕ}, y ^ h.p ^ n = 1 → Odd (orderOf y) := fun hy =>
    Odd.of_dvd_nat ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow (orderOf_dvd_of_pow_eq_one hy)
  have hPPK : d.P ≤ PK := fun x hx => by
    obtain ⟨n, hn⟩ := d.isPGroup ⟨x, hx⟩
    have hxn : x ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hPKmem x (hKGmem x (Subgroup.le_normalizer hx) (hpodd hxn)) n hxn
  have hq2 : 2 ≤ h.q := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have hk3 : k = 3 := by
    have := Subgroup.card_le_of_le hPPK
    rw [d.card, hPKcard] at this
    have := (Nat.pow_le_pow_iff_right hq2).mp this
    omega
  have hPeq : d.P = PK := Subgroup.eq_of_le_of_card_ge hPPK (by rw [hPKcard, d.card, hk3])
  have hmemP : ∀ y ∈ N, ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ d.P := fun y hy n hyn => by
    rw [hPeq]
    exact hPKmem y (hKGmem y hy (hpodd hyn)) n hyn
  have hNcard : Nat.card N = 4 * (h.q ^ 3 * Nat.card b.C) := by
    rw [← hKcard, ← hKGcard, hKGcard', ← hPeq, d.card, Sylow.card_eq_multiplicity, hfacN]
    ring
  have hNR : Subgroup.normalizer (b.R : Set G) = N := Subgroup.eq_of_le_of_card_ge
    (fun g hg => d.normal g hg) (by rw [hNcard]; exact d.card_le_card_normalizer_R hp hq5)
  obtain ⟨S, hPS⟩ := d.isPGroup.exists_le_sylow
  have hSP : (S : Subgroup G) = d.P := by
    refine (Subgroup.eq_of_le_of_card_ge hPS ?_).symm
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyN, ⟨n, hyn⟩, hyP⟩ := exists_pow_eq_one_not_mem d.isPGroup fun S' => by
      rwa [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S]
    exact hyP (hmemP y hyN n hyn)
  have hτu : b.τ = h.t ∨ b.τ = b.τ ∨ b.τ = h.t * b.τ := Or.inr (Or.inl rfl)
  obtain ⟨g, hg⟩ := h.exists_conj_of_card_eq hp b.R_le_F b.card_R b.orderOf_τ
    (inf_le_right : d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) ≤ _) (d.card_inf hp hq5 hp3 hτu)
  have hq1 : 1 < h.q := by omega
  have hnt : Nontrivial (d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [d.card_inf hp hq5 hp3 hτu]; exact hq1)
  obtain ⟨⟨r, hr⟩, hr1⟩ := exists_ne (1 : (d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) :
    Subgroup G))
  have hr1' : r ≠ 1 := fun h0 => hr1 (Subtype.ext h0)
  have hgr : g * r * g⁻¹ ∈ b.R := by
    rw [← hg]
    exact ⟨r, hr, rfl⟩
  have hcen : ∀ {z : G}, z ∈ d.P → z ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff, hSP]
    intro w hw
    exact d.commute hp hq5 hp3 hw hz
  obtain ⟨n, hnN, hnr⟩ := exists_mem_normalizer_conj_of_mem_centralizer S (hcen hr.1)
    (hcen (d.R_le hgr)) rfl
  rw [hSP] at hnN
  have hnN' : n ∈ Subgroup.normalizer (b.R : Set G) := by rw [hNR]; exact hnN
  have hrR : r ∈ b.R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN') _).mp (hnr ▸ hgr)
    simpa [mul_assoc] using this
  exact hr1' (d.inf_T hp hq5 (d.R_le hrR) (b.R_comm_t hrR)
    (Subgroup.mem_centralizer_singleton_iff.mp hr.2))

variable (hq3 : h.q % 3 = 2)
include hq3

theorem exists_orderOf_three :
    ∃ μ : G, orderOf μ = 3 ∧ μ ∈ Subgroup.normalizer (d.P : Set G) ∧
      μ ∈ Subgroup.normalizer (b.T : Set G) ∧ ∃ x ∈ d.P, x ≠ 1 ∧ x * μ = μ * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyP, hyT, hyC⟩ := d.exists_mem_normalizer_not_mem_centralizer hp hq5 hp3
  obtain ⟨s, hsT⟩ := b.exists_setup
  have hy3 : y ^ 3 ∈ Subgroup.centralizer (b.T : Set G) := by
    have := centralizer_subgroupOf_normalizer_normal s.T
    have h3 := Subgroup.pow_index_mem
      ((Subgroup.centralizer (s.T : Set G)).subgroupOf (Subgroup.normalizer (s.T : Set G)))
      (⟨y, hsT ▸ hyT⟩ : Subgroup.normalizer (s.T : Set G))
    rw [show ((Subgroup.centralizer (s.T : Set G)).subgroupOf
        (Subgroup.normalizer (s.T : Set G))).index = 3 from
      s.relIndex_centralizer_T_normalizer_T hp, Subgroup.mem_subgroupOf] at h3
    rw [← hsT]
    simpa using h3
  have h3y : 3 ∣ orderOf y := by
    by_contra h3
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 3) (x := y)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    apply hyC
    rw [← hm]
    exact Subgroup.pow_mem _ hy3 m
  set μ := y ^ (orderOf y / 3) with hμdef
  have hμ3 : orderOf μ = 3 := orderOf_pow_orderOf_div (orderOf_pos y).ne' h3y
  have hμP : μ ∈ Subgroup.normalizer (d.P : Set G) := Subgroup.pow_mem _ hyP _
  refine ⟨μ, hμ3, hμP, Subgroup.pow_mem _ hyT _, ?_⟩
  have hmod := card_modEq_of_fixed hμ3 hμP
    (inf_le_left : d.P ⊓ Subgroup.centralizer ({μ} : Set G) ≤ d.P)
    (fun x hx => ⟨fun h1 => ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩,
      fun h1 => Subgroup.mem_centralizer_singleton_iff.mp h1.2⟩)
  rw [d.card] at hmod
  have hq33 : h.q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq3]
  have hne : Nat.card (d.P ⊓ Subgroup.centralizer ({μ} : Set G) : Subgroup G) ≠ 1 := by
    intro h1
    rw [h1] at hmod
    have := hmod
    unfold Nat.ModEq at this
    omega
  have hnt : Nontrivial (d.P ⊓ Subgroup.centralizer ({μ} : Set G) : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      have := (Nat.card_pos (α := (d.P ⊓ Subgroup.centralizer ({μ} : Set G) : Subgroup G)))
      omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : (d.P ⊓ Subgroup.centralizer ({μ} : Set G) :
    Subgroup G))
  exact ⟨x, hx.1, fun h0 => hx1 (Subtype.ext h0), Subgroup.mem_centralizer_singleton_iff.mp hx.2⟩

end M1Data

end BorelData

end CFSG.Walter.JT
