module

public import CFSG.Walter.ReeOrder.JT.Section4H
public import CFSG.Walter.ReeOrder.JT.Section4I

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_of_odd_of_psl24
    {L : Type*} [Group L] (e : L ≃* PSL(2, GaloisField 2 2))
    {H : Subgroup L} (hodd : Odd (Nat.card H)) : Nat.card H ∣ 3 ∨ Nat.card H ∣ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  set H' := H.map e.toMonoidHom with hH'def
  have hH'card : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective e.injective
  have h2 : ¬ 2 ∣ Nat.card H' := by
    rw [hH'card]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rcases Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hKcard H' h2 with
    ⟨z, hz, hcard, -⟩ | ⟨z, -, hcard, -⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩ | ⟨-, ⟨e'⟩⟩
  · rw [hKcard] at hz
    norm_num at hz
    rw [← hH'card, hcard]
    exact hz
  · exfalso
    rw [← hH'card, hcard] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul z)
  · exfalso
    rw [← hH'card, Nat.card_congr e'.toEquiv, card_alternatingGroup_four] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [← hH'card, Nat.card_congr e'.toEquiv, card_perm_four] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [← hH'card, Nat.card_congr e'.toEquiv, card_alternatingGroup_five] at hodd
    exact absurd hodd (by decide)

section DirectProduct

variable {X : Type*} [Group X] [Finite X] {A B H : Subgroup X}

omit [Finite X] in
theorem IsInternalDirectProduct.pow_eq_one_of_mul (hd : IsInternalDirectProduct A B H) {a b : X}
    (ha : a ∈ A) (hb : b ∈ B) {n : ℕ} (hn : (a * b) ^ n = 1) : a ^ n = 1 ∧ b ^ n = 1 := by
  have hc : Commute a b := hd.commute ha hb
  rw [hc.mul_pow] at hn
  have h1 : a ^ n = (b ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have h2 : a ^ n ∈ B := h1 ▸ B.inv_mem (B.pow_mem hb n)
  have h3 : a ^ n = 1 := Subgroup.disjoint_def.mp hd.2.1 (A.pow_mem ha n) h2
  refine ⟨h3, ?_⟩
  rw [h3, one_mul] at hn
  exact hn

end DirectProduct

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

theorem card_normalizer_T :
    Nat.card (Subgroup.normalizer (s.T : Set G)) = 24 * Nat.card s.Q := by
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (s.T : Set G))
    (Subgroup.normalizer (s.T : Set G))
  rw [s.relIndex_centralizer_T_normalizer_T hp, inf_eq_left.mpr
    s.centralizer_T_le_normalizer_T, s.card_centralizer_T hp] at h2
  omega

theorem mem_Q_of_mem_normalizer_T
    {z : G} (hz : z ∈ Subgroup.normalizer (s.T : Set G))
    (hz6 : Nat.Coprime (orderOf z) 6) : z ∈ s.Q := by
  have := centralizer_subgroupOf_normalizer_normal s.T
  have h3 := Subgroup.pow_index_mem
    ((Subgroup.centralizer (s.T : Set G)).subgroupOf (Subgroup.normalizer (s.T : Set G)))
    (⟨z, hz⟩ : Subgroup.normalizer (s.T : Set G))
  rw [show ((Subgroup.centralizer (s.T : Set G)).subgroupOf
      (Subgroup.normalizer (s.T : Set G))).index = 3 from
    s.relIndex_centralizer_T_normalizer_T hp, Subgroup.mem_subgroupOf] at h3
  have hzC : z ∈ Subgroup.centralizer (s.T : Set G) := by
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 3) (x := z)
      (Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hz6))
    rw [← hm]
    exact Subgroup.pow_mem _ (by simpa using h3) m
  rw [s.mem_Q_iff hp]
  exact ⟨hzC, Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) hz6)⟩

theorem mem_Q_of_mem_D_of_odd
    {D : Subgroup G} (hQD : s.Q ≤ D)
    (hD : 2 * (Nat.card D : ℤ) = h.q + h.eps) {d : G} (hdD : d ∈ D) (hd : Odd (orderOf d)) :
    d ∈ s.Q := by
  have h4 := s.four_mul_card_Q hp
  have hDcard : Nat.card D = 2 * Nat.card s.Q := by
    have : (Nat.card D : ℤ) = 2 * Nat.card s.Q := by linarith
    exact_mod_cast this
  have hidx : (s.Q.subgroupOf D).index = 2 := by
    have h1 := (s.Q.subgroupOf D).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv, hDcard] at h1
    have hQ0 : 0 < Nat.card s.Q := Nat.card_pos
    nlinarith
  exact mem_of_relIndex_two_of_odd hidx hdD hd

variable (hS : SuzukiFourGroupTheorem) (h3Q : ¬ 3 ∣ Nat.card s.Q)
include hS h3Q

theorem mem_Q_of_commute
    {μ : G} (hμ : μ ∈ Subgroup.normalizer (s.Q : Set G))
    (hμ3 : orderOf μ = 3) {y : G} (hyN : y ∈ Subgroup.normalizer (s.Q : Set G))
    (hyμ : y * μ = μ * y) (hy6 : Nat.Coprime (orderOf y) 6) : y ∈ s.Q := by
  classical
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  · exact s.mem_Q_of_mem_normalizer_T hp (h1 ▸ hyN) hy6
  obtain ⟨a₀, ha₀, d₀, hd₀, hμad⟩ := hLD.exists_mul hμ
  have hd₀1 : d₀ = 1 := by
    have h3 : (a₀ * d₀) ^ 3 = 1 := by rw [hμad, ← hμ3, pow_orderOf_eq_one]
    have hd3 := (hLD.pow_eq_one_of_mul ha₀ hd₀ h3).2
    have h2 : orderOf d₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have hd₀Q : d₀ ∈ s.Q :=
      s.mem_Q_of_mem_D_of_odd hp hQD hD hd₀ (Odd.of_dvd_nat (by decide) h2)
    have h1 : orderOf d₀ ∣ Nat.card s.Q := Subgroup.orderOf_dvd_natCard _ hd₀Q
    have hcop : Nat.Coprime 3 (Nat.card s.Q) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  rw [hd₀1, mul_one] at hμad
  subst hμad
  obtain ⟨a, ha, d, hd, rfl⟩ := hLD.exists_mul hyN
  have hpow := hLD.pow_eq_one_of_mul ha hd (pow_orderOf_eq_one (a * d))
  have haμ : a * a₀ = a₀ * a := by
    have hda : d * a₀ = a₀ * d := (hLD.commute ha₀ hd).symm
    calc a * a₀ = a * a₀ * d * d⁻¹ := by group
      _ = a * (d * a₀) * d⁻¹ := by rw [hda]; group
      _ = (a * d) * a₀ * d⁻¹ := by group
      _ = a₀ * (a * d) * d⁻¹ := by rw [hyμ]
      _ = a₀ * a := by group
  have ha1 : a = 1 := by
    have hao : orderOf a ∣ orderOf (a * d) := orderOf_dvd_of_pow_eq_one hpow.1
    have hcop : Nat.Coprime (orderOf a) 3 :=
      Nat.Coprime.coprime_dvd_left hao (Nat.Coprime.coprime_dvd_right (by norm_num) hy6)
    have hN : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers a₀ : Set G) :=
      (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_commute haμ)
    have hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers a₀) := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [Nat.card_zpowers, Nat.card_zpowers, hμ3]
      exact hcop
    have hcard := card_sup_eq_mul_of_disjoint hN hdisj
    rw [Nat.card_zpowers, Nat.card_zpowers, hμ3] at hcard
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers a₀ ≤ L :=
      sup_le ((Subgroup.zpowers_le).mpr ha) ((Subgroup.zpowers_le).mpr ha₀)
    set H := (Subgroup.zpowers a ⊔ Subgroup.zpowers a₀).subgroupOf L with hHdef
    have hHcard : Nat.card H = orderOf a * 3 := by
      rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
    have hodd : Odd (Nat.card H) := by
      rw [hHcard]
      exact (Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_left hao
        (Nat.Coprime.coprime_dvd_right (by norm_num) hy6))).mul (by decide)
    rcases card_dvd_of_odd_of_psl24 eL hodd with h3 | h5
    · rw [hHcard] at h3
      have : orderOf a = 1 := by
        have := Nat.le_of_dvd (by norm_num) h3
        have hpos := orderOf_pos a
        omega
      exact orderOf_eq_one_iff.mp this
    · rw [hHcard] at h5
      exfalso
      have := (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5
      omega
  rw [ha1, one_mul] at hy6 ⊢
  exact s.mem_Q_of_mem_D_of_odd hp hQD hD hd
    (Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) hy6))

omit h3Q in
theorem card_dvd_of_odd
    {X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (s.Q : Set G))
    (hXodd : Odd (Nat.card X))
    (hXQ : Nat.Coprime (Nat.card X) (Nat.card s.Q)) :
    Nat.card X ∣ 3 ∨ Nat.card X ∣ 5 := by
  classical
  rcases s.lemma_4_4 hp hS with h1 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  · left
    have hdvd := Subgroup.card_dvd_of_le (h1 ▸ hXN)
    rw [s.card_normalizer_T hp] at hdvd
    have h2 : Nat.Coprime (Nat.card X) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.symm (Nat.coprime_two_left.mpr hXodd))
    have h3 : Nat.card X ∣ 3 * Nat.card s.Q := by
      have : 24 * Nat.card s.Q = 8 * (3 * Nat.card s.Q) := by ring
      rw [this] at hdvd
      exact h2.dvd_of_dvd_mul_left hdvd
    exact hXQ.dvd_of_dvd_mul_right h3
  have hXL : X ≤ L := by
    intro x hx
    obtain ⟨a, ha, d, hd, rfl⟩ := hLD.exists_mul (hXN hx)
    have hpow := hLD.pow_eq_one_of_mul ha hd (pow_orderOf_eq_one (a * d))
    have hdo : orderOf d ∣ orderOf (a * d) := orderOf_dvd_of_pow_eq_one hpow.2
    have hxX : orderOf (a * d) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
    have hdQ : d ∈ s.Q := s.mem_Q_of_mem_D_of_odd hp hQD hD hd
      (Odd.of_dvd_nat hXodd (hdo.trans hxX))
    have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hXQ
      (hdo.trans hxX) (Subgroup.orderOf_dvd_natCard _ hdQ))
    rw [hd1, mul_one]
    exact ha
  have hc := card_dvd_of_odd_of_psl24 eL (H := X.subgroupOf L) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv]
    exact hXodd)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv] at hc

omit h3Q in
theorem card_dvd_of_le_normalizer
    {g : G} {K : Subgroup G}
    (hK : K ≤ s.Q.map (MulAut.conj g).toMonoidHom) (hK1 : K ≠ ⊥) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hXodd : Odd (Nat.card X))
    (hXQ : Nat.Coprime (Nat.card X) (Nat.card s.Q)) :
    Nat.card X ∣ 3 ∨ Nat.card X ∣ 5 := by
  set K' := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'def
  have hK'Q : K' ≤ s.Q := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hK hx
    have : (MulAut.conj g⁻¹) ((MulAut.conj g) y) = y := by
      simp [MulAut.conj_apply, mul_assoc]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [this]
    exact hy
  have hK'1 : K' ≠ ⊥ := by
    rw [Ne, hK'def, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
    exact hK1
  have hN := s.lemma_4_3 hp hS hK'Q hK'1
  set X' := X.map (MulAut.conj g⁻¹).toMonoidHom with hX'def
  have hX'card : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hX'N : X' ≤ Subgroup.normalizer (s.Q : Set G) := by
    rw [← hN]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.le_normalizer_map _ ⟨x, hXN hx, rfl⟩
  have := s.card_dvd_of_odd hp hS hX'N (hX'card ▸ hXodd) (hX'card ▸ hXQ)
  rwa [hX'card] at this

end Setup

end CFSG.Walter.JT
