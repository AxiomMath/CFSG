module

public import CFSG.Walter.ReeOrder.JT.Section7V
public import CFSG.Walter.ReeOrder.JT.Ward

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_normal_complement_of_le_centralizer {r : ℕ} [Fact r.Prime] (P : Sylow r X)
    (hP : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    ∃ K : Subgroup X, K.Normal ∧ ¬ r ∣ Nat.card K ∧
      (∀ g : X, Nat.Coprime (orderOf g) r → g ∈ K) ∧
      Nat.card K * Nat.card (P : Subgroup X) = Nat.card X := by
  refine ⟨(MonoidHom.transferSylow P hP).ker, inferInstance,
    MonoidHom.not_dvd_card_ker_transferSylow P hP, ?_,
    (MonoidHom.ker_transferSylow_isComplement' P hP).card_mul_card⟩
  intro g hg
  rw [MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := P.isPGroup' (MonoidHom.transferSylow P hP g)
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 := orderOf_map_dvd (MonoidHom.transferSylow P hP) g
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hg.pow_right k) h2 h1)

end General

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp3 : h.p = 3)
include hp3

theorem not_three_dvd_card_centralizer_T :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (s.T : Set G)) := by
  have hp := h.p_ne_two_of_eq_three hp3
  rw [s.card_centralizer_T hp]
  intro h3
  exact s.three_not_dvd_card_Q hp3
    (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 8) h3)

theorem eq_one_of_mem_centralizer_T
    {H : Subgroup G} (hH : IsPGroup 3 H) {z : G} (hzH : z ∈ H)
    (hzT : z ∈ Subgroup.centralizer (s.T : Set G)) : z = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨z, hzH⟩
  have h1 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hk)
  have h2 := Subgroup.orderOf_dvd_natCard _ hzT
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Subgroup.centralizer (s.T : Set G))) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (s.not_three_dvd_card_centralizer_T hp3))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem not_mem_centralizer_T_of_orderOf
    {μ : G} (hμ3 : orderOf μ = 3) :
    μ ∉ Subgroup.centralizer (s.T : Set G) := fun hμ =>
  s.not_three_dvd_card_centralizer_T hp3 (hμ3 ▸ Subgroup.orderOf_dvd_natCard _ hμ)

theorem exists_zpow_mul_eq
    {μ : G} (hμT : μ ∈ Subgroup.normalizer (s.T : Set G))
    (hμ3 : orderOf μ = 3) {g : G} (hg : g ∈ Subgroup.normalizer (s.T : Set G)) :
    ∃ k : ℤ, ∃ y ∈ Subgroup.centralizer (s.T : Set G), g = μ ^ k * y := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hle : Subgroup.zpowers μ ≤
      Subgroup.normalizer ((Subgroup.centralizer (s.T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun y hy => s.conj_mem_centralizer_T hμT hy
  rw [s.normalizer_T_eq_sup hp hμT (s.not_mem_centralizer_T_of_orderOf hp3 hμ3),
    ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hg
  obtain ⟨a, ha, y, hy, hgay⟩ := hg
  simp only at hgay
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨k, y, hy, hgay.symm⟩

theorem commute_of_mem_normalizer
    {μ : G} (hμT : μ ∈ Subgroup.normalizer (s.T : Set G))
    (hμ3 : orderOf μ = 3) {H : Subgroup G} (hH : IsPGroup 3 H) (hμH : μ ∈ H) {g : G}
    (hgT : g ∈ Subgroup.normalizer (s.T : Set G)) (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    g * μ = μ * g := by
  obtain ⟨k, y, hy, rfl⟩ := s.exists_zpow_mul_eq hp3 hμT hμ3 hgT
  have hyH : y ∈ Subgroup.normalizer (H : Set G) := by
    have : y = μ ^ (-k) * (μ ^ k * y) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (H.zpow_mem hμH _)) hgH
  have hc : y * μ * y⁻¹ * μ⁻¹ = 1 := by
    refine s.eq_one_of_mem_centralizer_T hp3 hH ?_ ?_
    · exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp hyH μ).mp hμH) (H.inv_mem hμH)
    · have : y * μ * y⁻¹ * μ⁻¹ = y * (μ * y⁻¹ * μ⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy (s.conj_mem_centralizer_T hμT (Subgroup.inv_mem _ hy))
  have hyμ : y * μ = μ * y := by
    calc y * μ = (y * μ * y⁻¹ * μ⁻¹) * μ * y := by group
      _ = μ * y := by rw [hc, one_mul]
  calc μ ^ k * y * μ = μ ^ k * (y * μ) := by group
    _ = μ ^ k * (μ * y) := by rw [hyμ]
    _ = μ * (μ ^ k * y) := by group

theorem exists_zpow_mul_mem_Q
    {μ : G} (hμT : μ ∈ Subgroup.normalizer (s.T : Set G))
    (hμ3 : orderOf μ = 3) {g : G} (hgT : g ∈ Subgroup.normalizer (s.T : Set G))
    (hgμ : g * μ = μ * g) (hg : Odd (orderOf g)) : ∃ k : ℤ, μ ^ k * g ∈ s.Q := by
  have hp := h.p_ne_two_of_eq_three hp3
  obtain ⟨k, y, hy, rfl⟩ := s.exists_zpow_mul_eq hp3 hμT hμ3 hgT
  refine ⟨-k, ?_⟩
  have hc : Commute (μ ^ (-k)) (μ ^ k * y) := Commute.zpow_left (hgμ.symm : Commute μ _) (-k)
  have h1 := hc.orderOf_mul_dvd_lcm
  have hy' : μ ^ (-k) * (μ ^ k * y) = y := by group
  rw [hy'] at h1 ⊢
  rw [s.mem_Q_iff hp]
  refine ⟨hy, ?_⟩
  have h3 : orderOf (μ ^ (-k)) ∣ 3 := by
    rw [← hμ3]
    exact orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
  have h4 : (orderOf (μ ^ (-k))).lcm (orderOf (μ ^ k * y)) ∣ 3 * orderOf (μ ^ k * y) :=
    (Nat.lcm_dvd_mul _ _).trans (Nat.mul_dvd_mul_right h3 _)
  exact Odd.of_dvd_nat (Odd.mul (by decide) hg) (h1.trans h4)

theorem mem_Q_of_coprime
    {z : G} (hz : z ∈ Subgroup.normalizer (s.T : Set G))
    (hz6 : Nat.Coprime (orderOf z) 6) : z ∈ s.Q := by
  have hp := h.p_ne_two_of_eq_three hp3
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

theorem le_Q_of_isPGroup
    (hS : SuzukiFourGroupTheorem) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : Nat.Coprime ℓ 6) {L : Subgroup G} (hL : IsPGroup ℓ L) {x : G} (hxQ : x ∈ s.Q)
    (hx1 : x ≠ 1) (hxL : x ∈ L) : L ≤ s.Q := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hNQ := s.lemma_7_1_b hp3 hS
  have hL6 : ∀ w ∈ L, Nat.Coprime (orderOf w) 6 := by
    intro w hw
    obtain ⟨k, hk⟩ := hL ⟨w, hw⟩
    have h1 : orderOf w ∣ ℓ ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    exact Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ hℓ)
  have hN : ∀ y ∈ s.Q, y ≠ 1 → Subgroup.normalizer (Subgroup.zpowers y : Set G) =
      Subgroup.normalizer (s.T : Set G) := by
    intro y hyQ hy1
    rw [s.lemma_4_3 hp hS ((Subgroup.zpowers_le).mpr hyQ)
      (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hy1), hNQ]
  have : Nontrivial L := ⟨⟨⟨x, hxL⟩, 1, fun h0 => hx1 (congrArg Subtype.val h0)⟩⟩
  have := hL.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center L)
  have hzx : ((z : L) : G) * x = x * ((z : L) : G) :=
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x, hxL⟩)).symm
  have hz'1 : ((z : L) : G) ≠ 1 := fun h0 => hz1 (Subtype.ext (Subtype.ext h0))
  have hz'T : ((z : L) : G) ∈ Subgroup.normalizer (s.T : Set G) := by
    rw [← hN x hxQ hx1]
    exact mem_normalizer_zpowers_of_commute hzx
  have hz'Q : ((z : L) : G) ∈ s.Q := s.mem_Q_of_coprime hp3 hz'T (hL6 _ (z : L).2)
  intro w hw
  have hwz : w * ((z : L) : G) = ((z : L) : G) * w :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩)
  have hwT : w ∈ Subgroup.normalizer (s.T : Set G) := by
    rw [← hN _ hz'Q hz'1]
    exact mem_normalizer_zpowers_of_commute hwz
  exact s.mem_Q_of_coprime hp3 hwT (hL6 w hw)

end Setup

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_12_a :
    Lemma712a h := by
  classical
  intro s μ hμQ hμ3 x₀ hx₀Q hx₀μ
  by_contra hx₀1
  have hp := h.p_ne_two_of_eq_three hp3
  have hS := CFSG.Walter.suzukiFourGroupTheorem
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNQ := s.lemma_7_1_b hp3 hS
  have hμT : μ ∈ Subgroup.normalizer (s.T : Set G) := hNQ ▸ hμQ
  have hQT : s.Q ≤ Subgroup.normalizer (s.T : Set G) :=
    s.Q_le_centralizer_T.trans s.centralizer_T_le_normalizer_T
  have hQc : ∀ y ∈ s.Q, ∀ z ∈ s.Q, y * z = z * y := by
    have := s.isCyclic_Q hp
    intro y hy z hz
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := s.Q)).mul_comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hμ1 : μ ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hμ3
    norm_num at hμ3
  have hx₀o1 : orderOf x₀ ≠ 1 := fun h0 => hx₀1 (orderOf_eq_one_iff.mp h0)
  obtain ⟨ℓ, hℓp, hℓdvd⟩ : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ orderOf x₀ :=
    ⟨_, Nat.minFac_prime hx₀o1, Nat.minFac_dvd _⟩
  have : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨x, hxQ, hxμ, hxo⟩ : ∃ x ∈ s.Q, x * μ = μ * x ∧ orderOf x = ℓ :=
    ⟨x₀ ^ (orderOf x₀ / ℓ), s.Q.pow_mem hx₀Q _,
      (Commute.pow_left (hx₀μ.symm : Commute x₀ μ) _).eq,
      orderOf_pow_orderOf_div (orderOf_pos x₀).ne' hℓdvd⟩
  have hx1 : x ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hxo
    exact hℓp.one_lt.ne hxo
  have hℓQ : ℓ ∣ Nat.card s.Q := hxo ▸ Subgroup.orderOf_dvd_natCard _ hxQ
  have hℓ2 : ℓ ≠ 2 := by
    intro h2
    rw [h2] at hℓQ
    exact (Nat.not_even_iff_odd.mpr (s.odd_card_Q hp)) (even_iff_two_dvd.mpr hℓQ)
  have hℓ3 : ℓ ≠ 3 := fun h3 => s.three_not_dvd_card_Q hp3 (h3 ▸ hℓQ)
  have hℓ6 : Nat.Coprime ℓ 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hℓp Nat.prime_two).mpr hℓ2)
      ((Nat.coprime_primes hℓp Nat.prime_three).mpr hℓ3)
  have hℓ3' : Nat.Coprime 3 ℓ := (Nat.coprime_primes Nat.prime_three hℓp).mpr (Ne.symm hℓ3)
  have hxN : Subgroup.normalizer (Subgroup.zpowers x : Set G) =
      Subgroup.normalizer (s.T : Set G) := by
    rw [s.lemma_4_3 hp hS ((Subgroup.zpowers_le).mpr hxQ)
      (by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1), hNQ]
  set Fam : Set (Subgroup G) :=
    {H | IsPGroup 3 H ∧ μ ∈ H ∧ x ∈ Subgroup.normalizer (H : Set G)} with hFam
  have hFne : Fam.Nonempty := by
    refine ⟨Subgroup.zpowers μ, ?_, Subgroup.mem_zpowers μ,
      mem_normalizer_zpowers_of_commute hxμ⟩
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hμ3, pow_one] :
      Nat.card (Subgroup.zpowers μ) = 3 ^ 1)
  obtain ⟨P, ⟨hP3, hμP, hxP⟩, hPmax⟩ :=
    Set.exists_max_image Fam (fun H => Nat.card H) (Set.toFinite _) hFne
  have hP1 : P ≠ ⊥ := fun h0 => hμ1 (by rw [h0] at hμP; exact Subgroup.mem_bot.mp hμP)
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hcommP : ∀ g ∈ Subgroup.normalizer (s.T : Set G), g ∈ N → g * μ = μ * g :=
    fun g hgT hgN => s.commute_of_mem_normalizer hp3 hμT hμ3 hP3 hμP hgT hgN
  obtain ⟨n, hn⟩ := hP3.exists_card_eq
  have hsyl : ¬ 3 ^ (n + 1) ∣ Nat.card G := by
    intro hdvd
    have hNdvd : 3 ^ (n + 1) ∣ Nat.card N := Sylow.prime_pow_dvd_card_normalizer hdvd hn
    have hNs : Group.IsSolvable N := h.isSolvable_normalizer_of_isPGroup_three hp3 hP3 hP1
    set π : Set Nat.Primes := {⟨3, Nat.prime_three⟩, ⟨ℓ, hℓp⟩} with hπ
    set XP := Subgroup.zpowers x ⊔ P with hXPdef
    have hXPN : XP ≤ N := sup_le ((Subgroup.zpowers_le).mpr hxP) hPN
    have hXPcard : Nat.card XP = ℓ * 3 ^ n := by
      have hdisj : Disjoint (Subgroup.zpowers x) P := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [Nat.card_zpowers, hxo, hn]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓp Nat.prime_three).mpr hℓ3)
      rw [hXPdef, card_sup_eq_mul_of_disjoint ((Subgroup.zpowers_le).mpr hxP) hdisj,
        Nat.card_zpowers, hxo, hn]
    have hXPπ : IsPiSubgroup π (XP.subgroupOf N) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXPN).toEquiv, hXPcard] at hr
      rcases (Nat.Prime.dvd_mul r.2).mp hr with h1 | h1
      · right
        exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 hℓp).mp h1)
      · left
        exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_three).mp
          (r.2.dvd_of_dvd_pow h1))
    obtain ⟨M', hM', hXPM'⟩ := SolvableHall.solvable_hall_containment hNs π _ hXPπ
    set M := M'.map N.subtype with hMdef
    have hMN : M ≤ N := Subgroup.map_subtype_le M'
    have hMcard : Nat.card M = Nat.card M' := Subgroup.card_map_of_injective N.subtype_injective
    have hXPM : XP ≤ M := fun y hy =>
      ⟨⟨y, hXPN hy⟩, hXPM' (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩
    have hxM : x ∈ M := hXPM (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    have hPM : P ≤ M := le_sup_right.trans hXPM
    have hMπ : ∀ r : ℕ, r.Prime → r ∣ Nat.card M → r = 3 ∨ r = ℓ := by
      intro r hr hrd
      rw [hMcard] at hrd
      rcases hM'.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrd with h1 | h1
      · left; exact congrArg Subtype.val h1
      · right; exact congrArg Subtype.val h1
    have hModd : Odd (Nat.card M) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      rcases hMπ 2 Nat.prime_two h2 with h1 | h1
      · omega
      · exact hℓ2 h1.symm
    have hMdvd : 3 ^ (n + 1) ∣ Nat.card M := by
      have hidx : ¬ 3 ∣ M'.index := fun hd =>
        hM'.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ hd (Or.inl rfl)
      have h1 : 3 ^ (n + 1) ∣ Nat.card M' * M'.index := by
        rw [M'.card_mul_index]
        exact hNdvd
      rw [hMcard]
      exact Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)) h1
    set xM : M := ⟨x, hxM⟩ with hxMdef
    obtain ⟨Λ, hΛx⟩ : ∃ Λ : Sylow ℓ M, Subgroup.zpowers xM ≤ Λ :=
      IsPGroup.exists_le_sylow (IsPGroup.of_card (by
        rw [Nat.card_zpowers, hxMdef, Subgroup.orderOf_mk, hxo, pow_one] :
          Nat.card (Subgroup.zpowers xM) = ℓ ^ 1))
    set Λ' := (Λ : Subgroup M).map M.subtype with hΛ'def
    have hxΛ' : x ∈ Λ' := ⟨xM, hΛx (Subgroup.mem_zpowers xM), rfl⟩
    have hΛ'Q : Λ' ≤ s.Q :=
      s.le_Q_of_isPGroup hp3 hS hℓ6 (Λ.isPGroup'.map M.subtype) hxQ hx1 hxΛ'
    have hΛ'1 : Λ' ≠ ⊥ := fun h0 => hx1 (by rw [h0] at hxΛ'; exact Subgroup.mem_bot.mp hxΛ')
    have hNΛ' : Subgroup.normalizer (Λ' : Set G) = Subgroup.normalizer (s.T : Set G) := by
      rw [s.lemma_4_3 hp hS hΛ'Q hΛ'1, hNQ]
    have hΛc : Subgroup.normalizer ((Λ : Subgroup M) : Set M) ≤
        Subgroup.centralizer ((Λ : Subgroup M) : Set M) := by
      intro m hm
      have hmT : (m : G) ∈ Subgroup.normalizer (s.T : Set G) := by
        rw [← hNΛ']
        exact Subgroup.le_normalizer_map M.subtype ⟨m, hm, rfl⟩
      have hmμ := hcommP _ hmT (hMN m.2)
      have hmodd : Odd (orderOf (m : G)) := by
        rw [Subgroup.orderOf_coe]
        exact Odd.of_dvd_nat hModd (orderOf_dvd_natCard m)
      obtain ⟨k, hk⟩ := s.exists_zpow_mul_mem_Q hp3 hμT hμ3 hmT hmμ hmodd
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlQ : (l : G) ∈ s.Q := hΛ'Q ⟨l, hl, rfl⟩
      have hlμ : (l : G) * μ = μ * l := hcommP _ (hQT hlQ) (hMN l.2)
      have hlμk : (l : G) * μ ^ (-k) = μ ^ (-k) * l :=
        (Commute.zpow_right (hlμ : Commute (l : G) μ) (-k)).eq
      apply Subtype.ext
      show (l : G) * m = m * l
      set z := μ ^ k * (m : G) with hzdef
      have hm' : (m : G) = μ ^ (-k) * z := by rw [hzdef]; group
      rw [hm']
      calc (l : G) * (μ ^ (-k) * z) = ((l : G) * μ ^ (-k)) * z := by group
        _ = μ ^ (-k) * ((l : G) * z) := by rw [hlμk]; group
        _ = μ ^ (-k) * (z * l) := by rw [hQc _ hlQ _ hk]
        _ = μ ^ (-k) * z * l := by group
    obtain ⟨K, hKn, hKℓ, hKmem, hKcard⟩ := exists_normal_complement_of_le_centralizer Λ hΛc
    set KG := K.map M.subtype with hKGdef
    have hKGcard : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective M.subtype_injective
    have hK3 : IsPGroup 3 KG := by
      refine IsPGroup.of_card (n := (Nat.card K).primeFactorsList.length) ?_
      rw [hKGcard]
      refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {d} hd hdK => ?_)
      have hdM : d ∣ Nat.card M := hdK.trans (Dvd.intro _ hKcard)
      rcases hMπ d hd hdM with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hdK) hKℓ
    have hμK : μ ∈ KG := by
      refine ⟨⟨μ, hPM hμP⟩, hKmem _ ?_, rfl⟩
      rw [Subgroup.orderOf_mk, hμ3]
      exact hℓ3'
    have hxK : x ∈ Subgroup.normalizer (KG : Set G) :=
      Subgroup.le_normalizer_map M.subtype ⟨xM, by
        have := hKn
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _, rfl⟩
    have hKdvd : 3 ^ (n + 1) ∣ Nat.card KG := by
      rw [hKGcard]
      have hΛcop : Nat.Coprime (3 ^ (n + 1)) (Nat.card (Λ : Subgroup M)) := by
        obtain ⟨b, hb⟩ := Λ.isPGroup'.exists_card_eq
        rw [hb]
        exact Nat.Coprime.pow _ _ hℓ3'
      refine hΛcop.dvd_of_dvd_mul_right ?_
      rw [hKcard]
      exact hMdvd
    have hle : Nat.card KG ≤ Nat.card P := hPmax KG ⟨hK3, hμK, hxK⟩
    rw [hn] at hle
    have h1 := Nat.le_of_dvd Nat.card_pos hKdvd
    have h2 : 3 ^ n < 3 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨Pst, hPPst⟩ := hP3.exists_le_sylow
  have hPeq : P = Pst := by
    refine Subgroup.eq_of_le_of_card_ge hPPst ?_
    obtain ⟨v, hv⟩ := Pst.isPGroup'.exists_card_eq
    rw [hv, hn]
    have hnv : 3 ^ n ∣ 3 ^ v := by
      have := Subgroup.card_dvd_of_le hPPst
      rwa [hn, hv] at this
    have hnv' : n ≤ v := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hnv
    by_contra hlt
    have hvn : n + 1 ≤ v := by
      have : n ≠ v := fun h0 => hlt (by rw [h0])
      omega
    have := Subgroup.card_subgroup_dvd_card (Pst : Subgroup G)
    rw [hv] at this
    exact hsyl ((pow_dvd_pow 3 hvn).trans this)
  have hfixP : ∀ y ∈ P, x * y = y * x → y ∈ Subgroup.zpowers μ := by
    intro y hyP hyx
    have hyT : y ∈ Subgroup.normalizer (s.T : Set G) := by
      rw [← hxN]
      exact mem_normalizer_zpowers_of_commute hyx.symm
    have hyμ := hcommP y hyT (hPN hyP)
    have hyodd : Odd (orderOf y) := by
      obtain ⟨k, hk⟩ := hP3 ⟨y, hyP⟩
      have : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
        simpa using congrArg Subtype.val hk)
      exact Odd.of_dvd_nat (Odd.pow (by decide)) this
    obtain ⟨k, hk⟩ := s.exists_zpow_mul_mem_Q hp3 hμT hμ3 hyT hyμ hyodd
    have h1 : μ ^ k * y = 1 := s.eq_one_of_mem_centralizer_T hp3 hP3
      (P.mul_mem (P.zpow_mem hμP k) hyP) (s.Q_le_centralizer_T hk)
    have : y = μ ^ (-k) := by
      calc y = μ ^ (-k) * (μ ^ k * y) := by group
        _ = μ ^ (-k) := by rw [h1, mul_one]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers μ) _
  have hxPn : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le).mpr hxP
  let := conjAct (Subgroup.zpowers x) P hxPn
  have hXℓ : IsPGroup ℓ (Subgroup.zpowers x) := IsPGroup.of_card
    (by rw [Nat.card_zpowers, hxo, pow_one] : Nat.card (Subgroup.zpowers x) = ℓ ^ 1)
  have hmod := hXℓ.card_modEq_card_fixedPoints P
  have hfix_iff : ∀ y : P, y ∈ MulAction.fixedPoints (Subgroup.zpowers x) P ↔
      (y : G) ∈ Subgroup.zpowers μ := by
    intro y
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hy
      have h1 : x * (y : G) * x⁻¹ = y := congrArg Subtype.val (hy ⟨x, Subgroup.mem_zpowers x⟩)
      refine hfixP y y.2 ?_
      calc x * (y : G) = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h1]
    · intro hy g
      apply Subtype.ext
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      change (g : G) * y * (g : G)⁻¹ = y
      rw [← hi, ← hj]
      have hc : Commute (x ^ i) (μ ^ j) :=
        (Commute.zpow_left (hxμ : Commute x μ) i).zpow_right j
      rw [hc.eq, mul_inv_cancel_right]
  have hfixcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) P) = 3 := by
    have hμPle : Subgroup.zpowers μ ≤ P := (Subgroup.zpowers_le).mpr hμP
    rw [← hμ3, ← Nat.card_zpowers]
    exact Nat.card_congr
      { toFun := fun y => ⟨((y.1 : P) : G), (hfix_iff y.1).mp y.2⟩
        invFun := fun z => ⟨⟨(z : G), hμPle z.2⟩, (hfix_iff _).mpr z.2⟩
        left_inv := fun y => rfl
        right_inv := fun z => rfl }
  obtain ⟨c⟩ := h.nonempty_torusConf hp3
  obtain ⟨m, -, hm⟩ := h.lemma_7_11_b hp3 c Pst
  rw [← hPeq] at hm
  rw [hfixcard, hm] at hmod
  have hq1 : ℓ ∣ h.q + 1 := by
    have h4 := s.four_mul_card_Q hp
    rw [h.eps_eq_one_of_eq_three hp3] at h4
    have : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4
    rw [← this]
    exact Dvd.dvd.mul_left hℓQ 4
  have hd1 : (ℓ : ℤ) ∣ 3 - (h.q : ℤ) ^ m := by
    have := Nat.modEq_iff_dvd.mp hmod
    push_cast at this
    exact this
  have hd2 : (ℓ : ℤ) ∣ (h.q : ℤ) ^ m - (-1) ^ m := by
    have h1 : (ℓ : ℤ) ∣ (h.q : ℤ) - (-1) := by
      rw [sub_neg_eq_add]
      exact_mod_cast Int.natCast_dvd_natCast.mpr hq1
    exact h1.trans (sub_dvd_pow_sub_pow _ _ m)
  have hd3 : (ℓ : ℤ) ∣ 3 - (-1) ^ m := by
    have := dvd_add hd1 hd2
    rwa [sub_add_sub_cancel] at this
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow] at hd3
    have h2 : (ℓ : ℤ) ∣ 2 := by simpa using hd3
    have h2' : ℓ ∣ 2 := by exact_mod_cast h2
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).mp h2')
  · rw [ho.neg_one_pow] at hd3
    have h4 : (ℓ : ℤ) ∣ 4 := by simpa using hd3
    have h4' : ℓ ∣ 2 ^ 2 := by exact_mod_cast h4
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).mp (hℓp.dvd_of_dvd_pow h4'))

end JTHyp

end CFSG.Walter.JT
