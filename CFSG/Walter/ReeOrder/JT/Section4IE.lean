module

public import CFSG.Walter.ReeOrder.JT.Section4ID
public import CFSG.Walter.ReeOrder.JT.Section4IC
public import CFSG.Walter.ReeOrder.JT.Section7Z

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mul_self_of_odd {y : X} (hy : y * y = 1) (hodd : Odd (orderOf y)) : y = 1 := by
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite X] in
theorem conj_commute {x a μ : X} (hxμ : x * μ = μ * x) (haμ : a * μ = μ * a) :
    x⁻¹ * a * x * μ = μ * (x⁻¹ * a * x) :=
  (((Commute.inv_left (hxμ : Commute x μ)).mul_left (haμ : Commute a μ)).mul_left hxμ).eq

theorem exists_conj_le_of_isPiSubgroup {M R U : Subgroup X} (hsolv : Group.IsSolvable M)
    {π : Set Nat.Primes} (hR : IsHallSubgroup π (R.subgroupOf M)) (hUM : U ≤ M)
    (hU : IsPiSubgroup π U) : ∃ g ∈ M, ∀ u ∈ U, g⁻¹ * u * g ∈ R := by
  have hU' : IsPiSubgroup π (U.subgroupOf M) := fun r hr =>
    hU r (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hr)
  obtain ⟨H, hH, hUH⟩ := SolvableHall.solvable_hall_containment hsolv π _ hU'
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hR hH
  refine ⟨g, g.2, fun u hu => ?_⟩
  have hmem : (⟨u, hUM hu⟩ : M) ∈ H := hUH (by rw [Subgroup.mem_subgroupOf]; exact hu)
  rw [hg] at hmem
  obtain ⟨r, hr, hru⟩ := hmem
  have hr' : (r : X) ∈ R := hr
  have hru' : (g : X) * r * (g : X)⁻¹ = u := by
    have := congrArg Subtype.val hru
    simpa [MulAut.conj_apply] using this
  rw [← hru']
  simpa [mul_assoc] using hr'

end General

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem)
include hp hS

theorem conj_mem_normalizer_Q
    {K : Subgroup G} {x : G} (hKQ : ∀ k ∈ K, x⁻¹ * k * x ∈ s.Q)
    (hK1 : K ≠ ⊥) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    x⁻¹ * y * x ∈ Subgroup.normalizer (s.Q : Set G) := by
  set K' := K.map (MulAut.conj x⁻¹).toMonoidHom with hK'def
  have hK'Q : K' ≤ s.Q := by
    rintro _ ⟨k, hk, rfl⟩
    have := hKQ k hk
    simpa [MulAut.conj_apply] using this
  have hK'1 : K' ≠ ⊥ := by
    rw [Ne, hK'def, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x⁻¹).injective]
    exact hK1
  rw [← s.lemma_4_3 hp hS hK'Q hK'1]
  refine mem_normalizer_of_conj_mem fun z hz => ?_
  obtain ⟨k, hk, rfl⟩ := hz
  have hyk : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hy k).mp hk
  refine ⟨y * k * y⁻¹, hyk, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

variable (h3Q : ¬ 3 ∣ Nat.card s.Q)
include h3Q

theorem mem_zpowers_of_commute
    {μ : G} (hμ : μ ∈ Subgroup.normalizer (s.Q : Set G))
    (hμ3 : orderOf μ = 3) {y : G} (hyN : y ∈ Subgroup.normalizer (s.Q : Set G))
    (hyμ : y * μ = μ * y) (hyodd : Odd (orderOf y))
    (hyQ : Nat.Coprime (orderOf y) (Nat.card s.Q)) : y ∈ Subgroup.zpowers μ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hb1 : b = 1 := by
    have hyo : orderOf (y ^ 3 ^ a) = b := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨b, hab⟩, hab]
      exact Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)
    have hodd : Odd b := Odd.of_dvd_nat hyodd ⟨3 ^ a, by rw [hab, mul_comm]⟩
    have h6 : Nat.Coprime b 6 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.coprime_two_left.mpr hodd))
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb))
    have hmem := s.mem_Q_of_commute hp hS h3Q hμ hμ3 (Subgroup.pow_mem _ hyN _)
      (((Commute.pow_left (hyμ : Commute y μ) _)).eq) (hyo ▸ h6)
    have h1 : b ∣ Nat.card s.Q := hyo ▸ Subgroup.orderOf_dvd_natCard _ hmem
    have h2 : b ∣ orderOf y := ⟨3 ^ a, by rw [hab, mul_comm]⟩
    exact Nat.eq_one_of_dvd_coprimes hyQ h2 h1
  rw [hb1, mul_one] at hab
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers μ : Set G) :=
    (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_commute hyμ)
  have hP : IsPGroup 3 (Subgroup.zpowers y ⊔ Subgroup.zpowers μ : Subgroup G) := by
    have h3a : IsPGroup 3 (Subgroup.zpowers y) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hab])
    have h3μ : IsPGroup 3 (Subgroup.zpowers μ) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hμ3, pow_one] :
        Nat.card (Subgroup.zpowers μ) = 3 ^ 1)
    exact h3a.to_sup_of_normal_right' h3μ hN
  have hPN : Subgroup.zpowers y ⊔ Subgroup.zpowers μ ≤ Subgroup.normalizer (s.Q : Set G) :=
    sup_le ((Subgroup.zpowers_le).mpr hyN) ((Subgroup.zpowers_le).mpr hμ)
  have hle : Nat.card (Subgroup.zpowers y ⊔ Subgroup.zpowers μ : Subgroup G) ≤ 3 := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le hPN
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact s.not_nine_dvd_card_normalizer_Q hp hS h3Q
        ((show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hdvd)
    interval_cases k <;> norm_num
  have heq : Subgroup.zpowers y ⊔ Subgroup.zpowers μ = Subgroup.zpowers μ :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right (by
      rw [Nat.card_zpowers, hμ3]; exact hle)).symm
  exact heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem mem_zpowers_of_conj
    {μ : G} (hμ : μ ∈ Subgroup.normalizer (s.Q : Set G))
    (hμ3 : orderOf μ = 3) {K : Subgroup G} {x : G} (hKQ : ∀ k ∈ K, x⁻¹ * k * x ∈ s.Q)
    (hK1 : K ≠ ⊥) (hxμ : x * μ = μ * x) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hyμ : y * μ = μ * y) (hyodd : Odd (orderOf y))
    (hyQ : Nat.Coprime (orderOf y) (Nat.card s.Q)) : y ∈ Subgroup.zpowers μ := by
  have ho : orderOf (x⁻¹ * y * x) = orderOf y := by
    rw [show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
  have hmem := s.mem_zpowers_of_commute hp hS h3Q hμ hμ3
    (s.conj_mem_normalizer_Q hp hS hKQ hK1 hy) (conj_commute hxμ hyμ) (ho ▸ hyodd) (ho ▸ hyQ)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxj : x * μ ^ j * x⁻¹ = μ ^ j := by
    rw [((Commute.zpow_right (hxμ : Commute x μ) j)).eq, mul_inv_cancel_right]
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [← hxj, hj]
  group

theorem commute_of_conj
    {μ : G} (hμ : μ ∈ Subgroup.normalizer (s.Q : Set G))
    (hμ3 : orderOf μ = 3) {K : Subgroup G} {x : G} (hKQ : ∀ k ∈ K, x⁻¹ * k * x ∈ s.Q)
    (hK1 : K ≠ ⊥) (hxμ : x * μ = μ * x) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hyμ : y * μ = μ * y) (hyodd : Odd (orderOf y)) :
    ∀ z ∈ K, z * μ = μ * z → y * z = z * y := by
  intro z hz hzμ
  have ho : orderOf (x⁻¹ * y * x) = orderOf y := by
    rw [show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
  have h := s.commute_of_mem_normalizer_Q hp hS h3Q hμ hμ3
    (s.conj_mem_normalizer_Q hp hS hKQ hK1 hy) (conj_commute hxμ hyμ) (ho ▸ hyodd)
    (x⁻¹ * z * x) (hKQ z hz) (conj_commute hxμ hzμ)
  calc y * z = x * ((x⁻¹ * y * x) * (x⁻¹ * z * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * z * x) * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
    _ = z * y := by group

end Setup

namespace L46Data

variable {h : JTHyp G} {c : Config h} (D : L46Data c)

theorem commute_μ {y : G} (hy : y ∈ D.M) : y * c.μ = c.μ * y := by
  classical
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat D.odd (Subgroup.orderOf_dvd_natCard _ hy)
  exact commute_of_orderOf_three_of_odd c.orderOf_μ hyodd
    ((Subgroup.mem_normalizer_iff.mp (D.M_le hy) c.μ).mp (Subgroup.mem_zpowers _))

theorem t₁_mem_normalizer : c.t₁ ∈ Subgroup.normalizer (D.M : Set G) :=
  D.normal _ (mem_normalizer_zpowers_of_commute c.comm.symm)

theorem t₂_mem_normalizer_zpowers :
    D.t₂ ∈ Subgroup.normalizer (Subgroup.zpowers c.μ : Set G) := by
  have ht₂μ : D.t₂ * c.μ * D.t₂⁻¹ = c.μ⁻¹ := D.inv_L c.μ D.μ_mem_L
  refine mem_normalizer_of_conj_mem fun z hz => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow, ht₂μ, inv_zpow']
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem t₂_mem_normalizer : D.t₂ ∈ Subgroup.normalizer (D.M : Set G) :=
  D.normal _ D.t₂_mem_normalizer_zpowers

theorem orderOf_dvd_m {y : G} (hy : y ∈ D.L) : orderOf y ∣ c.toSetup.m := by
  rw [← D.card_L]
  exact Subgroup.orderOf_dvd_natCard _ hy

theorem inv_props {σ : G} (hσ : σ = D.t₂ ∨ σ = c.t₁ * D.t₂) :
    σ * σ = 1 ∧ σ * c.t₁ = c.t₁ * σ ∧ σ ≠ 1 ∧ σ ≠ c.t₁ ∧
      (∀ y ∈ D.L, σ * y * σ⁻¹ = y⁻¹) ∧ σ ∈ Subgroup.normalizer (D.M : Set G) := by
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have ht₂t₂ : D.t₂ * D.t₂ = 1 := by rw [← pow_two, ← D.orderOf_t₂, pow_orderOf_eq_one]
  have ht₂1 : D.t₂ ≠ 1 := by
    intro h0
    have := D.orderOf_t₂
    rw [h0, orderOf_one] at this
    omega
  rcases hσ with rfl | rfl
  · exact ⟨ht₂t₂, D.comm, ht₂1, D.ne, D.inv_L, D.t₂_mem_normalizer⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc c.t₁ * D.t₂ * (c.t₁ * D.t₂) = c.t₁ * (D.t₂ * c.t₁) * D.t₂ := by group
        _ = c.t₁ * (c.t₁ * D.t₂) * D.t₂ := by rw [D.comm]
        _ = (c.t₁ * c.t₁) * (D.t₂ * D.t₂) := by group
        _ = 1 := by rw [ht₁t₁, ht₂t₂, one_mul]
    · calc c.t₁ * D.t₂ * c.t₁ = c.t₁ * (D.t₂ * c.t₁) := by group
        _ = c.t₁ * (c.t₁ * D.t₂) := by rw [D.comm]
    · intro h0
      apply D.ne
      calc D.t₂ = c.t₁⁻¹ * (c.t₁ * D.t₂) := by group
        _ = c.t₁ := by rw [h0, mul_one, inv_eq_of_mul_eq_one_right ht₁t₁]
    · intro h0
      apply ht₂1
      calc D.t₂ = c.t₁⁻¹ * (c.t₁ * D.t₂) := by group
        _ = 1 := by rw [h0, inv_mul_cancel]
    · intro y hy
      have hyt : y * c.t₁ = c.t₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (D.L_le hy)
      calc c.t₁ * D.t₂ * y * (c.t₁ * D.t₂)⁻¹ = c.t₁ * (D.t₂ * y * D.t₂⁻¹) * c.t₁⁻¹ := by group
        _ = c.t₁ * y⁻¹ * c.t₁⁻¹ := by rw [D.inv_L y hy]
        _ = y⁻¹ := by
          rw [← (Commute.inv_left (hyt : Commute y c.t₁)).eq, mul_inv_cancel_right]
    · exact Subgroup.mul_mem _ D.t₁_mem_normalizer D.t₂_mem_normalizer

theorem eq_one_of_commute {σ : G} (hσ : σ = D.t₂ ∨ σ = c.t₁ * D.t₂) {y : G} (hy : y ∈ D.M)
    (h1 : y * c.t₁ = c.t₁ * y) (h2 : y * σ = σ * y) : y = 1 := by
  have hyL := D.inf_t₁ y hy h1
  have h2' : y * D.t₂ = D.t₂ * y := by
    rcases hσ with rfl | rfl
    · exact h2
    · have : D.t₂ = c.t₁⁻¹ * (c.t₁ * D.t₂) := by group
      rw [this]
      exact ((Commute.inv_right (h1 : Commute y c.t₁)).mul_right (h2 : Commute y _)).eq
  have hinv := D.inv_L y hyL
  rw [← h2', mul_inv_cancel_right] at hinv
  have hyy : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel y
  exact eq_one_of_mul_self_of_odd hyy
    (Odd.of_dvd_nat D.odd (Subgroup.orderOf_dvd_natCard _ hy))

variable (hp : h.p ≠ 2)
include hp

theorem L_le_M : D.L ≤ D.M := by
  have := D.L_cyclic
  intro y hy
  have hyμ : y * c.μ = c.μ * y :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := D.L)).mul_comm ⟨y, hy⟩ ⟨c.μ, D.μ_mem_L⟩)
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat (by rw [D.card_L]; exact c.toSetup.odd_m hp)
    (Subgroup.orderOf_dvd_natCard _ hy)
  exact D.mem y (mem_normalizer_zpowers_of_commute hyμ) hyodd

variable (hS : SuzukiFourGroupTheorem) (h3Q : ¬ 3 ∣ Nat.card c.Q)
include hS h3Q

theorem exists_R
    {x₀ : G} (hx₀Q : x₀ ∈ c.Q) (hx₀μ : c.μ * x₀ = x₀ * c.μ) (hx₀1 : x₀ ≠ 1) :
    ∃ R : Subgroup G, R ≤ D.M ∧ c.t₁ ∈ Subgroup.normalizer (R : Set G) ∧
      D.t₂ ∈ Subgroup.normalizer (R : Set G) ∧ R ≠ ⊥ ∧
      (∀ r : ℕ, r.Prime → r ∣ Nat.card R → r ∣ Nat.card c.Q) ∧
      ∀ U : Subgroup G, U ≤ D.M → (∀ r : ℕ, r.Prime → r ∣ Nat.card U → r ∣ Nat.card c.Q) →
        ∃ y ∈ D.M, ∀ u ∈ U, y⁻¹ * u * y ∈ c.Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable D.M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ D.odd
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have ht₂t₂ : D.t₂ * D.t₂ = 1 := by rw [← pow_two, ← D.orderOf_t₂, pow_orderOf_eq_one]
  have ht₁1 : c.t₁ ≠ 1 := by
    intro h0
    have := c.orderOf_t₁
    rw [h0, orderOf_one] at this
    omega
  have ht₂1 : D.t₂ ≠ 1 := by
    intro h0
    have := D.orderOf_t₂
    rw [h0, orderOf_one] at this
    omega
  have hct : Commute c.t₁ D.t₂ := D.comm.symm
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions c.t₁ D.t₂ ht₁t₁ ht₂t₂ hct with hVdef
  have hV : IsKleinFour V := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ ht₁1 ht₂1 (Ne.symm D.ne) hct
  have hmemV : ∀ y, y ∈ V ↔ y = c.t₁ * D.t₂ ∨ y = c.t₁ ∨ y = D.t₂ ∨ y = 1 := fun y => Iff.rfl
  have ht₁V : c.t₁ ∈ V := (hmemV _).mpr (Or.inr (Or.inl rfl))
  have ht₂V : D.t₂ ∈ V := (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hVM : V ≤ Subgroup.normalizer (D.M : Set G) := fun y hy => by
    rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ D.t₁_mem_normalizer D.t₂_mem_normalizer
    · exact D.t₁_mem_normalizer
    · exact D.t₂_mem_normalizer
    · exact Subgroup.one_mem _
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (hV.card_four.trans (by norm_num))
  have h2M : ¬ 2 ∣ Nat.card D.M := fun h2 =>
    (Nat.not_even_iff_odd.mpr D.odd) (even_iff_two_dvd.mpr h2)
  set π : Set Nat.Primes := {r | (r : ℕ) ∣ Nat.card c.Q} with hπdef
  let := conjAct V D.M hVM
  obtain ⟨P, hPhall, hPinv, -⟩ := SolvableHall.coprime_invariant_hall_containment hV2 h2M hsolv
    π ⊥ (fun r hr => by
      rw [Subgroup.card_bot] at hr
      exact absurd (Nat.le_of_dvd one_pos hr) (not_le.mpr r.2.one_lt))
    (fun _ _ hx => by rw [Subgroup.mem_bot] at hx ⊢; rw [hx, smul_one])
  set R := P.map D.M.subtype with hRdef
  have hRM : R ≤ D.M := Subgroup.map_subtype_le _
  have hRcard : Nat.card R = Nat.card P := Subgroup.card_map_of_injective D.M.subtype_injective
  have hRsub : R.subgroupOf D.M = P :=
    Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective P
  have hRhall : IsHallSubgroup π (R.subgroupOf D.M) := hRsub ▸ hPhall
  have hRπ : ∀ r : ℕ, r.Prime → r ∣ Nat.card R → r ∣ Nat.card c.Q := fun r hr hrR =>
    hPhall.p_in_pi_of_p_dvd_card ⟨r, hr⟩ (by rwa [hRcard] at hrR)
  have hinvR : ∀ v ∈ V, v ∈ Subgroup.normalizer (R : Set G) := by
    intro v hv
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨(⟨v, hv⟩ : V) • z, hPinv ⟨v, hv⟩ z hz, rfl⟩
  have ht₁R := hinvR _ ht₁V
  have ht₂R := hinvR _ ht₂V
  set Qt := c.Q ⊓ Subgroup.centralizer ({c.μ} : Set G) with hQtdef
  have hQtM : Qt ≤ D.M := by
    intro y hy
    have hyμ : y * c.μ = c.μ * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyodd : Odd (orderOf y) := Odd.of_dvd_nat (c.toSetup.odd_card_Q hp)
      (Subgroup.orderOf_dvd_natCard _ hy.1)
    exact D.mem y (mem_normalizer_zpowers_of_commute hyμ) hyodd
  have hQtπ : IsPiSubgroup π Qt := fun r hr => hr.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hx₀Qt : x₀ ∈ Qt := ⟨hx₀Q, Subgroup.mem_centralizer_singleton_iff.mpr hx₀μ.symm⟩
  have hQt1 : Qt ≠ ⊥ := fun h0 => hx₀1 (by rw [h0] at hx₀Qt; exact Subgroup.mem_bot.mp hx₀Qt)
  have hRfix : ∀ y ∈ R, c.t₁ * y * c.t₁⁻¹ = y → y = 1 := by
    intro y hy hyt
    have hyt' : y * c.t₁ = c.t₁ * y := by
      calc y * c.t₁ = c.t₁ * y * c.t₁⁻¹ * c.t₁ := by rw [hyt]
        _ = c.t₁ * y := by group
    have h1 : orderOf y ∣ c.toSetup.m := D.orderOf_dvd_m (D.inf_t₁ y (hRM hy) hyt')
    have h2 : Nat.Coprime (orderOf y) c.toSetup.m := by
      refine Nat.coprime_of_dvd fun r hr hry hrm => ?_
      have hrQ := hRπ r hr (hry.trans (Subgroup.orderOf_dvd_natCard _ hy))
      exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (c.toSetup.coprime_m_card_Q hp) hrm hrQ)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)
  have hRc := commute_of_fpf_involution ht₁t₁ ht₁R hRfix
  obtain ⟨g, hgM, hg⟩ := exists_conj_le_of_isPiSubgroup hsolv hRhall hQtM hQtπ
  have hμN : c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT
  have hcop6 : Nat.Coprime (Nat.card c.Q) 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.coprime_two_left.mpr
      (c.toSetup.odd_card_Q hp)))
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q))
  have hRQ : ∀ y ∈ R, g * y * g⁻¹ ∈ c.Q := by
    intro y hy
    have hyM : g * y * g⁻¹ ∈ D.M := D.M.mul_mem (D.M.mul_mem hgM (hRM hy)) (D.M.inv_mem hgM)
    have hyN : g * y * g⁻¹ ∈ Subgroup.normalizer (Qt : Set G) := by
      refine mem_normalizer_of_conj_mem fun u hu => ?_
      have hcomm : y * (g⁻¹ * u * g) = (g⁻¹ * u * g) * y := hRc y hy _ (hg u hu)
      have : g * y * g⁻¹ * u * (g * y * g⁻¹)⁻¹ = u := by
        calc g * y * g⁻¹ * u * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * u * g)) * y⁻¹ * g⁻¹ := by
              group
          _ = g * ((g⁻¹ * u * g) * y) * y⁻¹ * g⁻¹ := by rw [hcomm]
          _ = u := by group
      rw [this]
      exact hu
    rw [c.toSetup.lemma_4_3 hp hS inf_le_left hQt1] at hyN
    have ho : orderOf (g * y * g⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have h6 : Nat.Coprime (orderOf (g * y * g⁻¹)) 6 := by
      rw [ho]
      refine Nat.coprime_of_dvd fun r hr hry hr6 => ?_
      have hrQ := hRπ r hr (hry.trans (Subgroup.orderOf_dvd_natCard _ hy))
      exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop6 hrQ hr6)
    exact c.toSetup.mem_Q_of_commute hp hS h3Q hμN c.orderOf_μ hyN (D.commute_μ hyM) h6
  refine ⟨R, hRM, ht₁R, ht₂R, ?_, hRπ, ?_⟩
  · intro h0
    apply hx₀1
    have := hg x₀ hx₀Qt
    rw [h0, Subgroup.mem_bot] at this
    calc x₀ = g * (g⁻¹ * x₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · intro U hUM hUπ
    obtain ⟨g', hg'M, hg'⟩ :=
      exists_conj_le_of_isPiSubgroup hsolv hRhall hUM (fun r hr => hUπ r r.2 hr)
    refine ⟨g' * g⁻¹, D.M.mul_mem hg'M (D.M.inv_mem hgM), fun u hu => ?_⟩
    rw [show (g' * g⁻¹)⁻¹ * u * (g' * g⁻¹) = g * (g'⁻¹ * u * g') * g⁻¹ by group]
    exact hRQ _ (hg' u hu)

theorem exists_M₁
    (hconj : ∀ U : Subgroup G, U ≤ D.M →
      (∀ r : ℕ, r.Prime → r ∣ Nat.card U → r ∣ Nat.card c.Q) →
      ∃ y ∈ D.M, ∀ u ∈ U, y⁻¹ * u * y ∈ c.Q) :
    ∃ M₁ : Subgroup G, M₁ ≤ D.M ∧ (∀ x ∈ M₁, Nat.Coprime (orderOf x) (Nat.card c.Q)) ∧
      (∀ x ∈ D.M, Nat.Coprime (orderOf x) (Nat.card c.Q) → x ∈ M₁) ∧
      ∀ g ∈ Subgroup.normalizer (D.M : Set G), g ∈ Subgroup.normalizer (M₁ : Set G) := by
  classical
  have hμN : c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT
  refine exists_hall_complement fun r hr hrQ => ?_
  have hr' : Fact r.Prime := ⟨hr⟩
  obtain ⟨S⟩ : Nonempty (Sylow r D.M) := inferInstance
  refine ⟨hr', S, fun z hz => ?_⟩
  set SG := (S : Subgroup D.M).map D.M.subtype with hSGdef
  have hSGM : SG ≤ D.M := Subgroup.map_subtype_le _
  have hSGπ : ∀ r' : ℕ, r'.Prime → r' ∣ Nat.card SG → r' ∣ Nat.card c.Q := by
    intro r' hr'' hr'S
    have hSp : IsPGroup r SG := S.isPGroup'.map _
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    rw [hk] at hr'S
    have := (Nat.prime_dvd_prime_iff_eq hr'' hr).mp (hr''.dvd_of_dvd_pow hr'S)
    rw [this]
    exact hrQ
  obtain ⟨y, hyM, hy⟩ := hconj SG hSGM hSGπ
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases hS1 : SG = ⊥
  · have : (w : G) ∈ SG := ⟨w, hw, rfl⟩
    rw [hS1, Subgroup.mem_bot] at this
    have hw1 : w = 1 := Subtype.ext this
    rw [hw1, one_mul, mul_one]
  · have hzN : (z : G) ∈ Subgroup.normalizer (SG : Set G) :=
      Subgroup.le_normalizer_map _ ⟨z, hz, rfl⟩
    have hzodd : Odd (orderOf (z : G)) :=
      Odd.of_dvd_nat D.odd (Subgroup.orderOf_dvd_natCard _ z.2)
    have h := c.toSetup.commute_of_conj hp hS h3Q hμN c.orderOf_μ hy hS1 (D.commute_μ hyM)
      hzN (D.commute_μ z.2) hzodd (w : G) ⟨w, hw, rfl⟩ (D.commute_μ w.2)
    exact Subtype.ext h.symm

end L46Data

end CFSG.Walter.JT
