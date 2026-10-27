module

public import CFSG.Walter.W67.Section5.P56AbBar
public import CFSG.Walter.W67.Section5.P56AbHallTools

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem isHallSubgroup_of_card_eq {K S S' : Subgroup G} {π : Set Nat.Primes}
    (hS : IsHallSubgroup π (S.subgroupOf K)) (hSK : S ≤ K) (hS'K : S' ≤ K)
    (hcard : Nat.card S' = Nat.card S) : IsHallSubgroup π (S'.subgroupOf K) := by
  have h1 : Nat.card (S'.subgroupOf K) = Nat.card (S.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'K).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hcard]
  have h2 : (S'.subgroupOf K).index = (S.subgroupOf K).index := by
    have h0 : 0 < Nat.card (S.subgroupOf K) := Nat.card_pos
    have e1 := Subgroup.card_mul_index (S'.subgroupOf K)
    have e2 := Subgroup.card_mul_index (S.subgroupOf K)
    rw [h1] at e1
    exact Nat.eq_of_mul_eq_mul_left h0 (e1.trans e2.symm)
  refine isHallSubgroup_of π _ ?_ ?_
  · intro p hp
    rw [h1] at hp
    exact hS.p_in_pi_of_p_dvd_card p hp
  · intro p hp hpdvd
    rw [h2] at hpdvd
    exact hS.p_in_pi_of_p_dvd_index p hpdvd hp

noncomputable abbrev Mbar : Subgroup (MulAut d.V) := (pCore 3 d.Nbar).map d.Nbar.subtype

noncomputable abbrev M : Subgroup G := (d.Mbar.comap d.φ).map d.NV.subtype

theorem mem_M {x : G} : x ∈ d.M ↔ ∃ hx : x ∈ d.NV, d.φ ⟨x, hx⟩ ∈ d.Mbar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem M_le_NV : d.M ≤ d.NV := Subgroup.map_subtype_le _

theorem Mbar_le_Nbar : d.Mbar ≤ d.Nbar := Subgroup.map_subtype_le _

theorem Mbar_isPGroup : IsPGroup 3 d.Mbar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (pCore_isPGroup (p := 3) (G := d.Nbar)).map d.Nbar.subtype

theorem CV_le_M : d.CV ≤ d.M := fun x hx =>
  d.mem_M.mpr ⟨d.CV_le_NV hx, by rw [(d.φ_eq_one_iff ⟨x, d.CV_le_NV hx⟩).mpr hx]; exact
    d.Mbar.one_mem⟩

theorem V_le_M : d.V ≤ d.M := d.V_le_CV.trans d.CV_le_M

theorem Nbar_le_normalizer_Mbar :
    d.Nbar ≤ Subgroup.normalizer (d.Mbar : Set (MulAut d.V)) := by
  intro α hα
  apply Sec53.mem_normalizer_of_conj_le
  rintro _ ⟨β, hβ, rfl⟩
  have hn := (pCore_normal (p := 3) (G := d.Nbar)).conj_mem β hβ ⟨α, hα⟩
  exact ⟨_, hn, rfl⟩

theorem NV_le_normalizer_M : d.NV ≤ Subgroup.normalizer (d.M : Set G) := by
  intro g hg
  apply Sec53.mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨hxN, hxM⟩ := d.mem_M.mp hx
  refine d.mem_M.mpr ⟨d.NV.mul_mem (d.NV.mul_mem hg hxN) (d.NV.inv_mem hg), ?_⟩
  have : d.φ ⟨g * x * g⁻¹, d.NV.mul_mem (d.NV.mul_mem hg hxN) (d.NV.inv_mem hg)⟩ =
      d.φ ⟨g, hg⟩ * d.φ ⟨x, hxN⟩ * (d.φ ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp (d.Nbar_le_normalizer_Mbar ⟨⟨g, hg⟩, rfl⟩) _).mp hxM

theorem card_M : Nat.card d.M = Nat.card d.CV * Nat.card d.Mbar := by
  set ψ : d.M →* MulAut d.V := d.φ.comp (Subgroup.inclusion d.M_le_NV)
  have hker : Nat.card ψ.ker = Nat.card d.CV := by
    have : ψ.ker = d.CV.subgroupOf d.M := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, φ_eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.CV_le_M).toEquiv]
  have hrange : ψ.range = d.Mbar := by
    ext α
    constructor
    · rintro ⟨x, rfl⟩
      exact (d.mem_M.mp x.2).2
    · intro hα
      obtain ⟨x, hx⟩ := d.Mbar_le_Nbar hα
      refine ⟨⟨x, d.mem_M.mpr ⟨x.2, show d.φ x ∈ d.Mbar from hx ▸ hα⟩⟩, ?_⟩
      exact hx
  rw [← Subgroup.card_ker_mul_card_range ψ, hker, hrange]

theorem odd_card_M : Odd (Nat.card d.M) := by
  rw [d.card_M]
  refine Odd.mul d.odd_card_CV ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.Mbar_isPGroup
  rw [hk]
  exact Odd.pow (by decide)

theorem H_le_normalizer_B : d.H ≤ Subgroup.normalizer (d.B : Set G) := by
  refine sup_le (sup_le ?_ Subgroup.le_normalizer) d.E_le_normalizer_B
  rw [Subgroup.zpowers_le]
  apply Sec53.mem_normalizer_of_conj_le
  intro b hb
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (d.B_le hb), mul_inv_cancel_right]
  exact hb

theorem P₀_faithful_B : ∀ y ∈ d.P₀, (∀ b ∈ d.B, y * b = b * y) → y = 1 :=
  fun y hy h => d.E_faithful y (d.P₀_le hy) h

theorem phi_comm_Jbar_of_comm {g : G} (hg : g ∈ d.NV) (hgJ : g * d.J = d.J * g) :
    d.φ ⟨g, hg⟩ * d.Jbar = d.Jbar * d.φ ⟨g, hg⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hgJ

theorem Mbar_inf_centralizer_eq_bot :
    d.Mbar ⊓ Subgroup.centralizer ({d.Jbar} : Set (MulAut d.V)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine d.eq_bot_of_comm_Jbar le_rfl d.H_le_normalizer_B d.P₀_faithful_B
    (inf_le_left.trans d.Mbar_le_Nbar) ?_ (d.Mbar_isPGroup.to_le inf_le_left) ?_
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  · rintro _ ⟨b, hb, rfl⟩
    have hbN := d.bar_le_Nbar d.B ⟨b, hb, rfl⟩
    have hbJ : d.φ b * d.Jbar = d.Jbar * d.φ b :=
      d.phi_comm_Jbar_of_comm b.2 (Subgroup.mem_centralizer_singleton_iff.mp (d.B_le hb))
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp
      (d.Nbar_le_normalizer_Mbar hbN) y).mp hyM, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    have hbJ' : (d.φ b)⁻¹ * d.Jbar = d.Jbar * (d.φ b)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbJ, mul_inv_cancel_right]
    calc d.φ b * y * (d.φ b)⁻¹ * d.Jbar = d.φ b * y * ((d.φ b)⁻¹ * d.Jbar) := by group
      _ = d.φ b * (y * d.Jbar) * (d.φ b)⁻¹ := by rw [hbJ']; group
      _ = d.φ b * (d.Jbar * y) * (d.φ b)⁻¹ := by rw [hyC]
      _ = (d.φ b * d.Jbar) * y * (d.φ b)⁻¹ := by group
      _ = d.Jbar * (d.φ b * y * (d.φ b)⁻¹) := by rw [hbJ]; group

theorem mem_P₁_of_mem_M {c : G} (hc : c ∈ d.M) (hcJ : c * d.J = d.J * c) : c ∈ d.P₁ := by
  obtain ⟨hcN, hcM⟩ := d.mem_M.mp hc
  have h1 : d.φ ⟨c, hcN⟩ ∈ d.Mbar ⊓ Subgroup.centralizer ({d.Jbar} : Set (MulAut d.V)) :=
    Subgroup.mem_inf.mpr ⟨hcM, Subgroup.mem_centralizer_singleton_iff.mpr
      (d.phi_comm_Jbar_of_comm hcN hcJ)⟩
  rw [d.Mbar_inf_centralizer_eq_bot, Subgroup.mem_bot, φ_eq_one_iff] at h1
  exact d.centralizer_J_inf (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcJ, h1⟩)

theorem coprime_card_zpowers_J_M :
    Nat.Coprime (Nat.card (Subgroup.zpowers d.J)) (Nat.card d.M) := by
  rw [Nat.card_zpowers, d.orderOf_J]
  exact (Nat.coprime_two_left).mpr d.odd_card_M

theorem zpowers_J_le_normalizer_M : Subgroup.zpowers d.J ≤ Subgroup.normalizer (d.M : Set G) :=
  Subgroup.zpowers_le.mpr (d.NV_le_normalizer_M d.J_mem_NV)

abbrev π₃ : Set Nat.Primes := {⟨3, Nat.prime_three⟩}

theorem isPiSubgroup_iff_isPGroup {X : Subgroup G} : IsPiSubgroup π₃ X ↔ IsPGroup 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · intro h
    have hX : Nat.card X = 3 ^ (Nat.card X).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq hqX => by
        have := h ⟨q, hq⟩ hqX
        exact congrArg Subtype.val (show (⟨q, hq⟩ : Nat.Primes) = ⟨3, Nat.prime_three⟩ from this))
    exact IsPGroup.of_card hX
  · intro h p hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
    rw [hk] at hp
    have := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).mp (p.2.dvd_of_dvd_pow hp)
    exact Subtype.ext this

theorem exists_sylow_M : ∃ S : Subgroup G, S ≤ d.M ∧ IsHallSubgroup π₃ (S.subgroupOf d.M) ∧
    Subgroup.zpowers d.J ≤ Subgroup.normalizer (S : Set G) ∧ d.V ≤ S :=
  exists_hall_invariant d.zpowers_J_le_normalizer_M (isSolvable_of_odd d.odd_card_M)
    d.coprime_card_zpowers_J_M d.V_le_M (isPiSubgroup_iff_isPGroup.mpr d.V_isPGroup)
    (Subgroup.zpowers_le.mpr d.J_mem_NV)

theorem mem_normalizer_sylow_M {S : Subgroup G} (hSM : S ≤ d.M)
    (hS : IsHallSubgroup π₃ (S.subgroupOf d.M))
    (hJS : Subgroup.zpowers d.J ≤ Subgroup.normalizer (S : Set G)) (hVS : d.V ≤ S) {g : G}
    (hg : g ∈ d.NV) (hgJ : g * d.J = d.J * g) : g ∈ Subgroup.normalizer (S : Set G) := by
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hmemS' : ∀ s ∈ S, g * s * g⁻¹ ∈ S' := fun s hs => ⟨s, hs, rfl⟩
  have hS'M : S' ≤ d.M := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (d.NV_le_normalizer_M hg) s).mp (hSM hs)
  have hS'Hall : IsHallSubgroup π₃ (S'.subgroupOf d.M) :=
    isHallSubgroup_of_card_eq hS hSM hS'M
      (Subgroup.card_map_of_injective (MulAut.conj g).injective)
  have hJS' : Subgroup.zpowers d.J ≤ Subgroup.normalizer (S' : Set G) := by
    intro a ha
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hga : g * d.J ^ k = d.J ^ k * g := (Commute.zpow_right (show Commute g d.J from hgJ) k).eq
    have hs' : d.J ^ k * s * (d.J ^ k)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hJS ha) s).mp hs
    have : d.J ^ k * ((MulAut.conj g).toMonoidHom s) * (d.J ^ k)⁻¹ =
        g * (d.J ^ k * s * (d.J ^ k)⁻¹) * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hga' : (d.J ^ k)⁻¹ * g⁻¹ = g⁻¹ * (d.J ^ k)⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hga]
      calc d.J ^ k * (g * s * g⁻¹) * (d.J ^ k)⁻¹ =
            (d.J ^ k * g) * s * (g⁻¹ * (d.J ^ k)⁻¹) := by group
        _ = (g * d.J ^ k) * s * ((d.J ^ k)⁻¹ * g⁻¹) := by rw [hga, hga']
        _ = g * (d.J ^ k * s * (d.J ^ k)⁻¹) * g⁻¹ := by group
    rw [this]
    exact hmemS' _ hs'
  obtain ⟨c, hc, hceq⟩ := exists_conj_hall_invariant d.zpowers_J_le_normalizer_M
    (isSolvable_of_odd d.odd_card_M) d.coprime_card_zpowers_J_M hSM hS'M hS hS'Hall hJS hJS'
  obtain ⟨hcM, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcJ : c * d.J = d.J * c :=
    (Subgroup.mem_centralizer_iff.mp hcC d.J (Subgroup.mem_zpowers _)).symm
  have hcS : c ∈ S := hVS (Subgroup.mem_sup_left (d.mem_P₁_of_mem_M hcM hcJ))
  have hSc : S.map (MulAut.conj c).toMonoidHom = S := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact S.mul_mem (S.mul_mem hcS hs) (S.inv_mem hcS)
    · intro s hs
      refine ⟨c⁻¹ * s * c, S.mul_mem (S.mul_mem (S.inv_mem hcS) hs) hcS, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hSc] at hceq
  apply Sec53.mem_normalizer_of_conj_le
  intro s hs
  rw [← hceq]
  exact hmemS' s hs

theorem sylow_M_eq_V {S : Subgroup G} (hSM : S ≤ d.M) (hS : IsHallSubgroup π₃ (S.subgroupOf d.M))
    (hJS : Subgroup.zpowers d.J ≤ Subgroup.normalizer (S : Set G)) (hVS : d.V ≤ S) :
    S = d.V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := by
    have h1 : IsPGroup 3 (S.subgroupOf d.M) :=
      isPiSubgroup_iff_isPGroup.mp hS.p_in_pi_of_p_dvd_card
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hSM)
  refine d.maximal S hSp hVS (hJS (Subgroup.mem_zpowers _)) ?_ ?_
  · intro b hb
    exact d.mem_normalizer_sylow_M hSM hS hJS hVS (d.B_le_NV hb)
      (Subgroup.mem_centralizer_singleton_iff.mp (d.B_le hb))
  · intro e he
    exact d.mem_normalizer_sylow_M hSM hS hJS hVS (d.E_le_NV he)
      (Subgroup.mem_centralizer_singleton_iff.mp (d.E_le he))

theorem pCore_Nbar_eq_bot : pCore 3 d.Nbar = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSM, hS, hJS, hVS⟩ := d.exists_sylow_M
  have hSV := d.sylow_M_eq_V hSM hS hJS hVS
  subst hSV
  have hfacM : (Nat.card d.M).factorization 3 = 2 * d.n := by
    have h1 := Subgroup.card_mul_index (d.V.subgroupOf d.M)
    have hcV : Nat.card (d.V.subgroupOf d.M) = 3 ^ (2 * d.n) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, d.card_V]
    have hcop := hS.card_coprime_index
    rw [hcV] at hcop h1
    have hidx : ¬ 3 ∣ (d.V.subgroupOf d.M).index := by
      have h3 : Nat.Coprime 3 (d.V.subgroupOf d.M).index :=
        Nat.Coprime.coprime_dvd_left (dvd_pow_self 3 (by have := d.three_le_n; omega)) hcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3
    have hidx0 : (d.V.subgroupOf d.M).index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact Nat.card_pos.ne' h1.symm
    rw [← h1, Nat.factorization_mul (by positivity) hidx0]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  have hfacC : 2 * d.n ≤ (Nat.card d.CV).factorization 3 := by
    have hdvd : 3 ^ (2 * d.n) ∣ Nat.card d.CV := d.card_V ▸ Subgroup.card_dvd_of_le d.V_le_CV
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
  have hcard := d.card_M
  have hfac := congrArg (fun m => m.factorization 3) hcard
  simp only [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.coe_add,
    Pi.add_apply] at hfac
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.Mbar_isPGroup
  rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at hfac
  have hk0 : k = 0 := by omega
  rw [hk0, pow_zero] at hk
  have hMbar : d.Mbar = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
  exact (Subgroup.map_eq_bot_iff_of_injective _ d.Nbar.subtype_injective).mp hMbar

end P56AbData

end CFSG.Walter.W67
