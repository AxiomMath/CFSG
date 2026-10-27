module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.Quasithin.EmptyFaithful.S146D1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4.G

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_isPGroup_two_of_pow_three {T : Subgroup G} (hT : IsPGroup 2 T) {u : G}
    (hu : u ∈ T) (h3 : u ^ 3 = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h3, hk'⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem exists_invariant_sylow {E W : Subgroup G} (hE3 : IsPGroup 3 E)
    (hEW : E ≤ Subgroup.normalizer (W : Set G)) :
    ∃ T : Subgroup G, T ≤ W ∧ (∃ T' : Sylow 3 ↥W, T = (T' : Subgroup ↥W).map W.subtype) ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥E →* MulAut ↥W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hEW)
  let _ : MulDistribMulAction ↥E ↥W := MulDistribMulAction.compHom ↥W φ
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 ↥W) := by
    have h := card_sylow_modEq_one 3 ↥W
    intro hd
    have h1 : Nat.card (Sylow 3 ↥W) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    have h2 : Nat.card (Sylow 3 ↥W) % 3 = 1 % 3 := h
    omega
  obtain ⟨T, hT⟩ := hE3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 ↥W) hnd
  have hinv : ∀ e : ↥E, ∀ x ∈ (T : Subgroup ↥W), e • x ∈ (T : Subgroup ↥W) := by
    intro e x hx
    have hsmul : e • T = T := MulAction.mem_fixedPoints.mp hT e
    have hmem : e • x ∈ ((e • T : Sylow 3 ↥W) : Subgroup ↥W) := by
      rw [Sylow.pointwise_smul_def]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hx, rfl⟩
    rw [hsmul] at hmem
    exact hmem
  refine ⟨(T : Subgroup ↥W).map W.subtype, Subgroup.map_subtype_le _, ⟨T, rfl⟩, ?_⟩
  have key : ∀ e ∈ E, ∀ x ∈ (T : Subgroup ↥W).map W.subtype,
      e * x * e⁻¹ ∈ (T : Subgroup ↥W).map W.subtype := by
    intro e he x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(⟨e, he⟩ : ↥E) • y, hinv ⟨e, he⟩ y hy, rfl⟩
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key e he x hx, fun hx => ?_⟩
  have h1 := key e⁻¹ (E.inv_mem he) _ hx
  have h2 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
  rwa [h2] at h1

theorem exists_mem_inf_of_rank {I W E : Subgroup G} (hrank : CFSG.Open.pRank 3 I ≤ 2) (hWI : W ≤ I)
    (hEI : E ≤ I) (hEW : E ≤ Subgroup.normalizer (W : Set G)) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (h3W : 3 ∣ Nat.card W) : E ⊓ W ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) hE9
  obtain ⟨T, hTW, ⟨T', hT'⟩, hET⟩ := exists_invariant_sylow hE3 hEW
  have hTne : T ≠ ⊥ := by
    have h3T := T'.dvd_card_of_dvd_card h3W
    intro hbot
    have hbot' : (T' : Subgroup ↥W) = ⊥ := by
      rw [hT'] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (T' : Subgroup ↥W) W.subtype_injective).mp hbot
    rw [hbot'] at h3T
    simp at h3T
  have hT3 : IsPGroup 3 ↥T := by
    rw [hT']
    exact (T'.isPGroup').map W.subtype
  have hP3 : IsPGroup 3 ↥(T ⊔ E) := IsPGroup.to_sup_of_normal_left' hT3 hE3 hET
  have hPnorm : T ⊔ E ≤ Subgroup.normalizer (T : Set G) := sup_le Subgroup.le_normalizer hET
  have hnormal : (T.subgroupOf (T ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff le_sup_left).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (hPnorm hk) h).mp hh
  have : Group.IsNilpotent ↥(T ⊔ E) := hP3.isNilpotent
  have hne : T.subgroupOf (T ⊔ E) ≠ ⊥ := by
    intro h
    apply hTne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, (le_sup_left : T ≤ T ⊔ E) hx⟩ : ↥(T ⊔ E)) ∈ T.subgroupOf (T ⊔ E) := hx
    rw [h] at this
    have h2 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp this)
    rw [h2]
    exact Subgroup.one_mem _
  obtain ⟨⟨u, hu⟩, hu1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have huT : (u : G) ∈ T := hu.1
  have huc : ∀ g : ↥(T ⊔ E), g * (u : ↥(T ⊔ E)) = (u : ↥(T ⊔ E)) * g :=
    fun g => Subgroup.mem_center_iff.mp hu.2 g
  have huE : ∀ x ∈ E, x * (u : G) = (u : G) * x := fun x hx =>
    congrArg Subtype.val (huc ⟨x, (le_sup_right : E ≤ T ⊔ E) hx⟩)
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT3) ⟨u, huT⟩
  have hord : orderOf (u : G) = 3 ^ k := (Subgroup.orderOf_coe (⟨(u : G), huT⟩ : ↥T)).trans hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hu1' (orderOf_eq_one_iff.mp (by simpa using hord))
  have hdvd : 3 ∣ orderOf (u : G) := by
    rw [hord]
    exact dvd_pow_self 3 hk0
  set v : G := (u : G) ^ (orderOf (u : G) / 3) with hv
  have hv3 : orderOf v = 3 := orderOf_pow_orderOf_div (orderOf_pos _).ne' hdvd
  have hv1 : v ≠ 1 := fun h => by
    rw [h, orderOf_one] at hv3
    omega
  have hvT : v ∈ T := Subgroup.pow_mem _ huT _
  have hvE : ∀ x ∈ E, x * v = v * x := fun x hx =>
    (Commute.pow_right (show Commute x (u : G) from huE x hx) _).eq
  by_cases hvmem : v ∈ E
  · intro hbot
    have : v ∈ E ⊓ W := ⟨hvmem, hTW hvT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hv1 this
  · exfalso
    set B : Subgroup G := Subgroup.zpowers v with hB
    have hcardB : Nat.card ↥B = 3 := by rw [hB, Nat.card_zpowers, hv3]
    have hBE : E ⊓ B = ⊥ := by
      have : Fact (Nat.Prime (Nat.card ↥B)) := ⟨by rw [hcardB]; exact Nat.prime_three⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((E ⊓ B).subgroupOf B) with h | h
      · rw [Subgroup.subgroupOf_eq_bot] at h
        have h' := disjoint_iff.mp h
        rwa [inf_assoc, inf_idem] at h'
      · exfalso
        apply hvmem
        have hv : (⟨v, Subgroup.mem_zpowers v⟩ : ↥B) ∈ (E ⊓ B).subgroupOf B := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp hv).1
    have hc : ∀ x ∈ E, ∀ y ∈ B, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x v from hvE x hx) m).eq
    have hsum := pRank_add_le_pRank_sup Nat.prime_three hc hBE
    have h2 : 2 ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hE9
    have hBel : IsElemAbelian 3 B :=
      isElemAbelian_zpowers_of_pow_eq_one (hv3 ▸ pow_orderOf_eq_one v)
    have h1 : 1 ≤ CFSG.Open.pRank 3 B :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBel (k := 1)
        (by rw [hcardB]; simp)
    have hle : CFSG.Open.pRank 3 (E ⊔ B) ≤ CFSG.Open.pRank 3 I :=
      CFSG.SectionRank.pRank_mono (by norm_num)
        (sup_le hEI ((Subgroup.zpowers_le).2 (hWI (hTW hvT))))
    omega

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem pRank_three_le_two_of_hyp (c : P4Ctx T Mc M H B₀ I X) : CFSG.Open.pRank 3 I ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2 := c.hyp.sqtk.1 3 Nat.prime_three (by norm_num)
  rwa [pRank_top_subtype] at hr

end S15223P4.G

end CFSG.Quasithin
