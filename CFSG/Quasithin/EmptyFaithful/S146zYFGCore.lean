module

public import CFSG.Quasithin.Vol2.F134LieF4Group
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.S146zY

open CFSG.ABGLocalTools CFSG.LieType.BorelTits CFSG.Quasithin.F134.LieF4

theorem exists_closure_pair_eq_of_le {G : Type*} [Group G] [Finite G] {P F : Subgroup G}
    (hP : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) (hFP : F ≤ P) :
    ∃ a ∈ F, ∃ b ∈ F, F = Subgroup.closure {a, b} := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hF : F = ⊥
  · refine ⟨1, F.one_mem, 1, F.one_mem, ?_⟩
    rw [hF, Set.pair_eq_singleton, Subgroup.closure_singleton_one]
  obtain ⟨a, haF, ha1⟩ : ∃ a ∈ F, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hF ((Subgroup.eq_bot_iff_forall F).2 hcon)
  have ha5 : orderOf a = 5 := orderOf_eq_prime (hexp a (hFP haF)) ha1
  by_cases hzF : Subgroup.zpowers a = F
  · refine ⟨a, haF, a, haF, ?_⟩
    rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, hzF]
  have hlt : Subgroup.zpowers a < F := lt_of_le_of_ne (Subgroup.zpowers_le.2 haF) hzF
  obtain ⟨b, hbF, hbz⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨a, haF, b, hbF, ?_⟩
  have hcl_le : Subgroup.closure ({a, b} : Set G) ≤ F :=
    (Subgroup.closure_le F).2 (by rintro x (rfl | rfl) <;> assumption)
  have hz_le : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hb_cl : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have h5 : 5 ∣ Nat.card (Subgroup.closure ({a, b} : Set G)) := by
    have := Subgroup.card_dvd_of_le hz_le
    rwa [Nat.card_zpowers, ha5] at this
  have hdvd : Nat.card (Subgroup.closure ({a, b} : Set G)) ∣ 5 ^ 2 := by
    have := Subgroup.card_dvd_of_le (hcl_le.trans hFP)
    rwa [hP] at this
  have h25 : Nat.card (Subgroup.closure ({a, b} : Set G)) = 25 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
    interval_cases j
    · rw [pow_zero] at hj'
      rw [hj'] at h5
      omega
    · exfalso
      have heq : Subgroup.zpowers a = Subgroup.closure ({a, b} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hz_le (by rw [Nat.card_zpowers, ha5, hj']; norm_num)
      exact hbz (heq ▸ hb_cl)
    · simpa using hj'
  have hclP : Subgroup.closure ({a, b} : Set G) = P :=
    Subgroup.eq_of_le_of_card_ge (hcl_le.trans hFP) (by rw [h25, hP])
  exact le_antisymm (hclP ▸ hFP) hcl_le

theorem exists_normal_isPGroup_two_ne_bot_of_card {G : Type*} [Group G] [Finite G] {k : ℕ}
    (hG : Nat.card G = 25 * 2 ^ k) (hk : 10 ≤ k) {P : Subgroup G} (hP : Nat.card P = 25)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) : ∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ N ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsolv : Group.IsSolvable G := by
    have : Fintype G := Fintype.ofFinite G
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 5) (q := 2) (a := 2) (b := k) (by norm_num) Nat.prime_two (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hG]; ring)
  have hp' : CFSG.pPrimeCore 5 G = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    refine hcon K hK ?_
    have hdvd : Nat.card K ∣ 5 ^ 2 * 2 ^ k := by
      rw [show 5 ^ 2 * 2 ^ k = Nat.card G by rw [hG]; ring]
      exact Subgroup.card_subgroup_dvd_card K
    have hcop' : Nat.Coprime (Nat.card K) (5 ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcop'.dvd_of_dvd_mul_left hdvd)
    exact IsPGroup.of_card hj
  have hFn : (CFSG.pCore 5 G).Normal := CFSG.pCore_normal
  have hF5 : IsPGroup 5 (CFSG.pCore 5 G) := CFSG.pCore_isPGroup
  have hcent : Subgroup.centralizer (CFSG.pCore 5 G : Set G) ≤ CFSG.pCore 5 G := by
    have := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    rwa [CFSG.Fitting_eq_pcore G 5 hp'] at this
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hPidx : ¬ 5 ∣ P.index := by
    have h := P.card_mul_index
    rw [hP, hG] at h
    have hidx : P.index = 2 ^ k := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    rw [hidx]
    intro h5
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  have hFP : CFSG.pCore 5 G ≤ P := hF5.le_sylow_of_normal (hP5.toSylow hPidx)
  obtain ⟨a, haF, b, hbF, hab⟩ := exists_closure_pair_eq_of_le hP hexp hFP
  obtain ⟨U, hU⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 2 (n := k)
    (by rw [hG]; exact Dvd.intro_left _ rfl)
  have hU2 : IsPGroup 2 U := IsPGroup.of_card hU
  have hUF : Disjoint U (CFSG.pCore 5 G) :=
    IsPGroup.disjoint_of_ne 2 5 (by norm_num) U _ hU2 hF5
  let f : U → CFSG.pCore 5 G × CFSG.pCore 5 G := fun u =>
    (⟨(u : G) * a * (u : G)⁻¹, hFn.conj_mem a haF u⟩,
      ⟨(u : G) * b * (u : G)⁻¹, hFn.conj_mem b hbF u⟩)
  have hf : Function.Injective f := by
    intro u u' h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hc : ((u' : G)⁻¹ * u : G) ∈ Subgroup.centralizer (CFSG.pCore 5 G : Set G) := by
      rw [hab, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro x (rfl | rfl)
      · calc x * ((u' : G)⁻¹ * u) = (u' : G)⁻¹ * ((u' : G) * x * (u' : G)⁻¹) * u := by group
          _ = (u' : G)⁻¹ * ((u : G) * x * (u : G)⁻¹) * u := by rw [h1]
          _ = ((u' : G)⁻¹ * u) * x := by group
      · calc x * ((u' : G)⁻¹ * u) = (u' : G)⁻¹ * ((u' : G) * x * (u' : G)⁻¹) * u := by group
          _ = (u' : G)⁻¹ * ((u : G) * x * (u : G)⁻¹) * u := by rw [h2]
          _ = ((u' : G)⁻¹ * u) * x := by group
    have hcU : ((u' : G)⁻¹ * u : G) ∈ U := U.mul_mem (U.inv_mem u'.2) u.2
    have h1' : ((u' : G)⁻¹ * u : G) = 1 :=
      Subgroup.disjoint_def.1 hUF hcU (hcent hc)
    exact Subtype.ext (inv_mul_eq_one.1 h1').symm
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hU] at hle
  have hFcard : Nat.card (CFSG.pCore 5 G) ≤ 25 := hP ▸ Subgroup.card_le_of_le hFP
  have h625 : 2 ^ k ≤ 25 * 25 := hle.trans (Nat.mul_le_mul hFcard hFcard)
  have h1024 : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem exists_normalizing_isPGroup_two_ne_bot_of_card {Y : Type*} [Group Y] [Finite Y]
    {H P : Subgroup Y} {k : ℕ} (hH : Nat.card H = 25 * 2 ^ k) (hk : 10 ≤ k) (hPH : P ≤ H)
    (hP : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) :
    ∃ V : Subgroup Y, V ≠ ⊥ ∧ IsPGroup 2 V ∧ H ≤ Subgroup.normalizer (V : Set Y) := by
  obtain ⟨N, hN, hN2, hNbot⟩ := exists_normal_isPGroup_two_ne_bot_of_card (G := H) hH hk
    (P := P.subgroupOf H)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP])
    (fun x hx => Subtype.ext (by simpa using hexp x (Subgroup.mem_subgroupOf.mp hx)))
  refine ⟨N.map H.subtype, ?_, hN2.map H.subtype, ?_⟩
  · intro h
    exact hNbot (by rwa [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h)
  · have hVsub : (N.map H.subtype).subgroupOf H = N := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).1 ?_
    rw [hVsub]
    exact hN

theorem exists_proper_overgroup_of_normal_isPGroup {Y : Type*} [Group Y] [Finite Y]
    (hBT : Holds Y 2) {U H V : Subgroup Y} (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H) (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hHV : H ≤ Subgroup.normalizer (V : Set Y)) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hV hV2
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, normalizer_le_of_isSylowOf
    (isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

end CFSG.Quasithin.S146zY
