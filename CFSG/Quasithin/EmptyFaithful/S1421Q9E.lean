module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9A
public import CFSG.Quasithin.EmptyFaithful.S1421Q9B
public import CFSG.Quasithin.EmptyFaithful.S1421Q9D
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Q9

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem exists_mem_not_mem_normalizer (hlt : S1421.sOf T K1 < T) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (K1 : Set G) := by
  by_contra hcon
  push Not at hcon
  exact hlt.ne (le_antisymm hlt.le fun t ht => ⟨ht, hcon t ht⟩)

theorem lt_conjClosure_of_not_mem_normalizer {K1 T : Subgroup G} {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (K1 : Set G)) : K1 < conjClosure K1 T := by
  refine lt_of_le_of_ne (le_conjClosure K1 T) fun h => htn ?_
  apply mem_normalizer_of_conj_le
  intro k hk
  have h1 := mem_conjClosure ht hk
  rwa [← h] at h1

omit [Finite G] in
theorem mem_pCoreOf_iff_mk_eq_one {Mc : Subgroup G} (x : ↥Mc) :
    (x : G) ∈ pCoreOf 2 Mc ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥Mc) x = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem two_le_pRank_conjClosure (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h128One : Lemma128One) (h128Two : Lemma128Two) (st : Setting1427 T M H K1)
    (hK1 : K1 ∈ cComp H) (hlt : S1421.sOf T K1 < T) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (mcOf T)) (hKKc : K1 ≤ Kc) (hne : Kc ≠ K1) {T1 : Subgroup G}
    (hT1 : IsSylowTwoOf T1 (mcOf T)) : 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htT, htn1⟩ := exists_mem_not_mem_normalizer hlt
  have hK1loc := isLocal_of_cComp_H st hK1
  have hKcloc := isLocal_of_cComp_mcOf st hKc
  have hcc := lt_conjClosure_of_not_mem_normalizer htT htn1
  have hA5 : IsAlt 5 (ModO2 K1) := by
    rcases h128Two G st.hyp.qtke st.hyp.simple st.hyp.nonabelian T K1 Kc hK1loc hKcloc hKKc hcc
      with h | ⟨hA, -⟩
    · exact absurd h.symm hne
    · exact hA
  have htn : t ∉ Subgroup.normalizer (Kc : Set G) := by
    intro htKc
    have heq := lemma_1_2_8_one st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h128One hK1loc
      hKcloc hKKc
    have h1 : t ∈ T ⊓ Subgroup.normalizer (Kc : Set G) := ⟨htT, htKc⟩
    rw [← heq] at h1
    exact htn1 h1.2
  obtain ⟨a, haK1, ha3⟩ := exists_orderOf_three_of_isAlt_five hA5
  have hMcO := pCoreOf_mcOf_ne_bot st
  have hKcMc : Kc ≤ mcOf T := le_of_mem_cComp hKc
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot st.hyp.qtke st.hyp.simple st.hyp.nonabelian hMcO
  have hLb := modO2Image_mem_cComp hKc
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hT1)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T))) (QuotientGroup.mk'_surjective _)
  obtain ⟨-, hL2⟩ := h38 _ hQ _ hLb
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨tb, htbT, -, -, -, hcomm, hinf, -⟩
  · exfalso
    have hn := normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥(mcOf T))
      (isSolvable_pCore_two_group ↥(mcOf T)) (subgroupOf_mem_cComp hKc) hnorm
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hKcMc).mp hn
    exact htn (hle (st.hyp.toQTFE14.t_le_mc htT))
  · obtain ⟨r', hr'mem, hr'⟩ := Subgroup.mem_map.mp htbT
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T)) with hπ
    have haMc : a ∈ mcOf T := k1_le_mcOf st haK1
    let a' : ↥(mcOf T) := ⟨a, haMc⟩
    let b' : ↥(mcOf T) := r' * a' * r'⁻¹
    have hrT1 : (r' : G) ∈ T1 := hr'mem
    have haq : π a' ∈ modO2Image (mcOf T) Kc := Subgroup.mem_map.mpr ⟨a', hKKc haK1, rfl⟩
    have hπb : π b' = tb * π a' * tb⁻¹ := by
      simp only [b', map_mul, map_inv, hr']
    have hbq : π b' ∈ (modO2Image (mcOf T) Kc).map (MulAut.conj tb).toMonoidHom := by
      rw [A38.mem_map_conj]
      have h1 : tb⁻¹ * π b' * tb = π a' := by
        rw [hπb]
        group
      rw [h1]
      exact haq
    have hcomm1 : π a' * π b' * (π a')⁻¹ * (π b')⁻¹ = 1 := by
      have hmem := Subgroup.commutator_mem_commutator haq hbq
      rw [hcomm] at hmem
      simpa [commutatorElement_def] using hmem
    have hcommR : a * ((r' : G) * a * (r' : G)⁻¹) * a⁻¹ * ((r' : G) * a * (r' : G)⁻¹)⁻¹ ∈
        pCoreOf 2 (mcOf T) := by
      refine (mem_pCoreOf_iff_mk_eq_one (a' * b' * a'⁻¹ * b'⁻¹)).mpr ?_
      simp only [map_mul, map_inv]
      exact hcomm1
    have haq1 : π a' ≠ 1 := by
      intro h
      have h0 := (mem_pCoreOf_iff_mk_eq_one a').mpr h
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨a, h0⟩
      have h1 : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
      rw [ha3] at h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
    have ha3' : a ^ 3 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha3] at this
    have haq3 : π a' ^ 3 = 1 := by
      rw [← map_pow]
      have : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3')
      rw [this, map_one]
    have hord : orderOf (π a') = 3 := orderOf_eq_prime haq3 haq1
    have hbq3 : (π b') ^ 3 = 1 := by
      rw [hπb, conj_pow, haq3, mul_one, mul_inv_cancel]
    have hbq1 : π b' ≠ 1 := by
      intro h
      apply haq1
      have h1 : tb⁻¹ * π b' * tb = π a' := by
        rw [hπb]
        group
      rw [← h1, h]
      group
    have hordb : orderOf (π b') = 3 := orderOf_eq_prime hbq3 hbq1
    have hind : ∀ i j : ℤ, a ^ i * ((r' : G) * a * (r' : G)⁻¹) ^ j ∈ pCoreOf 2 (mcOf T) →
        (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
      intro i j hij
      have h1 : π (a' ^ i * b' ^ j) = 1 :=
        (mem_pCoreOf_iff_mk_eq_one (a' ^ i * b' ^ j)).mp (by exact hij)
      rw [map_mul, map_zpow, map_zpow] at h1
      have h2 : π a' ^ i ∈ modO2Image (mcOf T) Kc ⊓
          (modO2Image (mcOf T) Kc).map (MulAut.conj tb).toMonoidHom := by
        refine ⟨Subgroup.zpow_mem _ haq i, ?_⟩
        have h3 : π a' ^ i = (π b' ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h3]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ hbq j)
      rw [hinf, Subgroup.mem_bot] at h2
      have h3 : π b' ^ j = 1 := by
        rw [h2, one_mul] at h1
        exact h1
      have h4 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      have h5 := orderOf_dvd_iff_zpow_eq_one.mpr h3
      rw [hord] at h4
      rw [hordb] at h5
      exact ⟨by exact_mod_cast h4, by exact_mod_cast h5⟩
    have hMcX : conjClosure K1 T1 ≤ mcOf T :=
      conjClosure_le fun h hh z hz => (mcOf T).mul_mem
        ((mcOf T).mul_mem (hT1.1 hh) (k1_le_mcOf st hz)) ((mcOf T).inv_mem (hT1.1 hh))
    have hXR : conjClosure K1 T1 ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
      hMcX.trans (le_normalizer_pCoreOf 2 (mcOf T))
    have haX : a ∈ conjClosure K1 T1 := le_conjClosure K1 T1 haK1
    have hbX : (r' : G) * a * (r' : G)⁻¹ ∈ conjClosure K1 T1 := mem_conjClosure hrT1 haK1
    have hb3' : ((r' : G) * a * (r' : G)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, ha3', mul_one, mul_inv_cancel]
    exact two_le_pRank_of_commute_mod_two_group (pCoreOf_isPGroup 2 (mcOf T)) hXR haX hbX ha3'
      hb3' hcommR hind

theorem case2 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h128One : Lemma128One)
    (h128Two : Lemma128Two) (st : Setting1427 T M H K1) (hK1 : K1 ∈ cComp H)
    (hlt : S1421.sOf T K1 < T) :
    ∃ Kc ∈ cComp (mcOf T), K1 ≤ Kc ∧ oTwoUpper H ≤ Kc ⊔ T ∧
      ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
        Kc ≤ K1 ⊔ T1 ∨ 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) := by
  have hBl : K1 ∈ lFamily T := by
    show K1 ∈ cComp (K1 ⊔ T)
    rw [sup_eq_hStar st]
    exact hK1
  obtain ⟨Kc, hKc, hKKc⟩ := exists_cComp_mcOf h37 h39 st hBl (k1_le_mcOf st)
  refine ⟨Kc, hKc, hKKc, ?_, ?_⟩
  · calc oTwoUpper H ≤ H := oTwoUpper_le H
      _ = K1 ⊔ T := (sup_eq_hStar st).symm
      _ ≤ Kc ⊔ T := sup_le_sup_right hKKc T
  · intro T1 hT1 _
    by_cases hKcK1 : Kc = K1
    · left
      rw [hKcK1]
      exact le_sup_left
    · right
      exact two_le_pRank_conjClosure h37 h38 h128One h128Two st hK1 hlt hKc hKKc hKcK1 hT1

end Q9

end CFSG.Quasithin
