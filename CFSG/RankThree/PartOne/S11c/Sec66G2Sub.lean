module

public import CFSG.RankThree.PartOne.S11c.Sec66G2

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem g2Sub_mem_normalizer {G : Type*} [Group G] [Finite G] {R : Subgroup G} {x : G}
    (hx : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : x ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hx h, fun hh => ?_⟩
  have hle : R.map (MulAut.conj x).toMonoidHom ≤ R := by
    rintro _ ⟨u, hu, rfl⟩
    exact hx u hu
  have heq : R.map (MulAut.conj x).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective).ge
  rw [← heq] at hh
  obtain ⟨u, hu, hux⟩ := hh
  have : u = h := by
    simpa [MulAut.conj_apply] using hux
  rwa [← this]

theorem g2Sub_exists_conj_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U S : Sylow p G) (B P : Subgroup G)
    (hB : B ≤ Subgroup.normalizer ((U : Subgroup G) : Set G))
    (hS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ P) :
    ∃ g : G, B ≤ P.comap (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U S
  refine ⟨g, ?_⟩
  rw [← Subgroup.map_le_iff_le_comap]
  calc B.map (MulAut.conj g).toMonoidHom
      ≤ (Subgroup.normalizer ((U : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hB
    _ = Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) := Subgroup.map_equiv_normalizer_eq _ _
    _ = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [← coe_smul_sylow_eq_map, hg]
    _ ≤ P := hS

theorem g2Sub_two_pow_prime_arith {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ 2 ^ p ∧ ¬ p ∣ 2 ^ p - 1 ∧ ¬ p ∣ 2 ^ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : ((2 ^ p : ℕ) : ZMod p) = 2 := by
    push_cast
    exact ZMod.pow_card 2
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h0 : ((2 ^ p : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [hF] at h0
    have h2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have h1 : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_sub Nat.one_le_two_pow, hF, Nat.cast_one] at h1
    exact one_ne_zero (by linear_combination h1 : (1 : ZMod p) = 0)
  · have h1 : ((2 ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_add, hF, Nat.cast_one] at h1
    have h3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1
      (by exact_mod_cast (by linear_combination h1 : (3 : ZMod p) = 0))
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem g2Sub_exists_other (i : Fin Tag.G2.rank) :
    ∃ j : Fin Tag.G2.rank, ∀ l, l ≠ i → l = j := by
  have hr : Tag.G2.rank = 2 := rfl
  revert i
  rw [hr]
  decide

theorem g2Sub_exists_subset_singleton {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    ∃ j, J ⊆ {j} := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  obtain ⟨j, hj⟩ := g2Sub_exists_other i
  exact ⟨j, fun l hl => hj l (fun h => hi (h ▸ hl))⟩

theorem g2Sub_mem_parabolicWeylGroup_cases {J : Set (Fin Tag.G2.rank)} {j : Fin Tag.G2.rank}
    (hJ : J ⊆ {j}) {w : WeylGroup Tag.G2} (hw : w ∈ parabolicWeylGroup Tag.G2 J) :
    w = 1 ∨ w = simple Tag.G2 j := by
  have hle : parabolicWeylGroup Tag.G2 J ≤ Subgroup.zpowers (simple Tag.G2 j) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have : i = j := hJ hi
    subst this
    exact Subgroup.mem_zpowers _
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hle hw)
  have hsq : simple Tag.G2 j * simple Tag.G2 j = 1 :=
    (coxeterSystem Tag.G2).simple_mul_simple_self j
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, zpow_two, hsq, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hsq, one_zpow, one_mul]

theorem g2Sub_finsum_parabolicWeyl {J : Set (Fin Tag.G2.rank)} {j : Fin Tag.G2.rank}
    (hJ : J ⊆ {j}) (Q : ℕ) :
    ∑ᶠ w : parabolicWeylGroup Tag.G2 J, Q ^ (coxeterSystem Tag.G2).length w.1 = 1 ∨
    ∑ᶠ w : parabolicWeylGroup Tag.G2 J, Q ^ (coxeterSystem Tag.G2).length w.1 = 1 + Q := by
  have hne : (1 : WeylGroup Tag.G2) ≠ simple Tag.G2 j := by
    intro h
    have h' : (coxeterSystem Tag.G2).simple j = 1 := h.symm
    have := (coxeterSystem Tag.G2).length_simple j
    rw [h', (coxeterSystem Tag.G2).length_one] at this
    exact zero_ne_one this
  rw [finsum_subtype_eq_finsum_cond (fun w => w ∈ parabolicWeylGroup Tag.G2 J)
    (f := fun w => Q ^ (coxeterSystem Tag.G2).length w)]
  by_cases hs : simple Tag.G2 j ∈ parabolicWeylGroup Tag.G2 J
  · right
    have hset : ((parabolicWeylGroup Tag.G2 J : Subgroup _) : Set (WeylGroup Tag.G2)) =
        {1, simple Tag.G2 j} := by
      ext w
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact g2Sub_mem_parabolicWeylGroup_cases hJ
      · rintro (rfl | rfl)
        · exact one_mem _
        · exact hs
    have := finsum_mem_pair (f := fun w => Q ^ (coxeterSystem Tag.G2).length w) hne
    simp only [(coxeterSystem Tag.G2).length_one, (coxeterSystem Tag.G2).length_simple,
      pow_zero, pow_one] at this
    show ∑ᶠ i ∈ ((parabolicWeylGroup Tag.G2 J : Subgroup _) : Set (WeylGroup Tag.G2)),
      Q ^ (coxeterSystem Tag.G2).length i = _
    rw [hset]
    exact this
  · left
    have hset : ((parabolicWeylGroup Tag.G2 J : Subgroup _) : Set (WeylGroup Tag.G2)) = {1} := by
      ext w
      simp only [SetLike.mem_coe, Set.mem_singleton_iff]
      constructor
      · intro hw
        rcases g2Sub_mem_parabolicWeylGroup_cases hJ hw with h | h
        · exact h
        · exact absurd (h ▸ hw) hs
      · rintro rfl
        exact one_mem _
    have := finsum_mem_singleton (f := fun w => Q ^ (coxeterSystem Tag.G2).length w) (a := 1)
    simp only [(coxeterSystem Tag.G2).length_one, pow_zero] at this
    show ∑ᶠ i ∈ ((parabolicWeylGroup Tag.G2 J : Subgroup _) : Set (WeylGroup Tag.G2)),
      Q ^ (coxeterSystem Tag.G2).length i = _
    rw [hset]
    exact this

theorem g2Sub_borel_le_adjointGroup
    {K : Type} [Field K] : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K :=
  ((triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem g2Sub_borel_le_normalizer
    {K : Type} [Field K] :
    (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
      Subgroup.normalizer (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup (adjointGroup Tag.G2 K)) : Set (adjointGroup Tag.G2 K)) := by
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUB : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
  have hBN : borelGroup Tag.G2 K ≤
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.2.2.2.2.2.1
  intro b hb
  have hb' : (b : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := hb
  have : b ∈ (Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K))).subgroupOf
      (adjointGroup Tag.G2 K) := hBN hb'
  rwa [Subgroup.subgroupOf_normalizer_eq (hUB.trans hBC)] at this

theorem g2Sub_exists_parabolic
    {K : Type} [Field K]
    (P₁ : Subgroup (adjointGroup Tag.G2 K))
    (hB : (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤ P₁) (hP₁ : P₁ ≠ ⊤) :
    ∃ J : Set (Fin Tag.G2.rank), J ≠ Set.univ ∧
      ∀ y ∈ P₁, (y : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J := by
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  set A : Subgroup (ModGL Tag.G2 K) := P₁.map (adjointGroup Tag.G2 K).subtype
  have hBA : borelGroup Tag.G2 K ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hB (show (⟨b, hBC hb⟩ : adjointGroup Tag.G2 K) ∈
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) from hb), rfl⟩
  have hAC : A ≤ adjointGroup Tag.G2 K := Subgroup.map_subtype_le _
  have hAJ := (borel_overgroup_classification Tag.G2 K).1 A hBA hAC
  refine ⟨{i | weylElt Tag.G2 K i 1 ∈ A}, fun huniv => hP₁ ?_, fun y hy => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have hy : (y : ModGL Tag.G2 K) ∈ A := by
      rw [hAJ, huniv, (standard_parabolic_cells Tag.G2 K).2.2.2.2.2.1]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  · rw [← hAJ]
    exact ⟨y, hy, rfl⟩

theorem g2Sub_not_dvd_card_torusGroup
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (torusGroup Tag.G2 K) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have := finite_modGL (τ := Tag.G2) (K := K)
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1' : (h : ModGL Tag.G2 K) ^ (Nat.card K - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h.2)
  have h2 : orderOf h ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1'))
  rw [hh] at h2
  exact h1 h2

theorem g2Sub_not_dvd_card_parabolic
    {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (h0 : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    (h2 : ¬ p ∣ Nat.card K + 1) {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    ¬ p ∣ Nat.card (parabolicSubgroup Tag.G2 K J) := by
  obtain ⟨j, hj⟩ := g2Sub_exists_subset_singleton hJ
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells Tag.G2 K
  rw [hcell J]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact g2Sub_not_dvd_card_torusGroup hp h1 h
    · exact h0 (hp.dvd_of_dvd_pow h)
  · rcases g2Sub_finsum_parabolicWeyl hj (Nat.card K) with hs | hs
    · rw [hs] at h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h)
    · rw [hs, add_comm] at h
      exact h2 h

theorem g2Sub_no_normalized_two_subgroup
    {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (h0 : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    (h2 : ¬ p ∣ Nat.card K + 1) (x : adjointGroup Tag.G2 K) (hx : orderOf x = p)
    (R : Subgroup (adjointGroup Tag.G2 K)) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : False := by
  have hfin : Finite (ModGL Tag.G2 K) := finite_modGL
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_right.trans hBC
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := holds_adjointGroup_tag Tag.G2 K 2 R hR hR2
  have hxP : x ∈ P := hNR (g2Sub_mem_normalizer hxR)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := g2Sub_exists_conj_le (hUp.toSylow hUi) S
    ((borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) P
    (by rw [hUc]; exact g2Sub_borel_le_normalizer) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := g2Sub_exists_parabolic _ hg hP₁top
  set x₁ : adjointGroup Tag.G2 K := g⁻¹ * x * g with hx₁
  have hconj : (MulAut.conj g) x₁ = x := by
    rw [MulAut.conj_apply, hx₁]
    group
  have hx₁P : x₁ ∈ P.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.mem_comap]
    exact (show (MulAut.conj g).toMonoidHom x₁ = x from hconj) ▸ hxP
  have hx₁ord : orderOf x₁ = p := by
    rw [← hx, ← hconj, MulEquiv.orderOf_eq]
  have hmem := hJP x₁ hx₁P
  have hdvd : p ∣ Nat.card (parabolicSubgroup Tag.G2 K J) := by
    have := orderOf_dvd_natCard (⟨(x₁ : ModGL Tag.G2 K), hmem⟩ : parabolicSubgroup Tag.G2 K J)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx₁ord] at this
  exact g2Sub_not_dvd_card_parabolic hp h0 h1 h2 hJ hdvd

theorem g2SubfieldCaseExcluded :
    G2SubfieldCaseExcluded := by
  intro T _ _ p hp hp5 hM _ q U _ _ hq1 hqp _ hU1 hU2 _ hqU _
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := p) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  obtain ⟨h0, h1, h2⟩ := g2Sub_two_pow_prime_arith hp hp5
  rw [← hKcard] at h0 h1 h2
  have hx : orderOf (e q) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hqp hq1
  refine g2Sub_no_normalized_two_subgroup hp h0 h1 h2 (e q) hx (U.map e.toMonoidHom) ?_
    (hU2.map e.toMonoidHom) ?_
  · intro hbot
    apply hU1
    exact (Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨q * u * q⁻¹, hqU u hu, by simp⟩

end CFSG.RankThree.PartOne.Sec66T
