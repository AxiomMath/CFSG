module

public import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.KFacts.KS10Wreath
public import CFSG.RankThree.PartTwo.KFacts.K73Direct

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

noncomputable abbrev barAct {G : Type*} [Group G] [Finite G] (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)

section Lemmas

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem mem_thetaQuotCentralizer_iff_barAct {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer L ↔ barAct L ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h1
    exact ⟨⟨x, hx⟩, h1, rfl⟩

theorem barAct_of_mem {y : G} (hy : y ∈ L) (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    barAct L ⟨y, hyN⟩ = MulAut.conj ((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  Sec11.thetaQuotMulAut_compAction_of_mem L hy

omit [Finite G] in
theorem exists_zpow_mul_of_mem_sup_zpowers' {H : Subgroup G} {x : G}
    (hN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G)) {y : G}
    (hy : y ∈ Subgroup.zpowers x ⊔ H) : ∃ k : ℤ, ∃ z ∈ H, y = x ^ k * z := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨k, z, hz, rfl⟩

omit [Finite G] in
theorem zpow_cases_of_pow_three {x : G} (hx : x ^ 3 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x ^ 2 := by
  have hx' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [zpow_eq_zpow_emod k hx']
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]))

theorem Sec10Std.a_mem_normalizer_inf (h : Sec10Std G A c L a R) :
    a ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
  have haR : a ∈ R := h.A_le_R h.a_mem
  have haL := h.toHyp81.a_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp haL x)]
  exact and_congr_left' (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haR) x)

theorem Sec10Std.card_T (h : Sec10Std G A c L a R) :
    Nat.card (Subgroup.zpowers a ⊔ (R ⊓ L) : Subgroup G) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 := h.pow_three h.a_mem
  have ha1 := h.a_ne_one
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (h.a_mem_normalizer_inf)
  rw [sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three ha3 fun haRL => h.a_not_mem_L haRL.2), h.card_inf,
    Nat.card_zpowers, orderOf_eq_prime ha3 ha1]

theorem Sec10Std.T_inf_Z (h : Sec10Std G A c L a R) :
    (Subgroup.zpowers a ⊔ (R ⊓ L)) ⊓ (R ⊓ Sec4.thetaQuotCentralizer L) = ⊥ := by
  have ha3 := h.pow_three h.a_mem
  have haN := h.toHyp81.a_mem_normalizer
  have hout := h.toHyp81.not_isInnerAut_induced
  rw [Subgroup.eq_bot_iff_forall]
  rintro t ⟨htT, -, htZ⟩
  obtain ⟨k, y, hy, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers'
    (Subgroup.zpowers_le.mpr (h.a_mem_normalizer_inf)) htT
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy.2
  have hakN : a ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ haN k
  have h1 := (mem_thetaQuotCentralizer_iff_barAct
    (Subgroup.mul_mem _ hakN hyN)).mp htZ
  have h2 : barAct L ⟨a ^ k * y, Subgroup.mul_mem _ hakN hyN⟩ =
      barAct L ⟨a, haN⟩ ^ k * barAct L ⟨y, hyN⟩ := by
    rw [← map_zpow, ← map_mul]
    rfl
  rw [h2, barAct_of_mem hy.2] at h1
  have hinner : KFacts.IsInnerAut (barAct L ⟨a, haN⟩ ^ k) := by
    rw [eq_inv_of_mul_eq_one_left h1, ← map_inv]
    exact ⟨_, rfl⟩
  rcases zpow_cases_of_pow_three ha3 k with hk | hk | hk
  · rw [hk, one_mul] at htZ ⊢
    exact h.eq_one_of_mem_inf_thetaQuotCentralizer hy.1 hy.2 htZ
  · exfalso
    apply hout
    have : barAct L ⟨a, haN⟩ ^ k = barAct L ⟨a, haN⟩ := by
      rw [← map_zpow]
      congr 1
      exact Subtype.ext hk
    rw [this] at hinner
    change KFacts.IsInnerAut (barAct L ⟨a, haN⟩)
    exact hinner
  · exfalso
    apply hout
    have h3 : barAct L ⟨a, haN⟩ ^ k = barAct L ⟨a, haN⟩ ^ 2 := by
      rw [← map_zpow, ← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hk)
    rw [h3] at hinner
    have h4 : barAct L ⟨a, haN⟩ = (barAct L ⟨a, haN⟩ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, pow_one]
      have h5 : barAct L ⟨a, haN⟩ ^ 3 = 1 := h.toHyp81.induced_pow_three
      rw [h5, one_mul]
    change KFacts.IsInnerAut (barAct L ⟨a, haN⟩)
    rw [h4]
    exact Subgroup.pow_mem _ hinner 2

theorem Sec10Std.exists_mul_of_mem_R (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) {r : G}
    (hr : r ∈ R) : ∃ t ∈ Subgroup.zpowers a ⊔ (R ⊓ L), ∃ z ∈ R ⊓ Sec4.thetaQuotCentralizer L,
      r = t * z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eL⟩ := h.exists_mulEquiv_psl2
  have hRN := h.R_le_normalizer h45
  set T := Subgroup.zpowers a ⊔ (R ⊓ L) with hT
  have hTR : T ≤ R := sup_le (Subgroup.zpowers_le.mpr (h.A_le_R h.a_mem)) inf_le_left
  set ρ : R →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (barAct L).comp (Subgroup.inclusion hRN) with hρ
  have hR3 : IsPGroup 3 R := h.isPGroup_R
  have hρ3 : IsPGroup 3 ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact (IsPGroup.of_equiv hR3 (Subgroup.topEquiv).symm).map ρ
  have hρcard : Nat.card ρ.range ≤ 81 := KFacts.card_le_of_isPGroup_three_mulAut eL hρ3
  have hρ1 : ∀ x : R, ρ x = 1 → (x : G) ∈ Sec4.thetaQuotCentralizer L := fun x hx =>
    (mem_thetaQuotCentralizer_iff_barAct (hRN x.2)).mpr hx
  set T' := T.subgroupOf R with hT'
  have hinj : Function.Injective (ρ.comp T'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : ((x : R) : G) ∈ T ⊓ (R ⊓ Sec4.thetaQuotCentralizer L) :=
      ⟨Subgroup.mem_subgroupOf.mp x.2, (x : R).2, hρ1 x hx⟩
    rw [h.T_inf_Z, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hT'card : Nat.card T' = 81 := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv, h.card_T]
  have hle : (ρ.comp T'.subtype).range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have himg : (ρ.comp T'.subtype).range = ρ.range := Subgroup.eq_of_le_of_card_ge hle (by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hT'card]
    exact hρcard)
  obtain ⟨t', ht'⟩ : ρ ⟨r, hr⟩ ∈ (ρ.comp T'.subtype).range := himg ▸ ⟨⟨r, hr⟩, rfl⟩
  refine ⟨((t' : R) : G), Subgroup.mem_subgroupOf.mp t'.2, ((t' : R) : G)⁻¹ * r,
    ⟨R.mul_mem (R.inv_mem (t' : R).2) hr, ?_⟩, by group⟩
  have h1 : ρ ((t' : R)⁻¹ * ⟨r, hr⟩) = 1 := by
    rw [map_mul, map_inv, ← ht']
    exact inv_mul_cancel _
  exact hρ1 _ h1

omit [Finite G] in
theorem pow_three_eq_one_of_mul_pow_three {Z : Subgroup G} [IsCyclic Z] (hZ3 : IsPGroup 3 Z)
    {t z : G} (htN : t ∈ Subgroup.normalizer (Z : Set G)) (ht3 : t ^ 3 = 1) (hz : z ∈ Z)
    (h3 : (t * z) ^ 3 = 1) : z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
  have hZg : ∀ x ∈ Z, ∃ k : ℤ, (g : G) ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨m, hm⟩ := hZg _ ((Subgroup.mem_normalizer_iff.mp htN g).mp g.2)
  have hpow : ∀ x ∈ Z, t * x * t⁻¹ = x ^ m := by
    intro x hx
    obtain ⟨k, rfl⟩ := hZg x hx
    rw [← conj_zpow, ← hm, ← zpow_mul, ← zpow_mul, mul_comm]
  have hzm : z ^ m ∈ Z := Z.zpow_mem hz m
  have ht3' : t * t * t = 1 := by rw [← pow_three']; exact ht3
  have h2 : (t * t) * z * (t * t)⁻¹ = z ^ (m * m) := by
    calc (t * t) * z * (t * t)⁻¹ = t * (t * z * t⁻¹) * t⁻¹ := by group
      _ = z ^ (m * m) := by rw [hpow z hz, hpow _ hzm, ← zpow_mul]
  have h3' : z ^ (m + m * m + 1) = 1 := by
    have e1 : (t * z) ^ 3 = (t * z * t⁻¹) * ((t * t) * z * (t * t)⁻¹) *
        ((t * t * t) * z * (t * t * t)⁻¹) * (t * t * t) := by
      rw [pow_three]
      group
    rw [e1, ht3', one_mul, inv_one, mul_one, mul_one, hpow z hz, h2] at h3
    rw [zpow_add, zpow_add, zpow_one]
    exact h3
  have hg3 : (g : G) ^ (m * m * m - 1) = 1 := by
    have hgZ : (g : G) ∈ Z := g.2
    have hgm : (g : G) ^ m ∈ Z := Z.zpow_mem hgZ m
    have hgmm : (g : G) ^ (m * m) ∈ Z := Z.zpow_mem hgZ (m * m)
    have e3 : (t * t * t) * (g : G) * (t * t * t)⁻¹ = (g : G) ^ (m * m * m) := by
      calc (t * t * t) * (g : G) * (t * t * t)⁻¹ = t * (t * (t * (g : G) * t⁻¹) * t⁻¹) * t⁻¹ := by
            group
        _ = (g : G) ^ (m * m * m) := by
          rw [hpow _ hgZ, hpow _ hgm, ← zpow_mul, hpow _ hgmm, ← zpow_mul]
    rw [ht3', one_mul, inv_one, mul_one] at e3
    rw [zpow_sub, zpow_one, ← e3, mul_inv_cancel]
  by_contra hz3
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hZ3) ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj2 : 2 ≤ j := by
    by_contra hj2
    apply hz3
    have : orderOf z ∣ 3 := by
      rw [hj]
      interval_cases j <;> simp
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have h9z : (9 : ℤ) ∣ (orderOf z : ℤ) := by
    rw [hj]
    exact_mod_cast (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)
  have hzg : orderOf z ∣ orderOf (g : G) := by
    obtain ⟨k, rfl⟩ := hZg z hz
    exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers _ k)
  have h9a : (9 : ℤ) ∣ m * m * m - 1 :=
    h9z.trans ((Int.natCast_dvd_natCast.mpr hzg).trans (orderOf_dvd_iff_zpow_eq_one.mpr hg3))
  have h9b : (9 : ℤ) ∣ m + m * m + 1 := h9z.trans (orderOf_dvd_iff_zpow_eq_one.mpr h3')
  have key : ∀ x : ZMod 9, x * x * x = 1 → x + x * x + 1 ≠ 0 := by decide
  apply key (m : ZMod 9)
  · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m * m * m - 1) 9).mpr (by exact_mod_cast h9a)
    push_cast at this
    exact sub_eq_zero.mp this
  · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (m + m * m + 1) 9).mpr (by exact_mod_cast h9b)
    push_cast at this
    exact this

end Lemmas

theorem rank3II_10_2 (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) : Item102 := by
  intro G _ _ A c L a R h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdL, hdo, hA⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  set T := Subgroup.zpowers a ⊔ (R ⊓ L) with hT
  set Z := R ⊓ Sec4.thetaQuotCentralizer L with hZ
  set D := sec10D c R L with hDdef
  have hc3 := h.pow_three h.mem_A
  have ha3 := h.pow_three h.a_mem
  have hcR : c ∈ R := h.A_le_R h.mem_A
  have haR : a ∈ R := h.A_le_R h.a_mem
  have hcZ : c ∈ Z := ⟨hcR, h.c_mem_thetaQuotCentralizer⟩
  have hTR : T ≤ R := sup_le (Subgroup.zpowers_le.mpr haR) inf_le_left
  have hDR : D ≤ R := sup_le (Subgroup.zpowers_le.mpr hcR) inf_le_left
  have hRN := h.R_le_normalizer h45
  have hZcyc : IsCyclic Z := rank3II_10_1 G A c L a R h
  have hZ3 : IsPGroup 3 Z := h.isPGroup_R.to_inf_left
  have hZN : ∀ t ∈ R, t ∈ Subgroup.normalizer (Z : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, Sec6.normalizer_le_normalizer_thetaQuotCentralizer L (hRN ht)⟩
  have hTZ := h.T_inf_Z
  have hdRL := h.d_mem_inf hdL
  have hdA := h.d_mem_A hdL
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hCa := h.inf_centralizer_a hdL hA
  obtain ⟨e, heRL, heB⟩ := KFacts.exists_eBase_eq h.isElemAbelian_inf h.card_inf ha3
    h.a_mem_normalizer_inf hdRL hd1 (by rw [h.comm h.a_mem hdA, mul_inv_cancel_right])
    (fun x hx hxa => by
      rw [← hCa]
      refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * a = a * x * a⁻¹ * a := by rw [hxa]
        _ = a * x := by group)
  have hW : KFacts.WreathData e a :=
    ⟨h.isElemAbelian_inf.2 e heRL, ha3, by
      have h1 : KFacts.eConj e a 1 ∈ R ⊓ L := heB ▸ KFacts.eConj_mem_eBase (Or.inr (Or.inl rfl))
      exact congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨e, heRL⟩ ⟨_, h1⟩),
      by rw [heB, h.card_inf], by rw [heB]; exact fun haRL => h.a_not_mem_L haRL.2⟩
  have hcl : Subgroup.closure {e, a} = Subgroup.zpowers a ⊔ (R ⊓ L) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_right heRL
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) ?_
      rw [← heB]
      exact hW.eBase_le
  have hcT : c ∉ T := by
    intro hcT
    have : c ∈ T ⊓ Z := ⟨hcT, hcZ⟩
    rw [hTZ, Subgroup.mem_bot] at this
    exact h.ne_one this
  have hcube : ∀ y ∈ R, y ^ 3 = 1 → ∃ t ∈ T, ∃ z ∈ Subgroup.zpowers c, y = t * z := by
    intro y hyR hy3
    obtain ⟨t, htT, z, hzZ, rfl⟩ := h.exists_mul_of_mem_R h45 hyR
    have htR := hTR htT
    have htN := hZN t htR
    have htN' := Subgroup.inv_mem _ htN
    have hw : t⁻¹ * t⁻¹ * z * t * t * (t⁻¹ * z * t) * z ∈ Z := by
      have h1 : t⁻¹ * z * t ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp htN' z).mp hzZ
        simpa using this
      have h2 : t⁻¹ * (t⁻¹ * z * t) * t ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp htN' _).mp h1
        simpa using this
      have e2 : t⁻¹ * t⁻¹ * z * t * t = t⁻¹ * (t⁻¹ * z * t) * t := by group
      rw [e2]
      exact Z.mul_mem (Z.mul_mem h2 h1) hzZ
    have ht3Z : t ^ 3 ∈ Z := by
      have e1 : (t * z) ^ 3 = t ^ 3 * (t⁻¹ * t⁻¹ * z * t * t * (t⁻¹ * z * t) * z) := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      have e2 : t ^ 3 = (t * z) ^ 3 * (t⁻¹ * t⁻¹ * z * t * t * (t⁻¹ * z * t) * z)⁻¹ := by
        rw [e1, mul_inv_cancel_right]
      rw [e2, hy3, one_mul]
      exact Z.inv_mem hw
    have ht3 : t ^ 3 = 1 := by
      have : t ^ 3 ∈ T ⊓ Z := ⟨T.pow_mem htT 3, ht3Z⟩
      rwa [hTZ, Subgroup.mem_bot] at this
    have hz3 := pow_three_eq_one_of_mul_pow_three hZ3 htN ht3 hzZ hy3
    exact ⟨t, htT, z, h.mem_zpowers_of_mem_thetaQuotCentralizer hzZ.1 hzZ.2 hz3, rfl⟩
  have hTD : T ≤ Subgroup.zpowers a ⊔ D := sup_le_sup_left le_sup_right _
  have hΩ : Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1} = Subgroup.zpowers a ⊔ D := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y ⟨hyR, hy3⟩
      obtain ⟨t, htT, z, hz, rfl⟩ := hcube y hyR hy3
      exact Subgroup.mul_mem _ (hTD htT) (Subgroup.mem_sup_right (Subgroup.mem_sup_left hz))
    · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨haR, ha3⟩))
        (sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hcR, hc3⟩)) ?_)
      intro x hx
      exact Subgroup.subset_closure ⟨hx.1, h.isElemAbelian_inf.2 x hx⟩
  refine ⟨hΩ, ⟨e, heRL, hW, hcl⟩, hcT, ?_⟩
  by_cases hZc : Z = Subgroup.zpowers c
  ·
    refine Or.inl ⟨hZc, le_antisymm ?_ (sup_le (Subgroup.zpowers_le.mpr haR) hDR)⟩
    intro r hr
    obtain ⟨t, htT, z, hzZ, rfl⟩ := h.exists_mul_of_mem_R h45 hr
    have hzc : z ∈ Z := hzZ
    rw [hZc] at hzc
    exact Subgroup.mul_mem _ (hTD htT) (Subgroup.mem_sup_right (Subgroup.mem_sup_left hzc))
  ·
    right
    set CD := R ⊓ Subgroup.centralizer (D : Set G) with hCD
    have hΩ' : Subgroup.zpowers a ⊔ D = Subgroup.zpowers c ⊔ Subgroup.closure {e, a} := by
      rw [hcl, hDdef, sec10D, ← sup_assoc, sup_comm (Subgroup.zpowers a), sup_assoc]
    have hce : Commute c e := (h.commute_c_of_mem_inf heRL).symm
    have hca : Commute c a := h.comm h.mem_A h.a_mem
    have hcT' : c ∉ Subgroup.closure ({e, a} : Set G) := by rw [hcl]; exact hcT
    have hc1 : ∀ σ : MulAut R, ∀ x (hx : x ∈ D), ((σ ⟨x, hDR hx⟩ : R) : G) ∈ D := by
      intro σ x hx
      set D1 : Subgroup G := (D.subgroupOf R).map (R.subtype.comp σ.toMonoidHom) with hD1
      have hDe : ∀ y : R, y ∈ D.subgroupOf R → y ^ 3 = 1 := fun y hy =>
        Subtype.ext (by simpa using h.isElemAbelian_D.2 y (Subgroup.mem_subgroupOf.mp hy))
      have hD1le : D1 ≤ Subgroup.zpowers c ⊔ Subgroup.closure {e, a} := by
        rw [← hΩ', ← hΩ]
        rintro _ ⟨y, hy, rfl⟩
        apply Subgroup.subset_closure
        refine ⟨(σ y).2, ?_⟩
        change ((σ y : R) : G) ^ 3 = 1
        rw [← Subgroup.coe_pow, ← map_pow, hDe y hy, map_one, Subgroup.coe_one]
      have hD1ab : ∀ u ∈ D1, ∀ v ∈ D1, u * v = v * u := by
        rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
        have hyy' : y * y' = y' * y := Subtype.ext (by
          simpa using congrArg Subtype.val
            (h.isElemAbelian_D.1.is_comm.comm ⟨y, Subgroup.mem_subgroupOf.mp hy⟩
              ⟨y', Subgroup.mem_subgroupOf.mp hy'⟩))
        change ((σ y : R) : G) * ((σ y' : R) : G) = ((σ y' : R) : G) * ((σ y : R) : G)
        rw [← Subgroup.coe_mul, ← map_mul, hyy', map_mul, Subgroup.coe_mul]
      have hD1card : 81 ≤ Nat.card D1 := by
        rw [hD1, Subgroup.card_map_of_injective (f := R.subtype.comp σ.toMonoidHom)
            (fun x y hxy => σ.injective (Subtype.ext hxy)),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, h.card_D]
      have hD1eq := hW.eq_of_abelian hc3 hce hca hcT' hD1le hD1ab hD1card
      have hmem : ((σ ⟨x, hDR hx⟩ : R) : G) ∈ D1 := ⟨⟨x, hDR hx⟩, hx, rfl⟩
      rw [hD1eq, heB] at hmem
      exact hmem
    have hc2 : ∀ σ : MulAut R, ∀ x (hx : x ∈ CD), ((σ ⟨x, hx.1⟩ : R) : G) ∈ CD := by
      intro σ x hx
      refine ⟨(σ ⟨x, hx.1⟩).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      set y' : R := σ⁻¹ ⟨y, hDR hy⟩ with hy'
      have hy'D : (y' : G) ∈ D := hc1 σ⁻¹ y hy
      have hxy : (y' : G) * x = x * y' := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'D
      have hσy : σ y' = ⟨y, hDR hy⟩ := by
        rw [hy', MulAut.inv_def, MulEquiv.apply_symm_apply]
      have h1 : y' * ⟨x, hx.1⟩ = ⟨x, hx.1⟩ * y' := Subtype.ext hxy
      have h2 := congrArg (fun w => ((σ w : R) : G)) h1
      simp only [map_mul, Subgroup.coe_mul, hσy] at h2
      exact h2
    have hc3' : ∀ x ∈ CD, (x ^ 3) ^ 3 = 1 → x ^ 3 ∈ Subgroup.zpowers c := by
      intro x hx hx9
      obtain ⟨t, htT, z, hzZ, rfl⟩ := h.exists_mul_of_mem_R h45 hx.1
      have hzRL : ∀ y ∈ R ⊓ L, y * z = z * y := fun y hy =>
        h.commute_of_mem_thetaQuotCentralizer hzZ.1 hzZ.2 hy
      have htRL : ∀ y ∈ R ⊓ L, y * t = t * y := by
        intro y hy
        have h1 : y * (t * z) = t * z * y :=
          Subgroup.mem_centralizer_iff.mp hx.2 y (Subgroup.mem_sup_right hy)
        calc y * t = y * (t * z) * z⁻¹ := by group
          _ = t * z * y * z⁻¹ := by rw [h1]
          _ = t * (z * y) * z⁻¹ := by group
          _ = t * (y * z) * z⁻¹ := by rw [hzRL y hy]
          _ = t * y := by group
      obtain ⟨k, y0, hy0, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers'
        (Subgroup.zpowers_le.mpr h.a_mem_normalizer_inf) htT
      have hak : ∀ y ∈ R ⊓ L, y * a ^ k = a ^ k * y := by
        intro y hy
        have h1 := htRL y hy
        have h2 : y * y0 = y0 * y :=
          congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨y, hy⟩ ⟨y0, hy0⟩)
        calc y * a ^ k = y * (a ^ k * y0) * y0⁻¹ := by group
          _ = a ^ k * y0 * y * y0⁻¹ := by rw [h1]
          _ = a ^ k * (y0 * y) * y0⁻¹ := by group
          _ = a ^ k * (y * y0) * y0⁻¹ := by rw [h2]
          _ = a ^ k * y := by group
      have hak1 : a ^ k = 1 := by
        have hnot : ¬ ∀ y ∈ R ⊓ L, y * a = a * y := by
          intro hall
          have hle : R ⊓ L ≤ Subgroup.zpowers d := by
            rw [← hCa]
            intro y hy
            exact Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr (hall y hy)⟩
          have h1 := Subgroup.card_le_of_le hle
          rw [h.card_inf, Nat.card_zpowers, hdo] at h1
          norm_num at h1
        rcases zpow_cases_of_pow_three ha3 k with hk | hk | hk
        · exact hk
        · exact absurd (fun y hy => hk ▸ hak y hy) hnot
        · exfalso
          apply hnot
          intro y hy
          have h2 := hak y hy
          rw [hk] at h2
          calc y * a = y * (a ^ 2) ^ 2 := by
                rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
            _ = (a ^ 2) ^ 2 * y := by rw [pow_two (a ^ 2), ← mul_assoc, h2, mul_assoc, h2,
                mul_assoc]
            _ = a * y := by
                rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
      rw [hak1, one_mul] at hx9 ⊢
      have hyz : y0 * z = z * y0 := hzRL y0 hy0
      have hcube : (y0 * z) ^ 3 = z ^ 3 := by
        rw [(Commute.mul_pow hyz), h.isElemAbelian_inf.2 y0 hy0, one_mul]
      rw [hcube] at hx9 ⊢
      exact h.mem_zpowers_of_mem_thetaQuotCentralizer (Z.pow_mem hzZ 3).1 (Z.pow_mem hzZ 3).2 hx9
    have hZCD : Z ≤ CD := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hle : D ≤ Subgroup.centralizer ({z} : Set G) := by
        apply sup_le
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hz.1)).symm
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact h.commute_of_mem_thetaQuotCentralizer hz.1 hz.2 hy
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    obtain ⟨x0, hx0, hx0c⟩ : ∃ x0 ∈ Z, x0 ^ 3 = c := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
      obtain ⟨n, hn⟩ := hZ3.exists_card_eq
      have hgord : orderOf (g : G) = 3 ^ n := by
        rw [Subgroup.orderOf_coe, ← hn, ← Nat.card_zpowers, (Subgroup.eq_top_iff' _).mpr hg,
          Subgroup.card_top]
      have hn2 : 2 ≤ n := by
        by_contra hn2
        interval_cases n
        · rw [pow_zero] at hn
          have : (⟨c, hcZ⟩ : Z) = 1 := (Nat.card_eq_one_iff_unique.mp hn).1.elim _ _
          exact h.ne_one (congrArg Subtype.val this)
        · apply hZc
          symm
          apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcZ)
          rw [hn, pow_one, Nat.card_zpowers, h.orderOf_c]
      set x : G := (g : G) ^ 3 ^ (n - 2) with hx
      have hxZ : x ∈ Z := Z.pow_mem g.2 _
      have hx3 : x ^ 3 = (g : G) ^ 3 ^ (n - 1) := by
        rw [hx, ← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega]
      have hx31 : x ^ 3 ≠ 1 := by
        rw [hx3]
        exact pow_ne_one_of_lt_orderOf (pow_ne_zero _ (by norm_num))
          (by rw [hgord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
      have hx39 : (x ^ 3) ^ 3 = 1 := by
        rw [hx3, ← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hgord, pow_orderOf_eq_one]
      have hx3c : x ^ 3 ∈ Subgroup.zpowers c :=
        h.mem_zpowers_of_mem_thetaQuotCentralizer (Z.pow_mem hxZ 3).1 (Z.pow_mem hxZ 3).2 hx39
      have hcx := KFacts.mem_zpowers_of_mem_zpowers_of_ne_one' h.orderOf_c hx3c hx31
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcx
      refine ⟨x ^ k, Z.zpow_mem hxZ k, ?_⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk]
    have hσc : ∀ σ : MulAut R, ((σ ⟨c, hcR⟩ : R) : G) ∈ Subgroup.zpowers c := by
      intro σ
      have hx0R : x0 ∈ R := hx0.1
      have h1 : σ ⟨c, hcR⟩ = (σ ⟨x0, hx0R⟩) ^ 3 := by
        rw [← map_pow]
        congr 1
        exact Subtype.ext hx0c.symm
      rw [h1, Subgroup.coe_pow]
      apply hc3' _ (hc2 σ x0 (hZCD hx0))
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← h1, ← map_pow]
      have : (⟨c, hcR⟩ : R) ^ 3 = 1 := Subtype.ext hc3
      rw [this, map_one, Subgroup.coe_one]
    have hchar : ∀ σ : MulAut R, ((Subgroup.zpowers c).subgroupOf R).map σ.toMonoidHom =
        (Subgroup.zpowers c).subgroupOf R := by
      intro σ
      have hle : ((Subgroup.zpowers c).subgroupOf R).map σ.toMonoidHom ≤
          (Subgroup.zpowers c).subgroupOf R := by
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hw)
        have hw' : w = (⟨c, hcR⟩ : R) ^ k := Subtype.ext (by rw [← hk]; simp)
        rw [Subgroup.mem_subgroupOf, hw']
        change ((σ ((⟨c, hcR⟩ : R) ^ k) : R) : G) ∈ _
        rw [map_zpow, Subgroup.coe_zpow]
        exact Subgroup.zpow_mem _ (hσc σ) k
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective σ.injective])
    refine ⟨hchar, Sec12.isSylowOf_of_normalizer_le h.isSylowOf le_top ?_⟩
    rintro n ⟨-, hn⟩
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have h1 := hσc (R.normalizerMonoidHom ⟨n, hn⟩)
    rwa [Sec4.normalizerMonoidHom_apply_coe] at h1

end CFSG.RankThree.PartTwo.Sec10

namespace CFSG.RankThree.PartTwo.Sec10

theorem rank3II_10_3 (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) : Item103 :=
  item103_of h97 (rank3II_10_2 h45 h97)

end CFSG.RankThree.PartTwo.Sec10
