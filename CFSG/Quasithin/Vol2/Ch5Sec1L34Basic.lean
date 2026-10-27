module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

structure Hyp5_1_14 (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ) :
    Prop where
  hyp : Hyp5_1_8 G T M L H n
  notation59 : IsNotation5_1_9 T M L H B D
  module : IsCh5Module T L V
  l34 : LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2

section General

variable {G : Type} [Group G]

theorem center_eq_bot_of_isSimpleGroup_of_card_nine {X : Type} [Group X] [IsSimpleGroup X]
    {E : Subgroup X} (hE : Nat.card E = 9) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    have hdvd : 9 ∣ Nat.card X := hE ▸ Subgroup.card_subgroup_dvd_card E
    have h3 : 3 ∣ Nat.card X := (show 3 ∣ 9 by norm_num).trans hdvd
    have h3eq : Nat.card X = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    rw [h3eq] at hdvd
    norm_num at hdvd

theorem mem_pCoreOf_of_mem_centralizerModO2 {K : Subgroup G}
    (hZ : Subgroup.center (O2Q K) = ⊥) {k : G} (hk : k ∈ K) (hc : k ∈ centralizerModO2 K) :
    k ∈ pCoreOf 2 K := by
  have hcen : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : O2Q K) ∈ Subgroup.center (O2Q K) := by
    rw [Subgroup.mem_center_iff]
    intro u
    induction u using QuotientGroup.induction_on with
    | H u =>
      have hu := hc.2.2 (u : G) u.2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hmem : (⟨k * u * k⁻¹ * u⁻¹, K.mul_mem (K.mul_mem (K.mul_mem hk u.2) (K.inv_mem hk))
          (K.inv_mem u.2)⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
        obtain ⟨y, hy, hyx⟩ := hu
        have hy' : y = ⟨k * u * k⁻¹ * u⁻¹, K.mul_mem (K.mul_mem (K.mul_mem hk u.2)
            (K.inv_mem hk)) (K.inv_mem u.2)⟩ := Subtype.ext hyx
        rw [← hy']
        exact hy
      have e : (u * ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ * u) =
          (u * ⟨k, hk⟩)⁻¹ * (⟨k * u * k⁻¹ * u⁻¹, K.mul_mem (K.mul_mem (K.mul_mem hk u.2)
            (K.inv_mem hk)) (K.inv_mem u.2)⟩ : ↥K) * (u * ⟨k, hk⟩)⁻¹⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      have hn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
      exact hn.conj_mem _ hmem _
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  exact ⟨⟨k, hk⟩, hcen, rfl⟩

theorem commutator_mem_of_mem_centralizerModO2 {K : Subgroup G} {x k : G}
    (hx : x ∈ centralizerModO2 K) (hk : k ∈ K) : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
  hx.2.2 k hk

theorem pRank_le_two_of_isTwoLocal [Finite G] (hQ : quasithinIsQTKECat G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H : Subgroup G} (hH : IsTwoLocal H) : CFSG.Open.pRank p H ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 H hH).trans hQ.2.2

theorem not_three_dvd_card_centralizerModO2
    [Finite G] (hE9 : L34ElemNineFact) {K : Subgroup G}
    (hK : LieModel (O2Q K) .PSL 3 2 2)
    (hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (K : Set G)) ≤ 2) :
    ¬ 3 ∣ Nat.card (centralizerModO2 K) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEcard, hEcomm, hEpow⟩ := hE9 _ hK
  have : IsSimpleGroup (O2Q K) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK
  have hZ : Subgroup.center (O2Q K) = ⊥ := center_eq_bot_of_isSimpleGroup_of_card_nine hEcard
  obtain ⟨⟨x, hxC⟩, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3' : orderOf x = 3 := by rw [← Subgroup.orderOf_mk x hxC]; exact hx3
  set Mp := Subgroup.normalizer (K : Set G) with hMp
  set Q := pCoreOf 2 K with hQdef
  have hKMp : K ≤ Mp := Subgroup.le_normalizer
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hQMp : Q ≤ Mp := hQK.trans hKMp
  have hxMp : x ∈ Mp := hxC.1
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 K
  have hQn : (Q.subgroupOf Mp).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMp).mpr
      (normalizer_le_normalizer_pCoreOf 2 K)
  set π := QuotientGroup.mk' (Q.subgroupOf Mp) with hπ
  set ι₀ : ↥K →* ↥Mp ⧸ Q.subgroupOf Mp := π.comp (Subgroup.inclusion hKMp) with hι₀
  have hker : CFSG.pCore 2 ↥K ≤ ι₀.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hι₀, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨k, hk, rfl⟩
  set ι : O2Q K →* ↥Mp ⧸ Q.subgroupOf Mp := QuotientGroup.lift _ ι₀ hker with hι
  have hι_mk : ∀ k : ↥K, ι (QuotientGroup.mk k) = ι₀ k := fun k => rfl
  have hι_inj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [hι_mk, hι₀, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyx⟩ := hq
      have : y = k := Subtype.ext hyx
      rw [← this]
      exact hy
  set xb : ↥Mp ⧸ Q.subgroupOf Mp := π ⟨x, hxMp⟩ with hxb
  have hQN : Mp ≤ Subgroup.normalizer (Q : Set G) := normalizer_le_normalizer_pCoreOf 2 K
  have hcommK : ∀ k : ↥K, xb * ι₀ k = ι₀ k * xb := by
    intro k
    rw [hxb, hι₀, MonoidHom.comp_apply, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc := commutator_mem_of_mem_centralizerModO2 hxC k.2
    have hn : (x * k : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      hQN (Mp.inv_mem (Mp.mul_mem hxMp (hKMp k.2)))
    have hmem := (Subgroup.mem_normalizer_iff.mp hn _).mp (Q.inv_mem hc)
    have e : (((⟨x, hxMp⟩ * Subgroup.inclusion hKMp k : ↥Mp)⁻¹ *
        (Subgroup.inclusion hKMp k * ⟨x, hxMp⟩) : ↥Mp) : G) =
        (x * k : G)⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹ * (x * k : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      group
    rw [e]
    exact hmem
  have hcomm : ∀ q : O2Q K, xb * ι q = ι q * xb := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k => exact hcommK k
  have hxK : x ∉ K := by
    intro hxK
    have hxQ := mem_pCoreOf_of_mem_centralizerModO2 hZ hxK hxC
    obtain ⟨m, hm⟩ := hQ2 ⟨x, hxQ⟩
    have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hd : 3 ∣ 2 ^ m := hx3' ▸ orderOf_dvd_of_pow_eq_one hm'
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)) (by norm_num)
  have hxb_range : ∀ q : O2Q K, ι q = xb → False := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [hι_mk, hι₀, MonoidHom.comp_apply, hxb, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      apply hxK
      have h1 : ((Subgroup.inclusion hKMp k)⁻¹ * ⟨x, hxMp⟩ : ↥Mp) ∈ Q.subgroupOf Mp := hq
      have h2 : (k : G)⁻¹ * x ∈ K := by
        have := hQK (Subgroup.mem_subgroupOf.mp h1)
        simpa using this
      have := K.mul_mem k.2 h2
      simpa using this
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxMp⟩ : ↥Mp) ^ 3 = 1 := Subtype.ext (by simp [← hx3', pow_orderOf_eq_one])
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := fun h => hxb_range 1 (by rw [map_one, h])
  have hxbord : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb1
  have hcomm' : ∀ (c : ↥(Subgroup.zpowers xb)) (e : ↥E),
      Commute ((Subgroup.zpowers xb).subtype c) ((ι.comp E.subtype) e) := by
    rintro ⟨c, hc⟩ e
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_left (hcomm (e : O2Q K)) i
  set f := MonoidHom.noncommCoprod (Subgroup.zpowers xb).subtype (ι.comp E.subtype) hcomm'
    with hf
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨c, hc⟩, e⟩ h
    rw [hf, MonoidHom.noncommCoprod_apply] at h
    simp only [Subgroup.coe_subtype, MonoidHom.coe_comp, Function.comp_apply] at h
    have hce : c = (ι (e : O2Q K))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hc1 : c = 1 := by
      by_contra hne
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hi : ¬ (3 : ℤ) ∣ i := by
        intro hdvd
        apply hne
        obtain ⟨j, rfl⟩ := hdvd
        rw [zpow_mul, show xb ^ (3 : ℤ) = 1 by exact_mod_cast hxb3, one_zpow]
      obtain ⟨j, hj⟩ : ∃ j : ℤ, i * j % 3 = 1 := by
        refine ⟨i % 3, ?_⟩
        have : i % 3 = 1 ∨ i % 3 = 2 := by omega
        rcases this with h | h <;> · rw [Int.mul_emod, h]; omega
      have hxbpow : xb = (xb ^ i) ^ j := by
        rw [← zpow_mul, ← zpow_mod_orderOf, hxbord]
        push_cast
        rw [hj, zpow_one]
      apply hxb_range ((e : O2Q K)⁻¹ ^ j)
      rw [map_zpow, map_inv, hxbpow, hce]
    have he1 : ι (e : O2Q K) = 1 := by
      rw [hc1] at hce
      exact inv_eq_one.mp hce.symm
    have he : (e : O2Q K) = 1 := hι_inj (by rw [he1, map_one])
    refine Prod.ext (Subtype.ext hc1) (Subtype.ext he)
  have hAcomm : ∀ a b : ↥(Subgroup.zpowers xb) × ↥E, a * b = b * a := by
    rintro ⟨⟨c, hc⟩, ⟨e, he⟩⟩ ⟨⟨c', hc'⟩, ⟨e', he'⟩⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hEcomm e he e' he'))
    show xb ^ i * xb ^ i' = xb ^ i' * xb ^ i
    rw [← zpow_add, ← zpow_add, add_comm]
  have hpow1 : ∀ c : ↥(Subgroup.zpowers xb), c ^ 3 = 1 := by
    rintro ⟨c, hc⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    show (xb ^ i) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show xb ^ ((3 : ℕ) : ℤ) = 1 by
      exact_mod_cast hxb3, one_zpow]
  have hpow2 : ∀ e : ↥E, e ^ 3 = 1 := fun e => Subtype.ext (by simpa using hEpow e e.2)
  have hApow : ∀ a : ↥(Subgroup.zpowers xb) × ↥E, a ^ 3 = 1 := fun a =>
    Prod.ext (by rw [Prod.pow_fst, hpow1, Prod.fst_one]) (by rw [Prod.pow_snd, hpow2, Prod.snd_one])
  have hAcard : Nat.card (↥(Subgroup.zpowers xb) × ↥E) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_zpowers, hxbord, hEcard]
    norm_num
  have h27 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥Mp ⧸ Q.subgroupOf Mp)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hAcomm hApow hAcard f hf_inj le_top
  have hQcard : ¬ 3 ∣ Nat.card (Q.subgroupOf Mp) := by
    intro h
    have hQ2' : IsPGroup 2 (Q.subgroupOf Mp) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQMp).symm
    obtain ⟨m, hm⟩ := hQ2'.exists_card_eq
    rw [hm] at h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hQcard] at h27
  have h3' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Mp) ≤ CFSG.Open.pRank 3 Mp := by
    have := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) Mp.subtype
      Mp.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have := h27.trans (h3'.trans hrank)
  omega

@[expose] noncomputable def quotConjFun (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) :
    MulAut (O2Q X) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥X) (X.normalizerMonoidHom g)
    (by exact Subgroup.characteristic_iff_map_eq.mp inferInstance _)

theorem quotConjFun_mk (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥X) :
    quotConjFun X g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨g * x * (g : G)⁻¹, (g.2 x).mp x.2⟩ : ↥X) :=
  rfl

@[expose] noncomputable def quotConjAut (X : Subgroup G) :
    ↥(Subgroup.normalizer (X : Set G)) →* MulAut (O2Q X) where
  toFun := quotConjFun X
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [quotConjFun_mk]
      congr 1
      apply Subtype.ext
      simp
  map_mul' g h := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, quotConjFun_mk, quotConjFun_mk, quotConjFun_mk]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]

theorem quotConjAut_mk (X : Subgroup G) (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥X) :
    quotConjAut X g (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨g * x * (g : G)⁻¹, (g.2 x).mp x.2⟩ : ↥X) :=
  rfl

theorem commutator_mem_of_quotConjAut_eq_one {X : Subgroup G}
    {g : ↥(Subgroup.normalizer (X : Set G))} (hg : quotConjAut X g = 1) (x : ↥X) :
    (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 X := by
  have h := congrArg (fun α : MulAut (O2Q X) => α (QuotientGroup.mk x)) hg
  simp only [quotConjAut_mk, MulAut.one_apply] at h
  rw [QuotientGroup.eq] at h
  have hmem : (⟨g * x * (g : G)⁻¹, (g.2 x).mp x.2⟩ : ↥X)⁻¹ * x ∈ CFSG.pCore 2 ↥X := h
  have hn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hmem' := hn.conj_mem _ (inv_mem hmem) x
  refine ⟨_, hmem', ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  group

theorem pCoreOf_ne_bot_of_isTwoLocal {X : Subgroup G} (hX : IsTwoLocal X) :
    pCoreOf 2 X ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hX
  intro hbot
  apply hP1
  have hle : P ≤ pCoreOf 2 (Subgroup.normalizer (P : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
  rw [hbot] at hle
  exact le_bot_iff.mp hle

end General

end CFSG.Quasithin.H13
