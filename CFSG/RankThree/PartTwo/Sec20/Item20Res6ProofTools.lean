module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofCyclic
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.Sec20.OneTools
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

namespace Res6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : g ∈ Subgroup.normalizer (H₂ : Set G)) :
    g ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_sup, h₁, h₂]

omit [Finite G] in
theorem normalizer_le_normalizer_inSubgroup_pPrimeCore (p : ℕ) (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore p) H : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

omit [Finite G] in
theorem le_normalizer_inSubgroup_pPrimeCore (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore p) H : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_inSubgroup_pPrimeCore p H)

omit [Finite G] in
theorem inSubgroup_pPrimeCore_le (p : ℕ) (H : Subgroup G) :
    inSubgroup (CFSG.pPrimeCore p) H ≤ H :=
  Subgroup.map_subtype_le _

theorem coprime_card_inSubgroup_pPrimeCore (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    Nat.Coprime p (Nat.card (inSubgroup (CFSG.pPrimeCore p) H)) := by
  rw [inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

omit [Finite G] in
theorem le_inSubgroup_pPrimeCore {p : ℕ} {D H : Subgroup G} (hDH : D ≤ H)
    (hn : H ≤ Subgroup.normalizer (D : Set G)) (hc : Nat.Coprime p (Nat.card D)) :
    D ≤ inSubgroup (CFSG.pPrimeCore p) H := by
  have hnor : (D.subgroupOf H).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hn h.2) x).mp hx
    simpa using this
  have hcop : Nat.Coprime p (Nat.card (D.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
  have hle : D.subgroupOf H ≤ CFSG.pPrimeCore p H := le_sSup ⟨hnor, hcop⟩
  rw [inSubgroup, ← Subgroup.map_subgroupOf_eq_of_le hDH]
  exact Subgroup.map_mono hle

theorem coprime_card_of_isPGroup {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q)
    {D : Subgroup G} (hD : IsPGroup p D) : Nat.Coprime q (Nat.card D) := by
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hp.out).mpr (Ne.symm hpq))

omit [Finite G] in
theorem normalClosureIn_mono {H H' : Subgroup G} (h : H ≤ H') (c : G) :
    normalClosureIn H c ≤ normalClosureIn H' c := by
  rw [normalClosureIn, Subgroup.closure_le]
  rintro _ ⟨m, hm, rfl⟩
  exact Subgroup.subset_closure ⟨m, h hm, rfl⟩

omit [Finite G] in
theorem normalClosureIn_le_self {H : Subgroup G} {c : G} (hc : c ∈ H) : normalClosureIn H c ≤ H :=
  normalClosureIn_le hc

omit [Finite G] in
theorem not_mem_of_isPGroup_two {D : Subgroup G} (hD : IsPGroup 2 D) {c : G}
    (hc : orderOf c = 3) : c ∉ D := by
  intro hcD
  obtain ⟨k, hk⟩ := hD ⟨c, hcD⟩
  have h1 : orderOf c ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk c hcD]
    exact orderOf_dvd_of_pow_eq_one hk
  rw [hc] at h1
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h1)
  omega

theorem le_normalClosureIn_self {K : Subgroup G} (hperf : Group.IsPerfect K)
    (hsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) {c : G} (hcK : c ∈ K) (hc : orderOf c = 3) :
    K ≤ normalClosureIn K c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := normalClosureIn K c with hI
  have hIK : I ≤ K := normalClosureIn_le hcK
  set N : Subgroup K := I.subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn K c k.2) x).mp hx
    simpa using this
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hcN : (⟨c, hcK⟩ : K) ∈ N := by
    rw [hN, Subgroup.mem_subgroupOf]
    exact self_mem_normalClosureIn K c
  have hcO : (⟨c, hcK⟩ : K) ∉ CFSG.pCore 2 K := by
    intro h
    have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := h2 ⟨_, h⟩
    have h1 : orderOf (⟨c, hcK⟩ : K) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk (⟨c, hcK⟩ : K) h]
      exact orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, hc] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)
    omega
  have hNtop : N.map π = ⊤ := by
    have : (N.map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
    · exfalso
      have hmem : π ⟨c, hcK⟩ ∈ N.map π := ⟨_, hcN, rfl⟩
      rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hcO hmem
    · exact h
  have hdecomp : ∀ k : K, ∃ n ∈ N, ∃ o ∈ CFSG.pCore 2 K, k = n * o := by
    intro k
    have hk : π k ∈ N.map π := by rw [hNtop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := hk
    refine ⟨n, hn, n⁻¹ * k, ?_, by group⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
    exact hnk
  have hQ2 : IsPGroup 2 (K ⧸ N) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, o, ho, rfl⟩ := hdecomp k
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨o, ho⟩
    refine ⟨j, ?_⟩
    have hj' : o ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have e : (n * o) ^ 2 ^ j ∈ N := by
      have hmk : (QuotientGroup.mk (n * o) : K ⧸ N) = QuotientGroup.mk o := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← QuotientGroup.mk_pow, hj',
        QuotientGroup.mk_one]
    exact e
  have hQperf : Group.IsPerfect (K ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hQtriv : ∀ q : K ⧸ N, q = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨q, hq⟩ := hne
    have : Nontrivial (K ⧸ N) := ⟨⟨q, 1, hq⟩⟩
    have : Group.IsNilpotent (K ⧸ N) := hQ2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  intro k hk
  have := hQtriv (QuotientGroup.mk ⟨k, hk⟩)
  rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at this
  exact this

section Setting

variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P : Subgroup G}

theorem isSimpleGroup_of_setting204 (hset : Setting204 G A M L N c T i j P) :
    IsSimpleGroup (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c)) := by
  rcases hset.kType with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, hn0, ⟨e⟩⟩
  · have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 n)) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
    exact (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
  · have : IsSimpleGroup ↥(CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) :=
      Sec11.LSSolvableProof.isSimpleGroup_projSL (by obtain ⟨k, hk⟩ := hn; omega)
    exact e.isSimpleGroup

theorem orderOf_c_of_setting204 (hset : Setting204 G A M L N c T i j P) : orderOf c = 3 :=
  Res5.orderOf_eq_three hset.toCtx20 hset.not_le

theorem kTwenty_le_M (hset : Setting204 G A M L N c T i j P) : kTwenty M c ≤ M :=
  kTwenty_le_of_hyp201 hset.toHyp201

theorem kTwenty_le_normalClosureIn (hset : Setting204 G A M L N c T i j P) :
    kTwenty M c ≤ normalClosureIn (kTwenty M c) c :=
  le_normalClosureIn_self (isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn)
    (isSimpleGroup_of_setting204 hset) (self_mem_normalClosureIn M c)
    (orderOf_c_of_setting204 hset)

theorem kTwenty_le_yTwenty (hset : Setting204 G A M L N c T i j P) {X : Subgroup G}
    (hKX : kTwenty M c ≤ X) : kTwenty M c ≤ yTwenty X c :=
  (kTwenty_le_normalClosureIn hset).trans (normalClosureIn_mono hKX c)

theorem yTwenty_le_normalClosureIn_self (hset : Setting204 G A M L N c T i j P)
    (X : Subgroup G) : yTwenty X c ≤ normalClosureIn (yTwenty X c) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := yTwenty X c with hY
  have hc := orderOf_c_of_setting204 hset
  have hcY : c ∈ Y := self_mem_normalClosureIn X c
  have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨Q, hQ, hcQ⟩ := Sec20.exists_isSylowOf_le hc3 (Subgroup.zpowers_le.mpr hcY)
  show Subgroup.closure {x | ∃ m ∈ X, x = m * c * m⁻¹} ≤ normalClosureIn Y c
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := le_normalizer_normalClosureIn X c hx
  have hcxY : x * c * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hxY c).mp hcY
  have hZx : IsPGroup 3 ((Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom) := hc3.map _
  have hZxY : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ≤ Y := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hcxY
  obtain ⟨Q', hQ', hZQ'⟩ := Sec20.exists_isSylowOf_le hZx hZxY
  obtain ⟨y, hyY, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hQ hQ'
  have hle : (Subgroup.zpowers c).map (MulAut.conj (y⁻¹ * x)).toMonoidHom ≤ Q := by
    rw [← Res5.map_conj_map_conj]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨q, hq, hqw⟩ := hZQ' hw
    rw [← hqw]
    simpa [MulAut.conj_apply, mul_assoc] using hq
  have heq := Res5.map_conj_eq_of_le hset.sylow_top hset.conjugatesIn_eq hQ.isPGroup
    (hcQ (Subgroup.mem_zpowers c)) hle
  have hmem : (y⁻¹ * x) * c * (y⁻¹ * x)⁻¹ ∈ Subgroup.zpowers c := by
    rw [← heq]
    exact ⟨c, Subgroup.mem_zpowers c, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hyc : y * c * y⁻¹ ∈ normalClosureIn Y c := Subgroup.subset_closure ⟨y, hyY, rfl⟩
  have e : x * c * x⁻¹ = (y * c * y⁻¹) ^ k := by
    have : (y * c * y⁻¹) ^ k = y * c ^ k * y⁻¹ := by
      rw [show y * c * y⁻¹ = MulAut.conj y c from rfl, ← map_zpow, MulAut.conj_apply]
    rw [this, hk]
    group
  rw [SetLike.mem_coe, e]
  exact zpow_mem hyc k

end Setting

theorem eq_of_le_normalizer {M X K : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (hM : IsMaximalTwoLocal M) (hX : IsMaximalTwoLocal X) (hK : K ∈ oTwoComponentsIn M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    X = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : CFSG.Assembly.IsTwoLocal M := by
    obtain ⟨P, hP, hP2, hMP⟩ := hM.1
    exact ⟨P, hP, hP2, hMP⟩
  have hO : CFSG.Open.pCoreOf 2 K ≠ ⊥ := pCoreOf_ne_bot_of_mem_oTwoComponentsIn hchar hM2 hK
  set Nk := Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) with hNk
  have hloc : IsPLocal 2 Nk := ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K, rfl⟩
  have hKN : Subgroup.normalizer (K : Set G) ≤ Nk :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hMN : M = Nk := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne (hMK.trans hKN) hne) hloc
  have hXN : X = Nk := by
    by_contra hne
    exact hX.2 _ (lt_of_le_of_ne (hXK.trans hKN) hne) hloc
  rw [hXN, hMN]

theorem pCoreOf_ne_bot_of_le_normalizer {M K : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (hM : CFSG.Assembly.IsTwoLocal M) (hKM : K ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hK2 : ¬ IsPGroup 2 K) : CFSG.Open.pCoreOf 2 K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  set O := CFSG.Open.pCoreOf 2 M with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hOM : O ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hD : K ⊓ O ≤ CFSG.Open.pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk) (hMO (hKM hk)))
      (hO2.to_le inf_le_right)
  rw [hbot] at hD
  have hKC : K ≤ M ⊓ Subgroup.centralizer (O : Set G) := by
    intro k hk
    refine ⟨hKM hk, Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩
    have h1 : o * k * o⁻¹ * k⁻¹ ∈ K := by
      have : o * k * o⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hMK (hOM ho)) k).mp hk
      exact K.mul_mem this (K.inv_mem hk)
    have h2 : o * k * o⁻¹ * k⁻¹ ∈ O := by
      have : k * o⁻¹ * k⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hMO (hKM hk)) o⁻¹).mp (O.inv_mem ho)
      have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
      rw [e]
      exact O.mul_mem ho this
    have h3 : o * k * o⁻¹ * k⁻¹ = 1 := by
      have := hD ⟨h1, h2⟩
      simpa using this
    have e : o * k = k * o := by
      have h4 : o * k * o⁻¹ = k := by
        have := congrArg (· * k) h3
        simpa [mul_assoc] using this
      calc o * k = o * k * o⁻¹ * o := by group
        _ = k * o := by rw [h4]
    exact e
  exact hK2 (hO2.to_le ((hKC.trans (hchar M hM)).trans le_rfl))

theorem normalizer_le_of_le_normalizer {M K : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (hM : IsMaximalTwoLocal M) (hKM : K ≤ M) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hK2 : ¬ IsPGroup 2 K) : Subgroup.normalizer (K : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : CFSG.Assembly.IsTwoLocal M := by
    obtain ⟨P, hP, hP2, hMP⟩ := hM.1
    exact ⟨P, hP, hP2, hMP⟩
  have hO := pCoreOf_ne_bot_of_le_normalizer hchar hM2 hKM hMK hK2
  set Nk := Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) with hNk
  have hloc : IsPLocal 2 Nk := ⟨_, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K, rfl⟩
  have hKN : Subgroup.normalizer (K : Set G) ≤ Nk :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hMN : M = Nk := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne (hMK.trans hKN) hne) hloc
  rw [hMN]
  exact hKN

omit [Finite G] in
theorem le_of_isSylowOf_of_le_normalizer {p : ℕ} [Fact p.Prime] {R Y X S : Subgroup G}
    (hR : IsPGroup p R) (hRY : R ≤ Y) (hYX : Y ≤ X) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hS : IsSylowOf p S Y) : R ≤ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hn : (Subgroup.comap Y.subtype R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mpr (hYX.trans hXR)
  have hle : R.subgroupOf Y ≤ Q := (hR.comap_subtype (K := Y)).le_sylow_of_normal Q
  rw [← Subgroup.map_subgroupOf_eq_of_le hRY]
  exact Subgroup.map_mono hle

end Res6

end CFSG.RankThree.PartTwo.Sec20
