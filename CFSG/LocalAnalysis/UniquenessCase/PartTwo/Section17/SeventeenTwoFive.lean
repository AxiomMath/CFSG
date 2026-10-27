module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoFivePStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwoFiveFrattini
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
public import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.GroupTheory.AbelianSqLineCentralize
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_invariant_five {D : Data G} {Dsub X : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (hDsubM : Dsub ≤ D.M)
    (hDexp : ∀ x ∈ Dsub, x ^ 5 = 1) (hDcard : Nat.card ↥Dsub = 25)
    (hnormal : ((Dsub ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hX : CFSG.ABGLocalTools.IsSylowOf q X D.M) :
    ∃ D' : Subgroup G, D' ≤ D.M ∧ IsPGroup 5 ↥D' ∧ ¬ IsCyclic ↥D' ∧
      (∀ x ∈ D', x ^ 5 = 1) ∧ ⁅⁅D', D'⁆, D'⁆ = ⊥ ∧
      ((D' ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal ∧
      Nat.card ↥D' = 25 ∧ D' ⊔ CFSG.Open.pCoreOf 2 D.M = Dsub ⊔ CFSG.Open.pCoreOf 2 D.M ∧
      X ≤ Subgroup.normalizer (D' : Set G) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let K : Subgroup G := Dsub ⊔ CFSG.Open.pCoreOf 2 D.M
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hOM : O ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hOK : O ≤ K := le_sup_right
  have hKle : K ≤ D.M := sup_le hDsubM hOM
  have hKnormal : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).1 hnormal
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := hX.le.trans hKnormal
  have hDsubN : Dsub ≤ Subgroup.normalizer (O : Set G) :=
    hDsubM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  obtain ⟨m, hOcard⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hdisj : Disjoint O Dsub := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hOcard, hDcard]
    exact Nat.Coprime.pow m 2 (by norm_num : Nat.Coprime (2 : ℕ) 5)
  have hKcard : Nat.card K = 2 ^ m * 5 ^ 2 := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      O Dsub hDsubN hdisj
    dsimp [K]
    rw [sup_comm, h, hOcard, hDcard]
  have hcopK : ¬ q ∣ Nat.card K := by
    rw [hKcard]
    intro hdvd
    have hq25 : q ∣ 2 ^ m * 5 ^ 2 := by
      simpa using hdvd
    rcases hq.dvd_mul.mp hq25 with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (hq.dvd_of_dvd_pow h))
    · exact hq5 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp
        (hq.dvd_of_dvd_pow h))
  obtain ⟨S, hXS⟩ := CFSG.GroupTheory.FT63ChII.exists_sylow_normalized
    (p := q) (W := K) (A := X) hX.isPGroup hXK hcopK 5
  let D' : Subgroup G := (S : Subgroup K).map K.subtype
  have hD'K : D' ≤ K := Subgroup.map_subtype_le _
  have hD'M : D' ≤ D.M := hD'K.trans hKle
  have hD'5 : IsPGroup 5 ↥D' := S.isPGroup'.map K.subtype
  have hD'cardS : Nat.card ↥(S : Subgroup K) = 5 ^ (Nat.card K).factorization 5 :=
    S.card_eq_multiplicity
  have hfac : (Nat.card K).factorization 5 = 2 := by
    rw [hKcard]
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      have h52 : (5 : ℕ) ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at h52), Nat.factorization_pow_self Nat.prime_five]
  have hD'card : Nat.card ↥D' = 25 := by
    rw [show Nat.card ↥D' = Nat.card ↥(S : Subgroup K) from
      Subgroup.card_map_of_injective K.subtype_injective, hD'cardS, hfac]
    norm_num
  have hdisj' : Disjoint D' O := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hD'card, hOcard]
    exact Nat.Coprime.pow 2 m (by norm_num : Nat.Coprime (5 : ℕ) 2)
  have hD'normO : D' ≤ Subgroup.normalizer (O : Set G) :=
    hD'M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hsupcard : Nat.card ↥(D' ⊔ O) = Nat.card ↥D' * Nat.card ↥O := by
    simpa [sup_comm, mul_comm] using
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        O D' hD'normO hdisj'.symm
  have hsupK : D' ⊔ O = K := by
    have hle : D' ⊔ O ≤ K := sup_le hD'K hOK
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hsupcard, hKcard, hD'card, hOcard]
    norm_num
    rw [mul_comm]
  have hnormal' : ((D' ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal := by
    rw [hsupK]
    exact hnormal
  have hKmul : (K : Set G) = (Dsub : Set G) * (O : Set G) := by
    simpa [K] using Subgroup.coe_mul_of_left_le_normalizer_right Dsub O hDsubN
  have hD'exp : ∀ x ∈ D', x ^ 5 = 1 := by
    intro d hd
    have hdK : d ∈ (K : Set G) := hD'K hd
    rw [hKmul] at hdK
    rcases Set.mem_mul.mp hdK with ⟨a, ha, o, ho, rfl⟩
    have haK : a ∈ K := (le_sup_left : Dsub ≤ K) ha
    have hoK : o ∈ K := hOK ho
    have hOKnormal : (O.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOK).2
        (hKle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
    let : (O.subgroupOf K).Normal := hOKnormal
    let π : ↥K →* (↥K ⧸ (O.subgroupOf K)) :=
      QuotientGroup.mk' (O.subgroupOf K)
    have hπo : π ⟨o, hoK⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨o, hoK⟩ : ↥K)).mpr (Subgroup.mem_subgroupOf.mpr ho)
    have hdK' : a * o ∈ K := hD'K hd
    have hπd : π ⟨a * o, hdK'⟩ = π ⟨a, haK⟩ := by
      have hsplit : (⟨a * o, hdK'⟩ : ↥K) = ⟨a, haK⟩ * ⟨o, hoK⟩ := Subtype.ext rfl
      rw [hsplit, map_mul, hπo, mul_one]
    have hπpow : π (⟨a * o, hdK'⟩ ^ 5) = 1 := by
      rw [map_pow, hπd]
      have ha5 : (⟨a, haK⟩ : ↥K) ^ 5 = 1 := Subtype.ext (hDexp a ha)
      rw [← map_pow, ha5, map_one]
    have hker : (a * o) ^ 5 ∈ O := by
      have hmem : (⟨a * o, hdK'⟩ : ↥K) ^ 5 ∈ (O.subgroupOf K) :=
        (QuotientGroup.eq_one_iff ((⟨a * o, hdK'⟩ : ↥K) ^ 5)).mp hπpow
      exact Subgroup.mem_subgroupOf.mp hmem
    have hmemD' : (a * o) ^ 5 ∈ D' := D'.pow_mem hd 5
    have hbot : (a * o) ^ 5 ∈ (⊥ : Subgroup G) := by
      have hle : (a * o) ^ 5 ∈ D' ⊓ O := Subgroup.mem_inf.mpr ⟨hmemD', hker⟩
      rwa [hdisj'.eq_bot] at hle
    simpa using (Subgroup.mem_bot.mp hbot)
  have hD'comm : IsMulCommutative ↥D' :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [hD'card]; norm_num)
  have hD'class : ⁅⁅D', D'⁆, D'⁆ = ⊥ := by
    have hcomm : ⁅D', D'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simpa using congrArg Subtype.val (hD'comm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hcomm]
    simp
  have hD'nc : ¬ IsCyclic ↥D' := by
    intro hcyc
    let : IsCyclic ↥D' := hcyc
    rcases (isCyclic_iff_exists_orderOf_eq_natCard (α := ↥D')).mp hcyc with ⟨x, hxord⟩
    have hx5 : x ^ 5 = 1 := Subtype.ext (hD'exp (x : G) x.2)
    have hdvd : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx5
    have hle : Nat.card ↥D' ≤ 5 := by
      rw [← hxord]
      exact Nat.le_of_dvd (by norm_num) hdvd
    rw [hD'card] at hle
    omega
  refine ⟨D', hD'M, hD'5, hD'nc, hD'exp, hD'class, hnormal', hD'card, hsupK, hXS⟩

theorem isStronglyPEmbedded_of_forall_normalizer_le {q : ℕ} [Fact q.Prime] {D : Data G}
    {X : Subgroup G} (hX : CFSG.ABGLocalTools.IsSylowOf q X D.M)
    (hXne : X ≠ ⊥)
    (hN : ∀ Y : Subgroup G, Y ≤ X → Y ≠ ⊥ → Subgroup.normalizer (Y : Set G) ≤ D.M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := by
  have hMtop : D.M ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top D.standing.simple D.standing.nonab
      D.maxLocal.1
  have hNS : Subgroup.normalizer (X : Set G) ≤ D.M := hN X le_rfl hXne
  refine CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le hMtop hX hXne hNS ?_
  intro x hx hxq
  have hxne : Subgroup.zpowers x ≠ ⊥ := by
    rw [Subgroup.zpowers_ne_bot]
    intro h1
    rw [h1, orderOf_one] at hxq
    exact (Fact.out : q.Prime).one_lt.ne hxq
  have hzx : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hx
  have hNzx : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := hN _ hzx hxne
  have hcent : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  exact (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G)).trans hNzx

theorem r72UnitaryFiveOne_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) : R72UnitaryFiveOne D :=
  fun _ h7 _ hPSU => PartOne.Section7.eq_one_of_lieModel_psu D h63 h7 hPSU


theorem seventeen_two_five (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h1 : R17_2_1At D V₀ V) (h2 : R17_2_2At D V₀ V hV)
    (h3 : R17_2_3At D V₀ V hV) (h4 : R17_2_4At D V₀ V)
    (h17_1 : R17_1At D V₀ V hV)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1)
    (h78 : R7_8At5 D) (h76 : R76 D)
    (h72 : F07.R72 D) (h63 : UC6.R6_3 D) :
    R17_2_5At D V₀ V := by
  intro p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hp5le : p ≤ 5 := h4 p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  obtain ⟨hDcardP, -, hk2, -⟩ := h2 p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  have hp3 : p ≠ 3 := by
    intro hp3eq
    have h3sig : 3 ∈ D.sig := hp3eq ▸ hpσ
    have h3sig1 : 3 ∈ D.sig1 := by rw [← h1219]; exact h3sig
    have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := hSg.sig1_sp 3 h3sig1
    exact (Data.k_eq_two_iff D).1 hk2 hsp3
  have hp5 : p = 5 := by
    have h3le : 3 ≤ p := by
      have := hp.two_le
      omega
    interval_cases p
    · exact absurd rfl hp3
    · norm_num at hp
    · rfl
  have hDexp5 : ∀ x ∈ Dsub, x ^ 5 = 1 := by
    intro x hx
    simpa [hp5] using hexp x hx
  have hDcard5 : Nat.card ↥Dsub = 25 := by
    rw [hDcardP, hp5]
    norm_num
  have h5sig : 5 ∈ D.sig := hp5 ▸ hpσ
  have h5sig1 : 5 ∈ D.sig1 := by rw [← h1219]; exact h5sig
  have hM5 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M := hSg.sig1_sp 5 h5sig1
  have h76_5 : Conclusion76 D.M 5 := by
    intro r hr E hEM hEel hEcard hFE hX'
    exact h76 5 (by norm_num) (by norm_num) hM5 r hr E hEM hEel hEcard hFE hX'
  have hstrong_of : ∀ (q : ℕ), q ∈ piSet D.M → q ≠ 2 → q ≠ 5 →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := by
    intro q hq hq2 hq5
    let : Fact q.Prime := ⟨hq.1⟩
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨X, hX⟩ := CFSG.ABGLocalTools.exists_isSylowOf q D.M
    have hXne : X ≠ ⊥ := CFSG.ABGTheoremB.V56.ne_bot_of_isSylowOf hq.1 hX hq.2
    obtain ⟨D', hD'M, hD'5, hD'nc, hD'exp, hD'class, hnormal', hD'card, -, hXND'⟩ :=
      exists_invariant_five (D := D) (Dsub := Dsub) (X := X) hq.1 hq2 hq5 hDM
        hDexp5 hDcard5 hnormal hX
    have hnotIrr : ¬ IrrOn (D.M ⊓ Subgroup.normalizer (D' : Set G)) D' :=
      (h3 5 D' (by norm_num) (by norm_num) hD'M hD'5 hD'nc hD'exp hD'class hnormal').1
    rw [IrrOn] at hnotIrr
    push Not at hnotIrr
    obtain ⟨W, hWD', hNW, hWneBot, hWneD'⟩ := hnotIrr
    have hWcard : Nat.card W = 5 := by
      have hdvd : Nat.card W ∣ 5 ^ 2 := by
        have h := Subgroup.card_dvd_of_le hWD'
        rwa [hD'card] at h
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
      have hk0 : k ≠ 0 := fun hk0 =>
        hWneBot (Subgroup.card_eq_one.mp (by rw [hk, hk0]; norm_num))
      have hk2' : k ≠ 2 := fun hk2eq =>
        hWneD' (Subgroup.eq_of_le_of_card_ge hWD'
          (by rw [hk, hk2eq, hD'card]; norm_num))
      have hk1 : k = 1 := by omega
      rw [hk, hk1]
      norm_num
    have hXW : X ≤ Subgroup.normalizer (W : Set G) :=
      (le_inf hX.le hXND').trans hNW
    have hq4 : ¬ q ∣ 5 - 1 := by
      have h4 : (5 - 1 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4]
      intro hdvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.1 Nat.prime_two).mp
        (hq.1.dvd_of_dvd_pow hdvd))
    have hcent : X ≤ Subgroup.centralizer (D' : Set G) :=
      CFSG.GroupTheory.le_centralizer_of_normalizes_line (p := 5) (q := q)
        (P := D') (U := W) (X := X) (by rw [hD'card]; norm_num) hWD' hWcard hX.isPGroup
        hXND' hXW hq5 hq4
    by_cases hXcyc : IsCyclic ↥X
    ·
      have hN : ∀ Y : Subgroup G, Y ≤ X → Y ≠ ⊥ →
          Subgroup.normalizer (Y : Set G) ≤ D.M := by
        intro Y hYX hYne
        by_contra hH
        have hYq : IsPGroup q ↥Y := hX.isPGroup.to_le hYX
        have hYM : Y ≤ D.M := hYX.trans hX.le
        have hD'Y : D' ≤ Subgroup.centralizer (Y : Set G) :=
          Subgroup.le_centralizer_iff.mp (hYX.trans hcent)
        obtain ⟨S, hSsyl, hScyc⟩ := cyclic_sylow_of_r7_8 (D := D) (V₀ := V₀) (V := V) hV
          h2 h3 h78 hM5 h72 (r72UnitaryFiveOne_of_r6_3 D h63) (D' := D') (Y := Y) (q := q) hq.1
          hD'M hD'5 hD'nc hD'exp hD'class hnormal' hYq hYM hYne hD'Y hH
        exact h17_1.1 D'
          (inPStar_of_cyclic_sylow_frattini (D := D) (V₀ := V₀) (V := V) h1
            (D' := D') (X := X) (Y := Y) (q := q) hq.1 hD'M hD'5 hD'nc hD'exp hD'class
            hnormal' hX hXcyc hcent hYX ⟨S, hSsyl, hScyc⟩)
      exact isStronglyPEmbedded_of_forall_normalizer_le hX hXne hN
    ·
      obtain ⟨E, -, hEel, hEcard⟩ :=
        CFSG.PreuniquenessRankFour.Helpers.odd_pGroup_noncyclic_has_normal_elementary_rank_two
          q hq2 (Nat.card ↥X) rfl hX.isPGroup hXcyc
      let E' : Subgroup G := E.map X.subtype
      have hE'X : E' ≤ X := Subgroup.map_subtype_le _
      have hE'el : IsElemAbelian q E' := hEel.map X.subtype
      have hE'card : Nat.card ↥E' = q ^ 2 := by
        rw [show Nat.card ↥E' = Nat.card ↥E from
          Subgroup.card_map_of_injective X.subtype_injective, hEcard]
      have hXrank : 2 ≤ CFSG.Open.pRank q X :=
        CFSG.SectionRank.le_pRank hq.1.one_lt hE'X hE'el (by rw [hE'card])
      have hD'comm : IsMulCommutative ↥D' :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [hD'card]; norm_num)
      have hD'el : IsElemAbelian 5 D' := ⟨hD'comm, hD'exp⟩
      have hcent' : D' ≤ Subgroup.centralizer (X : Set G) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' := hcent hx
        rw [Subgroup.mem_centralizer_iff] at hx'
        exact (hx' d hd).symm
      have hD'leC : D' ≤ D.M ⊓ Subgroup.centralizer (X : Set G) :=
        le_inf hD'M hcent'
      have hF : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (X : Set G)) :=
        CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) hD'leC hD'el
          (by rw [hD'card]; norm_num)
      have hN := normalizer_le_of_two_le_pRank_inf_centralizer
        (p := 5) (r := q) hM5 h76_5 hX.le hX.isPGroup hXrank hF
      exact isStronglyPEmbedded_of_forall_normalizer_le hX hXne (fun Y hYX hYne => hN Y hYX hYne)
  have h3not : 3 ∉ piSet D.M := by
    intro h3pi
    exact (Data.k_eq_two_iff D).1 hk2 (hstrong_of 3 h3pi (by norm_num) (by norm_num))
  refine ⟨hp5, h3not, ?_⟩
  intro q hq hq2 hq5
  exact hstrong_of q hq hq2 hq5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
