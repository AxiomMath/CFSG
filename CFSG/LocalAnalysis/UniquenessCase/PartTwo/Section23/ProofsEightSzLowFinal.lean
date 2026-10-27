module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzLow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzLowRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightSzContext
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLow
import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaMinus)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem szLow_order {m a r : ℕ} (hm : 2 ≤ m) (ha : a = 2 ^ m - 1)
    (hap : a.Prime) (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) :
    Odd a ∧ r ≠ 2 ∧ orderOf (2 : ZMod r) = a ∧ a ∣ r - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have haodd : Odd a := by
    rw [ha]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega)) odd_one
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ a - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow
        (even_two.pow_of_ne_zero haodd.pos.ne') odd_one
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrdvd)
  have h2z : (2 : ZMod r) ≠ 0 := by
    intro h
    have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).1 h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
  have hmod : 2 ^ a ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hrdvd).symm
  have hpow : (2 : ZMod r) ^ a = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff (2 ^ a) 1 r).2 hmod
    simpa using h
  have hdvd_a : orderOf (2 : ZMod r) ∣ a := orderOf_dvd_of_pow_eq_one hpow
  have hne1 : orderOf (2 : ZMod r) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.mp h
    have hmod' : 2 ≡ 1 [MOD r] :=
      (ZMod.natCast_eq_natCast_iff 2 1 r).1 (by simpa using h2)
    exact hr.not_dvd_one
      ((Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod'.symm)
  have horda : orderOf (2 : ZMod r) = a := by
    rcases (Nat.dvd_prime hap).mp hdvd_a with h | h
    · exact absurd h hne1
    · exact h
  have hdvd_r1 : a ∣ r - 1 := by
    have h := ZMod.orderOf_dvd_card_sub_one h2z
    rwa [horda] at h
  exact ⟨haodd, hr2, horda, hdvd_r1⟩

private theorem szLow_m_lt_a {m a : ℕ} (hm : 2 ≤ m) (ha : a = 2 ^ m - 1) : m < a := by
  rw [ha]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hmain : ∀ k : ℕ, k + 2 + 1 < 2 ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have h1 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
        have hk : k + 4 ≤ 2 ^ (k + 2) := by omega
        nlinarith
  have h := hmain k
  omega

private theorem szLow_bounds {m a r : ℕ} (hm : 2 ≤ m) (ha : a = 2 ^ m - 1)
    (hap : a.Prime) (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) :
    Odd a ∧ 3 < r ∧ ¬ r ∣ m := by
  obtain ⟨haodd, hr2, -, hdvd_r1⟩ := szLow_order hm ha hap hr hrdvd
  have h2dvd : 2 ∣ r - 1 := by
    have hodd : Odd r := hr.odd_of_ne_two hr2
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
  have h2a_dvd : 2 * a ∣ r - 1 :=
    haodd.coprime_two_left.mul_dvd_of_dvd_of_dvd h2dvd hdvd_r1
  have ha3 : 3 ≤ a := by
    rw [ha]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hle : 2 * a + 1 ≤ r := by
    have h := Nat.le_of_dvd (Nat.sub_pos_of_lt hr.one_lt) h2a_dvd
    omega
  have hr3 : 3 < r := by omega
  have hm_lt_r : m < r := by
    have := szLow_m_lt_a hm ha
    omega
  refine ⟨haodd, hr3, ?_⟩
  intro h
  have := Nat.le_of_dvd (by omega : 0 < m) h
  omega

private theorem szLow_not_dvd_two_pow {m a r : ℕ} (hm : 2 ≤ m) (ha : a = 2 ^ m - 1)
    (hap : a.Prime) (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) :
    ¬ r ∣ 2 ^ (2 * m) - 1 := by
  obtain ⟨haodd, hr2, horda, -⟩ := szLow_order hm ha hap hr hrdvd
  intro hr2m
  have h2z : (2 : ZMod r) ≠ 0 := by
    intro h
    have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).1 h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
  have hmod : 2 ^ (2 * m) ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hr2m).symm
  have hpow : (2 : ZMod r) ^ (2 * m) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff (2 ^ (2 * m)) 1 r).2 hmod
    simpa using h
  have hdvd_2m : a ∣ 2 * m := by
    have h := orderOf_dvd_of_pow_eq_one hpow
    rwa [horda] at h
  have hdvd_m : a ∣ m := by
    have h' : a ∣ m * 2 := by rwa [mul_comm] at hdvd_2m
    exact (haodd.coprime_two_right.dvd_mul_right).mp h'
  have hm_lt_a := szLow_m_lt_a hm ha
  have := Nat.le_of_dvd (by omega : 0 < m) hdvd_m
  omega

private theorem mem_normalizer_of_calC_sup_zpowers {C L K : Subgroup G} {y : G}
    (hCne : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hyprime : (orderOf y).Prime)
    (hlt : CFSG.Open.evenRank G < orderOf y)
    (hLC : L ≤ Subgroup.normalizer (C : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G)) (hK : K ∈ calC L)
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  let H : Subgroup G := L ⊔ Subgroup.zpowers y
  have hH : H ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hLC (Subgroup.zpowers_le.mpr hyC)
  have hnorm : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hyL))
  have hLsn : CFSG.Open.IsSubnormal L H :=
    CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl H)
  exact mem_normalizer_of_evenRank_lt hCne hC2 hH
    ⟨hK.1.trans hLsn, hK.2.1, hK.2.2⟩
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyprime hlt

private theorem nParamSingle_to_shape {X : Type} [Group X] {m : ℕ} (hX : NParamSingle X m) :
    IsSz X m ∨ IsL2 X m ∨ IsSU3 X m ∨ IsSL3 X m ∨ IsSp4 X m ∨ IsOmegaMinus X 4 m := by
  rcases hX with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem commutator_mem_pCoreOf_of_nParamSingle (hKO : KOrdBorel) {L S : Subgroup G}
    {m r : ℕ} (hm : 2 ≤ m) (hr : r.Prime) (hr3 : 3 < r)
    (hrm : ¬ r ∣ m) (hr2m : ¬ r ∣ 2 ^ (2 * m) - 1)
    (hX : NParamSingle (Bar2 L) m) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) {y : G}
    (hyr : y ^ r = 1) (hyS : y ∈ Subgroup.normalizer (S : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ L, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
  commutator_mem_pCoreOf_of_kOrdBorel hKO hm (nParamSingle_to_shape hX) hr hr3 hrm hr2m
    hS hyr hyS hyL

private theorem commutator_mem_pCoreOf_of_nParamTwo (hKO : KOrdBorel)
    {T L La Lb : Subgroup G} {y : G} {m r : ℕ}
    (hm : 2 ≤ m) (hr : r.Prime) (hr3 : 3 < r)
    (hrm : ¬ r ∣ m) (hr2m : ¬ r ∣ 2 ^ (2 * m) - 1)
    (hLa : La ∈ calC L) (hLb : Lb ∈ calC L) (hLsup : L = La ⊔ Lb)
    (hshape : ∀ L' ∈ ({La, Lb} : Set (Subgroup G)),
      IsSz (Bar2 L') m ∨ IsL2 (Bar2 L') m ∨ (m = 3 ∧ IsSU3 (Bar2 L') 3))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L)
    (hyr : y ^ r = 1) (hyT : y ∈ Subgroup.normalizer (T : Set G))
    (hyLa : y ∈ Subgroup.normalizer (La : Set G))
    (hyLb : y ∈ Subgroup.normalizer (Lb : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ L, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have hSa : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ La) La :=
    isSylowOf_inf_of_mem_calC hS hLa
  have hSb : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Lb) Lb :=
    isSylowOf_inf_of_mem_calC hS hLb
  have hySa : y ∈ Subgroup.normalizer ((T ⊓ La : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hyT, hyLa⟩)
  have hySb : y ∈ Subgroup.normalizer ((T ⊓ Lb : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hyT, hyLb⟩)
  have hXa : IsSz (Bar2 La) m ∨ IsL2 (Bar2 La) m ∨ IsSU3 (Bar2 La) m ∨
      IsSL3 (Bar2 La) m ∨ IsSp4 (Bar2 La) m ∨ IsOmegaMinus (Bar2 La) 4 m :=
    nParamSingle_to_shape (uc22ine229_nParamSingle_of_prod (hshape La (by simp)))
  have hXb : IsSz (Bar2 Lb) m ∨ IsL2 (Bar2 Lb) m ∨ IsSU3 (Bar2 Lb) m ∨
      IsSL3 (Bar2 Lb) m ∨ IsSp4 (Bar2 Lb) m ∨ IsOmegaMinus (Bar2 Lb) 4 m :=
    nParamSingle_to_shape (uc22ine229_nParamSingle_of_prod (hshape Lb (by simp)))
  exact commutator_mem_pCoreOf_sup hLa hLb hLsup hyL
    (commutator_mem_pCoreOf_of_kOrdBorel hKO hm hXa hr hr3 hrm hr2m hSa hyr hySa hyLa)
    (commutator_mem_pCoreOf_of_kOrdBorel hKO hm hXb hr hr3 hrm hr2m hSb hyr hySb hyLb)

private theorem exists_calLLow_member (D : Data G) (h1930 : H1930 D) (hR : UC6.R6_40_2 D)
    (h20_4 : S20_4 D) (h20_9 : S20_9 D) :
    ∃ (C L₁ L' P : Subgroup G), C ≠ ⊥ ∧ IsPGroup 2 C ∧
      Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      L₁ ≤ Subgroup.normalizer (C : Set G) ∧ L₁ ∈ calLLow D.T D.M ∧
      L' ∈ calLOf D.T D.M (Subgroup.normalizer (C : Set G)) ∧
      MinTInvParabolic D.T D.M L' P ∧ L₁ = Hinf P := by
  obtain ⟨C, hCne, hCT, hNC, L', hL', L₁, hL₁, hL₁le, P, hP, hL₁eq⟩ :=
    exists_calLLow_le_calLOf_normalizer D h1930 hR h20_4 h20_9
  exact ⟨C, L₁, L', P, hCne, D.sylowM.isPGroup.to_le hCT, hNC,
    hL₁le.trans hL'.2.le, hL₁, hL', hP, hL₁eq⟩

private theorem exists_y_of_order {D : Data G} {A C : Subgroup G} {r : ℕ}
    (hAcard : Nat.card A = r) (hr : r.Prime) (hr3 : 3 < r)
    (hAT : A ≤ Subgroup.normalizer (D.T : Set G))
    (hNC : Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (C : Set G))
    (he4 : CFSG.Open.evenRank G ≤ 4) :
    ∃ y : G, y ∈ A ∧ A = Subgroup.zpowers y ∧ orderOf y = r ∧
      y ∈ Subgroup.normalizer (D.T : Set G) ∧
      y ∈ Subgroup.normalizer (C : Set G) ∧ (orderOf y).Prime ∧
      Odd (orderOf y) ∧ CFSG.Open.evenRank G < orderOf y := by
  classical
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  obtain ⟨y, hyA, hyne⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hAne
  have hyord : orderOf y = r := by
    have hdvd : orderOf y ∣ r := by
      simpa [hAcard] using Subgroup.orderOf_dvd_natCard A hyA
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hyne
    · exact h
  have hyprime : (orderOf y).Prime := by rw [hyord]; exact hr
  have hyodd : Odd (orderOf y) := by
    rw [hyord]
    exact hr.odd_of_ne_two (by omega)
  have hyT : y ∈ Subgroup.normalizer (D.T : Set G) := hAT hyA
  have hyC : y ∈ Subgroup.normalizer (C : Set G) := hNC hyT
  have hpos : CFSG.Open.evenRank G < orderOf y := by
    rw [hyord]
    have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three (by omega) (by omega)
    omega
  have hzA : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.mpr hyA
  have hcardz : Nat.card (Subgroup.zpowers y) = r := by
    rw [Nat.card_zpowers, hyord]
  have hz : Subgroup.zpowers y = A :=
    Subgroup.eq_of_le_of_card_ge hzA (by rw [hAcard, hcardz])
  exact ⟨y, hyA, hz.symm, hyord, hyT, hyC, hyprime, hyodd, hpos⟩

private theorem exists_context_of_y (D : Data G) (Ch : Choice2011 G) (hKD : KDiag)
    (h20_7 : S20_7 D) (h20_8 : S20_8 D) (h20_10 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (h1930 : H1930 D) (c : Ctx23L D Ch)
    {C L₁ L' P : Subgroup G} (hCne : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hNC : Subgroup.normalizer (D.T : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hL₁ : L₁ ∈ calLLow D.T D.M) (hL' : L' ∈ calLOf D.T D.M (Subgroup.normalizer (C : Set G)))
    (hP : MinTInvParabolic D.T D.M L' P) (hL₁eq : L₁ = Hinf P)
    {y : G} (hyprime : (orderOf y).Prime) (hyodd : Odd (orderOf y))
    (hpos : CFSG.Open.evenRank G < orderOf y)
    (hyT : y ∈ Subgroup.normalizer (D.T : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G)) :
    ∃ c₁ : Ctx23L D Ch, c₁.L0 = L₁ ∧ y ∈ Subgroup.normalizer (L₁ : Set G) := by
  classical
  have hyAll : ∀ K' ∈ calC (Subgroup.normalizer (C : Set G)),
      y ∈ Subgroup.normalizer (K' : Set G) :=
    fun K' hK' => mem_normalizer_of_evenRank_lt hCne hC2 le_rfl hK' hyC hyprime hpos
  have hTNC : D.T ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer.trans hNC
  have hyL' : y ∈ Subgroup.normalizer (L' : Set G) :=
    mem_normalizer_of_mem_calLOf hL' hTNC hyAll
  have hyL₁ : y ∈ Subgroup.normalizer (L₁ : Set G) := by
    rw [hL₁eq]
    exact mem_normalizer_hinf_of_kDiag hKD D h1930 h20_7 hL'.1 hP hyodd hyT hyL'
  obtain ⟨c₁, hc₁L0, -⟩ :=
    exists_ctx23L_of_mem_calLLow D Ch h1930 h20_8 h20_10 hCh c.hTI hL₁
  exact ⟨c₁, hc₁L0, hyL₁⟩

private theorem commutator_mem_pCoreOf_of_szLowContext (hKO : KOrdBorel) (D : Data G)
    (Ch : Choice2011 G) (h2352 : S23_5_2 D Ch) (h1930 : H1930 D) (c₁ : Ctx23L D Ch)
    {C L₁ : Subgroup G} {y : G} {m r : ℕ} (hm : m = CFSG.Open.pRank 2 D.Z)
    (hm2 : 2 ≤ m) (hr : r.Prime) (hr3 : 3 < r)
    (hrm : ¬ r ∣ m) (hr2m : ¬ r ∣ 2 ^ (2 * m) - 1)
    (hL₁ : L₁ ∈ calLLow D.T D.M) (hc₁L0 : c₁.L0 = L₁)
    (hyord : orderOf y = r) (hyT : y ∈ Subgroup.normalizer (D.T : Set G))
    (hyL₁ : y ∈ Subgroup.normalizer (L₁ : Set G))
    (hCne : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hyprime : (orderOf y).Prime)
    (hpos : CFSG.Open.evenRank G < orderOf y)
    (hLC : L₁ ≤ Subgroup.normalizer (C : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G)) :
    ∀ b ∈ L₁, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L₁ := by
  have hS₁ : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L₁) L₁ :=
    uc22p20i_isSylowOf_inf D hL₁.prop
  have hyS : y ∈ Subgroup.normalizer ((D.T ⊓ L₁ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hyT, hyL₁⟩)
  have hyr : y ^ r = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  rcases h2352 h1930 c₁ with hnm | ⟨hLc, hOm, -⟩
  · have hnm' : c₁.n = m := hnm.trans hm.symm
    have hnp : NParam L₁ m := by simpa [hc₁L0, hnm'] using c₁.hn
    rcases hnp with hsingle | ⟨La, Lb, hLa, hLb, hLsup, -, hshape⟩
    · exact commutator_mem_pCoreOf_of_nParamSingle hKO hm2 hr hr3 hrm hr2m hsingle
        hS₁ hyr hyS hyL₁
    · have hyLa : y ∈ Subgroup.normalizer (La : Set G) :=
        mem_normalizer_of_calC_sup_zpowers hCne hC2 hyprime hpos hLC hyC hLa hyL₁
      have hyLb : y ∈ Subgroup.normalizer (Lb : Set G) :=
        mem_normalizer_of_calC_sup_zpowers hCne hC2 hyprime hpos hLC hyC hLb hyL₁
      exact commutator_mem_pCoreOf_of_nParamTwo hKO hm2 hr hr3 hrm hr2m hLa hLb hLsup
        hshape hS₁ hyr hyT hyLa hyLb hyL₁
  · have hLc' : c₁.L = L₁ := hLc.trans hc₁L0
    have hOm' : IsOmegaMinus (Bar2 L₁) 4 m := by
      rw [← hLc', hm]
      exact hOm
    exact commutator_mem_pCoreOf_of_kOrdBorel hKO hm2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hOm')))))
      hr hr3 hrm hr2m hS₁ hyr hyS hyL₁

theorem s23_8_SzLow_of (D : Data G) (Ch : Choice2011 G) (hKD : KDiag) (hKO : KOrdBorel)
    (hR : UC6.R6_40_2 D) (h20_4 : S20_4 D) (h20_7 : S20_7 D) (h20_8 : S20_8 D) (h20_9 : S20_9 D)
    (h20_10 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (h2352 : S23_5_2 D Ch) (he4 : CFSG.Open.evenRank G ≤ 4) :
    S23_8_SzLow D Ch := by
  intro h1930 c K hK a hSz hne ha_eq ha_prime r hr hrdvd A hAcard hAM hAT hAK
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m : ℕ := CFSG.Open.pRank 2 D.Z with hm
  have ha : a = 2 ^ m - 1 := by rw [hm]; exact ha_eq
  have hm2 : 2 ≤ m := by
    have ha2 : 2 ≤ a := ha_prime.two_le
    by_contra h
    have hmle : m ≤ 1 := by omega
    have hpow : 2 ^ m ≤ 2 := by
      calc 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hmle
        _ = 2 := by norm_num
    omega
  obtain ⟨haodd, hr3, hrm⟩ := szLow_bounds hm2 ha ha_prime hr hrdvd
  have hr2m := szLow_not_dvd_two_pow hm2 ha ha_prime hr hrdvd
  obtain ⟨C, L₁, L', P, hCne, hC2, hNC, hLC, hL₁, hL', hP, hL₁eq⟩ :=
    exists_calLLow_member D h1930 hR h20_4 h20_9
  obtain ⟨y, -, hz, hyord, hyT, hyC, hyprime, hyodd, hpos⟩ :=
    exists_y_of_order hAcard hr hr3 hAT hNC he4
  obtain ⟨c₁, hc₁L0, hyL₁⟩ :=
    exists_context_of_y D Ch hKD h20_7 h20_8 h20_10 hCh h1930 c hCne hC2 hNC hL₁ hL' hP
      hL₁eq hyprime hyodd hpos hyT hyC
  have hcomm := commutator_mem_pCoreOf_of_szLowContext hKO D Ch h2352 h1930 c₁ hm hm2
    hr hr3 hrm hr2m hL₁ hc₁L0 hyord hyT hyL₁ hCne hC2 hyprime hpos hLC hyC
  rw [hz]
  refine ⟨L₁, hL₁, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr hyL₁
  · intro x hx b hb
    exact commutator_mem_pCoreOf_zpowers hyL₁ hcomm x hx b hb

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
