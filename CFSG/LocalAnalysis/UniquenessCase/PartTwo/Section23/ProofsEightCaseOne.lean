module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218N
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.Y2ConjugationInvariance
public import CFSG.RankThree.PartTwo.Sec19.Census194.Arith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private abbrev barInfCenterQuot (K : Subgroup G) : Type :=
  BarInf K ⧸ Subgroup.center (BarInf K)

private theorem exists_b0_caseI {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h215 : S21_5 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) :
    ∃ (b : G) (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G)),
      Odd (orderOf b) ∧ b ∉ Subgroup.centralizer (D.Z : Set G) := by
  classical
  obtain ⟨hm2, hP1⟩ := c.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930
  let m : ℕ := CFSG.Open.pRank 2 D.Z
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by simpa using hm2)
  have hne : 2 ^ m - 1 ≠ 1 := by omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  obtain ⟨b, hb0, hborder, hbZ⟩ := hP1 r hr hrdvd
  have hbodd : Odd (orderOf b) := by
    have hpowodd : Odd (2 ^ m - 1) :=
      CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    have hr2 : r ≠ 2 := by
      intro h
      exact hpowodd.not_two_dvd_nat (h ▸ hrdvd)
    exact hborder ▸ hr.odd_of_ne_two hr2
  exact ⟨b, hb0, c.B0_le_normalizer_of_mem_calC h215 h1930 hK hb0, hbodd, hbZ⟩

private theorem exists_sylow_caseI {D : Data G} {Ch : Choice2011 G}
    (hBor : KBor) (h215 : S21_5 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hshape : ∃ a : ℕ, IsSp4 (barInfCenterQuot K) a ∨ IsU3 (barInfCenterQuot K) a)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G)) :
    ∃ S : Sylow 2 (barInfCenterQuot K),
      (S : Subgroup (barInfCenterQuot K)) =
        ((D.T ⊓ K).subgroupOf K).map (piBarInf K) ∧
      (∀ x ∈ (S : Subgroup (barInfCenterQuot K)),
        inducedQuotInfAut K b hbN x ∈ (S : Subgroup (barInfCenterQuot K))) := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hZ : Subgroup.center (barInfCenterQuot K) = ⊥ := by
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzc : e z ∈ Subgroup.center (BarInf K) := (Subgroup.centerCongr e ⟨z, hz⟩).2
    have h1 : e z = 1 := by simpa [center_barInf_eq_bot hq] using hzc
    exact e.injective (by simpa using h1)
  have hshapeP3 : ∃ a : ℕ, IsL2 (barInfCenterQuot K) a ∨
      IsSz (barInfCenterQuot K) a ∨ IsSp4 (barInfCenterQuot K) a ∨
      IsU3 (barInfCenterQuot K) a := by
    obtain ⟨a, h | h⟩ := hshape
    · exact ⟨a, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨a, Or.inr (Or.inr (Or.inr h))⟩
  have hP3 := Ctx23L.inducedQuotInfAut_mem_sylow (D := D) (Ch := Ch) hBor h215 h1930
    c hK hZ hshapeP3 hb hbN
  let SK : Subgroup (barInfCenterQuot K) := ((D.T ⊓ K).subgroupOf K).map (piBarInf K)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSKp, hSKidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp
    (isSylowOf_map_piBarInf (D := D) (K := K) hK)
  let S : Sylow 2 (barInfCenterQuot K) := hSKp.toSylow (by simpa using hSKidx)
  have hScoe : (S : Subgroup (barInfCenterQuot K)) = SK := IsPGroup.toSylow_coe hSKp _
  have hSinv : ∀ x ∈ (S : Subgroup (barInfCenterQuot K)),
      inducedQuotInfAut K b hbN x ∈ (S : Subgroup (barInfCenterQuot K)) := by
    intro x hx
    rw [hScoe] at hx ⊢
    exact hP3 x hx
  exact ⟨S, hScoe, hSinv⟩

private theorem exists_caseIData {D : Data G} {Ch : Choice2011 G}
    {W : ∀ (X : Type) [Group X], MulAut X → Prop}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch)
    (h2111 : S21_11N D Ch W) (hBor : KBor) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) (hKN : (K.subgroupOf D.M).Normal)
    (hshape : ∃ a : ℕ, IsSp4 (barInfCenterQuot K) a ∨ IsU3 (barInfCenterQuot K) a)
    (hnotL2Sz : ¬ ∃ n : ℕ, IsL2 (BarInf K) n ∨ IsSz (BarInf K) n) :
    ∃ (b : G) (hbN : b ∈ Subgroup.normalizer (K : Set G))
      (S : Sylow 2 (barInfCenterQuot K)),
      b ∈ c.B0 ∧ Odd (orderOf b) ∧ b ∉ Subgroup.centralizer (D.Z : Set G) ∧
      Odd (orderOf (inducedQuotInfAut K b hbN)) ∧
      ¬ W (barInfCenterQuot K) (inducedQuotInfAut K b hbN) ∧
      (S : Subgroup (barInfCenterQuot K)) =
        ((D.T ⊓ K).subgroupOf K).map (piBarInf K) ∧
      (∀ x ∈ (S : Subgroup (barInfCenterQuot K)),
        inducedQuotInfAut K b hbN x ∈ (S : Subgroup (barInfCenterQuot K))) ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p ↥X →
        X ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) → X ∉ uniqueSet D.M) := by
  classical
  obtain ⟨b, hb0, hbN, hbodd, hbZ⟩ :=
    exists_b0_caseI hE h207 h52 h53 h215 h1930 c hK
  have hθodd : Odd (orderOf (inducedQuotInfAut K b hbN)) :=
    Odd.of_dvd_nat hbodd (orderOf_inducedQuotInfAut_dvd K hbN)
  have hnotW : ¬ W (barInfCenterQuot K) (inducedQuotInfAut K b hbN) := by
    intro hWθ
    obtain ⟨n, hn⟩ := h2111 h1930 c.withB0.toCtx23.toCtx21 K hK hKN b
      (by simpa [Ctx23L.withB0_B] using hb0) hbN (inducedQuotInfAut K b hbN)
      (inducedQuotInf_inducedQuotInfAut K b hbN) hWθ
    exact hnotL2Sz ⟨n, hn⟩
  obtain ⟨S, hScoe, hSinv⟩ :=
    exists_sylow_caseI hBor h215 h1930 c hK hshape hb0 hbN
  have hforbid : ∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) → X ∉ uniqueSet D.M := by
    intro p hp X hXne hXp hXle
    have hb' : b ∈ c.withB0.B := by simpa [Ctx23L.withB0_B] using hb0
    exact ((h54 h1930 c.withB0 b hb' hbZ).2 p hp X hXne hXp hXle).1
  exact ⟨b, hbN, S, hb0, hbodd, hbZ, hθodd, hnotW, hScoe, hSinv, hforbid⟩

private theorem sp4_setup {D : Data G}
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (ha : Odd a) (hSp : IsSp4 (Bar2 K) a) :
    IsSp4 (BarInf K) a ∧ IsSp4 (barInfCenterQuot K) a ∧
      (¬ ∃ n : ℕ, IsL2 (BarInf K) n ∨ IsSz (BarInf K) n) ∧
      ¬ IsPowTwo a ∧ LieRankTwoEven (BarInf K) a ∧ 3 ≤ a := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hcSp4 : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSp4 hq hSp
  have hSpInf : IsSp4 (BarInf K) a := lieModel_barInf_of_lieModel_bar2 hq hcSp4 hSp
  have hSpX : IsSp4 (barInfCenterQuot K) a := lieModel_xbar_of_lieModel_bar2 hq hcSp4 hSp
  have hnotL2Sz : ¬ ∃ n : ℕ, IsL2 (BarInf K) n ∨ IsSz (BarInf K) n := by
    rintro ⟨n, h | h⟩
    · exact not_isL2_of_isSp4 hSpInf h
    · exact not_isSz_of_isSp4 hSpInf h
  have ha_ne_one : a ≠ 1 := by
    intro h
    exact hSp.admissible.2.2.2 (by simp [h])
  have hpowa : ¬ IsPowTwo a := uc22p22a_not_isPowTwo_of_odd ha ha_ne_one
  have ha3 : 3 ≤ a := by
    rcases ha with ⟨k, rfl⟩
    omega
  exact ⟨hSpInf, hSpX, hnotL2Sz, hpowa, Or.inr (Or.inl hSpInf), ha3⟩

theorem Ctx23L.false_of_isSp4 {D : Data G} {Ch : Choice2011 G}
    {W : ∀ (X : Type) [Group X], MulAut X → Prop}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch)
    (h218 : S21_8N D Ch) (h2111 : S21_11N D Ch W) (hW : KWSp4 W) (hBor : KBor)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (ha : Odd a) (hSp : IsSp4 (Bar2 K) a) : False := by
  classical
  obtain ⟨hSpInf, hSpX, hnotL2Sz, hpowa, -, ha3⟩ := sp4_setup hK ha hSp
  have h4 : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ a)
  have hne : 2 ^ a - 1 ≠ 1 := by omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
  have hr2 : r ≠ 2 := by
    intro h
    have hodd : Odd (2 ^ a - 1) :=
      CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    exact hodd.not_two_dvd_nat (h ▸ hrdvd)
  have hKN : (K.subgroupOf D.M).Normal :=
    (h218 h1930 c.toCtx21 K hK a hSpInf hpowa r hr hrdvd).1.2.1
  obtain ⟨b, hbN, S, hb, hbodd, hbZ, hθodd, hnotW, hScoe, hSinv, hforbid⟩ :=
    exists_caseIData (W := W) hE h207 h52 h53 h54 h215 h2111 hBor h1930
      c hK hKN ⟨a, Or.inl hSpX⟩ hnotL2Sz
  obtain ⟨X, hXcard, hXK, hXuniq⟩ :=
    (h218 h1930 c.toCtx21 K hK a hSpInf hpowa r hr hrdvd).2.2
  have hXp : IsPGroup r ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  obtain ⟨Pr, hPrfix⟩ := hW (barInfCenterQuot K) a hSpX
    (inducedQuotInfAut K b hbN) hθodd hnotW S hSinv r hr hrdvd
  have hcSp4 : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSp4 hK.2.2 hSp
  obtain ⟨k, hkK, hkcent⟩ := exists_conj_le_centralizer_of_sylow_fixed hK hcSp4
    hbN hbodd hr hr2 Pr hPrfix hXK hXp
  have hKle : K ≤ D.M := CFSG.Open.IsSubnormal.le hK.1
  have hkM : k ∈ D.M := hKle hkK
  have hmapK : X.map (MulAut.conj k).toMonoidHom ≤ K := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact K.mul_mem (K.mul_mem hkK (hXK hx)) (K.inv_mem hkK)
  have hX'ne : X.map (MulAut.conj k).toMonoidHom ≠ ⊥ := by
    intro hbot
    have hXbot : X = ⊥ :=
      Subgroup.map_injective (MulAut.conj k).injective (by simpa using hbot)
    have h1 : Nat.card X = 1 := by rw [hXbot, Subgroup.card_bot]
    rw [hXcard] at h1
    exact hr.ne_one h1
  have hX'p : IsPGroup r ↥(X.map (MulAut.conj k).toMonoidHom) := by
    simpa using IsPGroup.map hXp (MulAut.conj k).toMonoidHom
  have hX'uniq : X.map (MulAut.conj k).toMonoidHom ∈ uniqueSet D.M :=
    (CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.mem_uniqueSet_map_iff
      hkM X).mpr hXuniq
  exact hforbid r hr _ hX'ne hX'p (le_inf (hmapK.trans hKle) hkcent) hX'uniq

private theorem su3_setup {D : Data G} {Ch : Choice2011 G}
    (h219 : S21_9NFull D Ch) (h2117 : S21_17 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSU : IsSU3 (Bar2 K) a) :
    IsU3 (barInfCenterQuot K) a ∧
      (¬ ∃ n : ℕ, IsL2 (BarInf K) n ∨ IsSz (BarInf K) n) ∧
      (a = 2 ∨ 4 ≤ a) ∧ (K.subgroupOf D.M).Normal := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hSU.1
  have hKN : (K.subgroupOf D.M).Normal :=
    uc22p21j_normal_of_s21_17 D Ch h2117 (uc22p21k_spU3NotList j1NotSp4SU3 D) h1930
      c.toCtx21 K hK (Or.inr ⟨a, hSU⟩)
  have ha1 : 1 ≤ a := hSU.2.admissible.2.1
  have ha_ne_one : a ≠ 1 := by
    intro h
    exact hSU.2.admissible.2.2.2 (by simp [h])
  have ha_ne_three : a ≠ 3 := by
    intro h3
    subst h3
    have hpow3 : ¬ IsPowTwo 3 :=
      uc22p22a_not_isPowTwo_of_odd (by decide) (by decide)
    have hmod := (h219 h1930 c.toCtx21 K hK hKN 3 hSU hpow3).1
    norm_num at hmod
  have ha2or4 : a = 2 ∨ 4 ≤ a := by omega
  have hU3x : IsU3 (barInfCenterQuot K) a := isU3_xbar_of_isSU3_bar2 hq hSU
  have hU3barInf : IsU3 (BarInf K) a := by
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hU3x
  have hnotL2Sz : ¬ ∃ n : ℕ, IsL2 (BarInf K) n ∨ IsSz (BarInf K) n := by
    rintro ⟨n, h | h⟩
    · exact not_isL2_of_isU3 hU3barInf h
    · exact not_isSz_of_isU3 hU3barInf h
  exact ⟨hU3x, hnotL2Sz, ha2or4, hKN⟩

theorem Ctx23L.false_of_isSU3 {D : Data G} {Ch : Choice2011 G}
    {W : ∀ (X : Type) [Group X], MulAut X → Prop}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch)
    (h219 : S21_9NFull D Ch) (h2117 : S21_17 D Ch) (h2111 : S21_11N D Ch W)
    (h846 : F08.R846 D) (hW : KWU3 W)
    (hBor : KBor) (hCen : UCK.U3Center) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ} (hSU : IsSU3 (Bar2 K) a) : False := by
  classical
  obtain ⟨hU3x, hnotL2Sz, ha2or4, hKN⟩ := su3_setup h219 h2117 h1930 c hK hSU
  obtain ⟨q, hqprime, hq3, hqdiv⟩ :=
    CFSG.RankThree.PartTwo.Sec19.exists_prime_gt_three_dvd_two_pow_add_one ha2or4
  have hq2 : q ≠ 2 := by omega
  have hqZ : ¬ q ∣ Nat.card (Subgroup.center (Bar2 K)) := by
    intro hqdvd
    have hdvd3 : Nat.card (Subgroup.center (Bar2 K)) ∣ 3 := hCen (Bar2 K) a hSU
    have hq3dvd : q ∣ 3 := hqdvd.trans hdvd3
    have hqeq : q = 3 := (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).mp hq3dvd
    omega
  obtain ⟨b, hbN, S, hb, hbodd, hbZ, hθodd, hnotW, hScoe, hSinv, hforbid⟩ :=
    exists_caseIData (W := W) hE h207 h52 h53 h54 h215 h2111 hBor h1930
      c hK hKN ⟨a, Or.inr hU3x⟩ hnotL2Sz
  obtain ⟨x, hxord, hxfix⟩ := hW (barInfCenterQuot K) a hU3x
    (inducedQuotInfAut K b hbN) hθodd hnotW S hSinv q hqprime hq3 hqdiv
  obtain ⟨y, hycent, hyord, -⟩ := exists_mem_centralizer_of_quotInf_fixed hK
    hbN hbodd hqprime hq2 hqZ hxord hxfix
  let Y : Subgroup G := Subgroup.zpowers (y : G)
  have hYcard : Nat.card Y = q := by
    rw [show Y = Subgroup.zpowers (y : G) from rfl, Nat.card_zpowers, hyord]
  have hKle : K ≤ D.M := CFSG.Open.IsSubnormal.le hK.1
  have hYle : Y ≤ D.M := (Subgroup.zpowers_le.mpr y.2).trans hKle
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hyY : (y : G) ∈ Y := Subgroup.mem_zpowers (y : G)
    rw [hbot] at hyY
    have hy1 : (y : G) = 1 := by simpa using hyY
    rw [hy1, orderOf_one] at hyord
    exact hqprime.ne_one hyord.symm
  have hYp : IsPGroup q ↥Y := IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one])
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
    h846 K hK a hSU q hqprime hq3 hqdiv
  have hYuniq : Y ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded hqprime hstrong hYle hYne hYp
  have hYcent : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.zpowers_le.mpr hycent
  exact hforbid q hqprime Y hYne hYp (le_inf hYle hYcent) hYuniq

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
