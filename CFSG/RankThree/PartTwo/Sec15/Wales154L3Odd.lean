module

public import CFSG.RankThree.PartTwo.Sec15.Wales154ONBranch
public import CFSG.RankThree.PartTwo.Sec15.Wales154KON
public import CFSG.RankThree.PartTwo.Sec15.Wales154KONAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.Main
public import CFSG.RankThree.PartTwo.Sec15.Wales154L3
import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofRead
public import CFSG.RankThree.PartTwo.Sec15.Wales154KU35
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Ronan148KPoint
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec15.Wales154Five

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_isLThreeEpsAt {Q : Type} [Group Q] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : IsLThreeEpsAt Q p f) :
    Nat.card Q * Nat.gcd 3 (p ^ f - 1) = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ∨
      (2 < p ^ f ∧ Nat.card Q * Nat.gcd 3 (p ^ f + 1) =
        (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · left
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
    rw [GaloisField.card p f (by omega)] at hc
    rw [Nat.card_congr φ.toEquiv]
    exact hc
  · right
    refine ⟨hq, ?_⟩
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_projSU_three_mul_gcd p f hf

theorem pow_three_dvd_card_of_isLThreeEpsAt {Q : Type} [Group Q] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (h : IsLThreeEpsAt Q p f) : (p ^ f) ^ 3 ∣ Nat.card Q := by
  have hp : p.Prime := Fact.out
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rcases card_eq_of_isLThreeEpsAt hf h with hc | ⟨-, hc⟩
  · have hcop : Nat.Coprime ((p ^ f) ^ 3) (Nat.gcd 3 (p ^ f - 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      have h1 : Nat.Coprime (p ^ f - 1) (p ^ f - 1 + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.sub_add_cancel hq1] at h1
      exact h1.symm
    exact hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)
  · have hcop : Nat.Coprime ((p ^ f) ^ 3) (Nat.gcd 3 (p ^ f + 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)

theorem gcd_three_eq (n : ℕ) : Nat.gcd 3 n = if n % 3 = 0 then 3 else 1 := by
  split_ifs with h
  · exact Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hd =>
      h (Nat.mod_eq_zero_of_dvd hd)

theorem order_key {M t a b P Q x y : ℕ} (hPQ : 0 < P * Q) (h1 : M * a = P * (Q * x))
    (h2 : M * t * b = P * (Q * y)) : x * t * b = y * a := by
  refine Nat.eq_of_mul_eq_mul_left hPQ ?_
  calc P * Q * (x * t * b) = P * (Q * x) * (t * b) := by ring
    _ = M * a * (t * b) := by rw [h1]
    _ = M * t * b * a := by ring
    _ = P * (Q * y) * a := by rw [h2]
    _ = P * Q * (y * a) := by ring

theorem false_of_isLThreeEpsAt_one_dvd {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁]
    {r : ℕ} [Fact r.Prime] (hr : 5 ≤ r) (h₁ : IsLThreeEpsAt Q₁ r 1) (h₂ : IsLThreeEpsAt Q₂ r 1)
    (hd : Nat.card Q₁ ∣ Nat.card Q₂) (hle : 2 * Nat.card Q₁ ≤ Nat.card Q₂) : False := by
  have hp : r.Prime := Fact.out
  have hr3 : r % 3 = 1 ∨ r % 3 = 2 := by
    have h0 : r % 3 ≠ 0 := fun h0 => by
      have h3 : 3 ∣ r := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.dvd_prime hp).mp h3 with h | h <;> omega
    omega
  obtain ⟨t, ht⟩ := hd
  have hpos : 0 < Nat.card Q₁ := Nat.card_pos
  have ht2 : 2 ≤ t := by
    by_contra h
    push Not at h
    interval_cases t <;> nlinarith
  have hPQ : 0 < r ^ 3 * (r ^ 2 - 1) := by
    have : 1 ≤ r ^ 2 - 1 := by
      have : 25 ≤ r ^ 2 := by nlinarith
      omega
    positivity
  have hS : 125 ≤ r ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have hgL : Nat.gcd 3 (r - 1) = if r % 3 = 1 then 3 else 1 := by
    rw [gcd_three_eq]
    congr 1
    apply propext
    omega
  have hgU : Nat.gcd 3 (r + 1) = if r % 3 = 2 then 3 else 1 := by
    rw [gcd_three_eq]
    congr 1
    apply propext
    omega
  have hfin : ∀ x y a b : ℕ, x * t * b = y * a → (x = r ^ 3 - 1 ∨ x = r ^ 3 + 1) →
      (y = r ^ 3 - 1 ∨ y = r ^ 3 + 1) → (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) →
      (x = y → a = b) → False := by
    intro x y a b hk hx hy ha hb hxy
    generalize hu : r ^ 3 = u at hS hx hy
    rcases (show t ≤ 3 ∨ 4 ≤ t by omega) with h4 | h4
    · interval_cases t <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hxy <;> omega
    · have hm := Nat.mul_le_mul_right b (Nat.mul_le_mul_left x h4)
      generalize hw : x * t * b = w at hk hm
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hxy <;> omega
  have hg1 : ∀ n : ℕ, ((if n = 1 then 3 else 1) = 1 ∨ (if n = 1 then 3 else 1) = 3) := by
    intro n
    split_ifs <;> simp
  have hg2 : ∀ n : ℕ, ((if n = 2 then 3 else 1) = 1 ∨ (if n = 2 then 3 else 1) = 3) := by
    intro n
    split_ifs <;> simp
  have hne : r ^ 3 - 1 ≠ r ^ 3 + 1 := by omega
  rcases card_eq_of_isLThreeEpsAt le_rfl h₁ with c₁ | ⟨-, c₁⟩ <;>
    rcases card_eq_of_isLThreeEpsAt le_rfl h₂ with c₂ | ⟨-, c₂⟩
  · rw [pow_one] at c₁ c₂
    rw [ht] at c₂
    have hk := order_key hPQ c₁ c₂
    rw [hgL] at hk
    exact hfin _ _ _ _ hk (Or.inl rfl) (Or.inl rfl) (hg1 _) (hg1 _) fun _ => rfl
  · rw [pow_one] at c₁ c₂
    rw [ht] at c₂
    have hk := order_key hPQ c₁ c₂
    rw [hgL, hgU] at hk
    exact hfin _ _ _ _ hk (Or.inl rfl) (Or.inr rfl) (hg1 _) (hg2 _) fun h => (hne h).elim
  · rw [pow_one] at c₁ c₂
    rw [ht] at c₂
    have hk := order_key hPQ c₁ c₂
    rw [hgL, hgU] at hk
    exact hfin _ _ _ _ hk (Or.inr rfl) (Or.inl rfl) (hg2 _) (hg1 _) fun h => (hne h.symm).elim
  · rw [pow_one] at c₁ c₂
    rw [ht] at c₂
    have hk := order_key hPQ c₁ c₂
    rw [hgU] at hk
    exact hfin _ _ _ _ hk (Or.inr rfl) (Or.inr rfl) (hg2 _) (hg2 _) fun _ => rfl

theorem le_one_of_isLThreeEpsAt_dvd {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] {r k : ℕ}
    [Fact r.Prime] (hk : 1 ≤ k) (h₁ : IsLThreeEpsAt Q₁ r k) (h₂ : IsLThreeEpsAt Q₂ r 1)
    (hd : Nat.card Q₁ ∣ Nat.card Q₂) : k ≤ 1 := by
  have hp : r.Prime := Fact.out
  have h1 := (pow_three_dvd_card_of_isLThreeEpsAt hk h₁).trans hd
  have hr1 : 1 ≤ r := hp.pos
  have hcopr : ∀ m : ℕ, 1 ≤ m → Nat.Coprime r (r ^ m - 1) := fun m hm => by
    have h1 : Nat.Coprime (r ^ m - 1) (r ^ m - 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)] at h1
    exact (h1.coprime_dvd_right (dvd_pow_self r (by omega))).symm
  have hcopr' : Nat.Coprime r (r ^ 3 + 1) :=
    ((Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).coprime_dvd_left
      (dvd_pow_self r (by norm_num)))
  obtain ⟨M, hM, hcop⟩ : ∃ M, Nat.card Q₂ ∣ r ^ 3 * M ∧ Nat.Coprime r M := by
    rcases card_eq_of_isLThreeEpsAt le_rfl h₂ with c | ⟨-, c⟩ <;> rw [pow_one] at c
    · exact ⟨(r ^ 2 - 1) * (r ^ 3 - 1), c ▸ Dvd.intro _ rfl,
        Nat.Coprime.mul_right (hcopr 2 (by norm_num)) (hcopr 3 (by norm_num))⟩
    · exact ⟨(r ^ 2 - 1) * (r ^ 3 + 1), c ▸ Dvd.intro _ rfl,
        Nat.Coprime.mul_right (hcopr 2 (by norm_num)) hcopr'⟩
  have h2 : (r ^ k) ^ 3 ∣ r ^ 3 := by
    have := h1.trans hM
    rw [← pow_mul] at this ⊢
    exact (Nat.Coprime.pow_left (k * 3) hcop).dvd_of_dvd_mul_right this
  rw [← pow_mul] at h2
  have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
  omega

theorem false_of_isLThreeEpsAt_dvd {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] [Finite Q₁] {r k : ℕ}
    [Fact r.Prime] (hr : 5 ≤ r) (hk : 1 ≤ k) (h₁ : IsLThreeEpsAt Q₁ r k)
    (h₂ : IsLThreeEpsAt Q₂ r 1) (hd : Nat.card Q₁ ∣ Nat.card Q₂)
    (hle : 2 * Nat.card Q₁ ≤ Nat.card Q₂) : False := by
  have hk1 : k = 1 := le_antisymm (le_one_of_isLThreeEpsAt_dvd hk h₁ h₂ hd) hk
  subst hk1
  exact false_of_isLThreeEpsAt_one_dvd hr h₁ h₂ hd hle

theorem eq_one_of_isLThreeEpsAt_two_local {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    {Y : Subgroup G} (hY2 : Y ∈ scriptY2 A) {r f : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hr3 : 3 < r) (hf : 1 ≤ f) (hε : IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) r f) : f = 1 := by
  have hrp : r.Prime := Fact.out
  have hlt := h.toTheoremFourHyp.localRank_lt r hrp hr3
  have hQ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  obtain ⟨hQeven, hQcop⟩ := Proof1518R2.two_dvd_and_coprime_of_isPGroup_two hQ2 hY2.2 hrp hr2
  by_contra hf1
  obtain ⟨Eb, hEb, hEbcard⟩ := ks1518PRank _ r f hr2 (by omega) hε
  have hN : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥Y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y))
    rw [hk]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp (hrp.dvd_of_dvd_pow hd))
  obtain ⟨S, -, hS, hScard⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift (CFSG.pCore 2 ↥Y) hN hEb
  have hSD : S.map Y.subtype ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    (Subgroup.map_subtype_le S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hS' : CFSG.Assembly.IsElemAbelian r (S.map Y.subtype) :=
    let h' := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map r Y.subtype S
      ⟨hS.1, hS.2⟩
    ⟨h'.1, h'.2⟩
  have hS'card : Nat.card ↥(S.map Y.subtype) = r ^ 3 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hScard, hEbcard]
  have hk := CFSG.RankThree.Classical2.le_localRank_of_normalizes hrp hSD hS' hS'card hQcop
    hQeven
  omega

section Odd


theorem item154L3Point_odd (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKU : KS154U35A7) : Item154L3Point (· ≠ 2) := by
  intro G _ _ A c L hR hNHJ Y hY X hX hXY hYX c' L' r e f hr hr2 he hf _ hc' htrivY hL' hπ
    hεY3 R hRm
  left
  have hrp : r.Prime := Fact.out
  have hr3 : r ≠ 3 := Sec14.Ronan148K.ne_three_of_isoLThreePi he hπ
  have hr5 : 5 ≤ r := by
    rcases (show r ≤ 4 ∨ 5 ≤ r by omega) with h | h
    · interval_cases r
      · exact absurd hrp (by norm_num)
      · exact absurd hrp (by norm_num)
      · exact absurd rfl hr2
      · exact absurd rfl hr3
      · exact absurd hrp (by norm_num)
    · exact h
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY.1
  have heqY : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun W _ hWc hcop ⟨φ⟩ =>
      Proof1511Steps.eq_bot_of_isLThreeEpsAt _ W hperf hWc hcop hf
        (IsLThreeEpsAt.of_mulEquiv φ.symm hεY3)
  have hεY : IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) r f :=
    IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heqY) hεY3
  have hf1 := eq_one_of_isLThreeEpsAt_two_local hR hY.2 hr2 (by omega) hf hεY
  subst hf1
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  have hq3 := card_quot_pPrimeCore_dvd (Z := ↥X)
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
  have hc'1 : c' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc'3
    omega
  have htrivX := trivial_of_le hXY (hX.1.2 hc'A) htrivY
  have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 hR.toSec14Std hNHJ hB
  have hstd' : Sec14Std G A c' L' :=
    { hR.toSec14Std with zpowers_mem_omegaA := hc', mem_lA := hL' }
  have h3L' : 3 ∣ Nat.card L' := Sec16.Proof1613.three_dvd_card_L hstd'
  have hneX := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hX
  have : Group.IsPerfect ↥X := isPerfect_of_mem_scriptY4 hX
  have : Group.IsPerfect (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := QuotientGroup.nontrivial_iff.mpr hneX
  have harith : ∀ k : ℕ, 1 ≤ k → IsLThreeEpsAt (↥X ⧸ CFSG.pPrimeCore 3 ↥X) r k → False :=
    fun k hk hεX => false_of_isLThreeEpsAt_dvd hr5 hk hεX hεY (hq3.trans hdvd)
      (le_trans (Nat.mul_le_mul_left 2 (Nat.le_of_dvd Nat.card_pos hq3)) hle)
  rcases read154_nhj5 h148 h134 h48 hR hNHJ hX with
    ⟨c'', hc'', htriv'', L'', hL'', h2⟩ | ⟨ψ⟩ | ⟨-, -, -, -, -, -, -, -, -, -, hL4, -⟩
  ·
    obtain ⟨hc''A, hc''3, -⟩ := zpowers_mem_omegaA_iff.mp hc''
    have hc''1 : c'' ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc''3
      omega
    have hmem := mem_zpowers_of_trivial hR.toSec14Std hLB hX hc''A hc''1 hc'A htriv'' htrivX
    have hzz : Subgroup.zpowers c'' = Subgroup.zpowers c' := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_).symm
      rw [hc''3, hc'3]
    have hLc'' : L' ∈ thetaComponentsAt 3 c'' :=
      (Proof1515.thetaComponentsAt_eq_of_zpowers_eq hzz.symm) ▸ hL'.1
    have hL : L' = L'' := (hR.chosen136.2 c'' hc'' L'' hL'').2 L' hLc'' h3L'
    subst hL
    rcases h2 with ⟨⟨ψ⟩⟩ | ⟨hL3, ⟨ψ⟩⟩ | ⟨p, f', e', hp, hf', he', hiso', hε'⟩
    · exact (harith e he
        (Sec14.isLThreeEpsAt_of_isoLThreePi148 (Proof1515.isoLThreePi_congr ψ.symm hπ))).elim
    · have h7 : 7 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
        have : 7 ∣ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := by
          rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_seven]
          norm_num
        exact this.trans hq3
      have hr5' : r = 5 := by
        rcases hL3 with ⟨⟨φM⟩⟩ | ⟨_, ⟨φL⟩⟩ | ⟨_, ⟨φU⟩⟩
        · exact (KFacts.KS14.not_isoLThreePi_M22 r e (Proof1515.isoLThreePi_congr φM hπ)).elim
        · exact (Sec14.Ronan148A.isoLThreePi_unique he (by norm_num) hπ
            (Or.inl ⟨by norm_num, ⟨φL⟩⟩)).1
        · exact (Sec14.Ronan148A.isoLThreePi_unique he (by norm_num) hπ
            (Or.inr ⟨by norm_num, ⟨φU⟩⟩)).1
      subst hr5'
      rcases hεY with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exfalso
        have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 5 1)
        rw [GaloisField.card 5 1 (by norm_num), ← Nat.card_congr φ.toEquiv] at hc
        norm_num at hc
        have h1 := h7.trans hdvd
        rw [hc] at h1
        norm_num at h1
      · exact commutator_le_of_U35 hKU ⟨φ⟩ hXY h7 hRm.1 hR2 hXR
    · obtain ⟨rfl, -⟩ := Sec14.Ronan148A.isoLThreePi_unique he (Nat.mul_pos hf' he') hπ hiso'
      exact (harith f' hf' hε').elim
  ·
    exfalso
    obtain ⟨ψ⟩ := ψ
    obtain ⟨φ10⟩ := Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hX ⟨ψ⟩
      Proof1515.multFree_alternatingGroup_ten
    have hZX : Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
      CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating (by norm_num) φ10
    have heqX := pPrimeCore_eq_pCore_of_center_eq_bot hX hZX
    have hOX := Proof1515.pPrimeCoreOf_eq_pCoreOf_two heqX
    obtain ⟨E, hE, hE27⟩ := exists_E27_of_A10 φ10
    exact hc'1 (eq_one_of_trivial_of_E27_of hR.toSec14Std (J := X)
      (U := CFSG.Open.pCoreOf 2 Y) hY.2.2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
      (hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)) hZX hc'A (hX.1.2 hc'A)
      (fun x hx => hOX ▸ htrivX x hx) hE hE27)
  ·
    exact (hc'1 (hL4 c' hc'A htrivX)).elim

end Odd

theorem item154ProperR_of_char2
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14)
    (h142 : Item142R) (htwo : Item154L3Point (· = 2)) (h5 : Item154L3Five) :
    Item154ProperR :=
  item154ProperR_of_branches h148 h134 h48 hbot
      (item154ProperWhenNHJ_L3_of h148 h134 h48 (item154L3Point_odd h148 h134 h48 ks154U35A7) htwo
          h5)
      (item154ProperWhenHJ_ON h148 h134 h48 h142
          CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.ks1523ONCent_holds
          (ks154ON_of_core ks154ONCore))

end CFSG.RankThree.PartTwo.Sec15.Wales154
