module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.GroupTheory.LieTypeOrderBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixB
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecAS
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

section Step0

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_sup_of_prime_le_normalizer {X T : Subgroup G}
    (hXcard : (Nat.card X).Prime) (hXT : X ≤ normalizer (T : Set G)) (hT2 : IsPGroup 2 T) :
    Group.IsSolvable ↥(X ⊔ T) := by
  haveI : Fact (Nat.card X).Prime := ⟨hXcard⟩
  have hXcyc : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := Nat.card X) dvd_rfl
  haveI : IsCyclic ↥X := hXcyc
  haveI hXsolv : Group.IsSolvable ↥X :=
    Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  haveI hTsolv : Group.IsSolvable ↥T := CFSG.GorensteinWalter.isSolvable_of_isPGroup hT2
  have h := CFSG.Quasithin.A3.isSolvable_sup_of_le_normalizer (M := T) (N := X) hXT
  rw [sup_comm X T]
  exact h

private theorem isHallOddIn_sup_of_prime_le_normalizer {X T : Subgroup G}
    (hXcard : (Nat.card X).Prime) (hXodd : Odd (Nat.card X))
    (hXT : X ≤ normalizer (T : Set G)) (hT2 : IsPGroup 2 T) :
    IsHallOddIn X (X ⊔ T) := by
  obtain ⟨k, hTcard⟩ := hT2.exists_card_eq
  have hinf : X ⊓ T = ⊥ := by
    have hdvdX : Nat.card ↥(X ⊓ T) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
    have hdvdT : Nat.card ↥(X ⊓ T) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hXcard).mp hdvdX with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hr2 : Nat.card X ≠ 2 := by
        rintro h2
        obtain ⟨j, hj⟩ := hXodd
        rw [h2] at hj
        omega
      rw [h1, hTcard] at hdvdT
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hXcard Nat.prime_two).1
        (hXcard.dvd_of_dvd_pow hdvdT))
  have hYcard : Nat.card ↥(X ⊔ T) = Nat.card X * Nat.card T := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := X) (K := T) hXT
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hXsubcard : Nat.card (X.subgroupOf (X ⊔ T)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hidx : (X.subgroupOf (X ⊔ T)).index = Nat.card T := by
    have h := Subgroup.card_mul_index (X.subgroupOf (X ⊔ T))
    rw [hXsubcard, hYcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  exact ⟨le_sup_left, hXodd, ⟨k, by rw [hidx, hTcard]⟩⟩

private theorem isCyclic_quotient_sup_of_prime_le_normalizer {X T Y : Subgroup G}
    [hN : (T.subgroupOf Y).Normal] (hXY : X ≤ Y)
    (hXcard : (Nat.card X).Prime) (hIP : (T.subgroupOf Y) ⊔ (X.subgroupOf Y) = ⊤) :
    IsCyclic (↥Y ⧸ (T.subgroupOf Y)) := by
  classical
  haveI : Fact (Nat.card X).Prime := ⟨hXcard⟩
  have hXcyc : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := Nat.card X) dvd_rfl
  let f : ↥X →* ↥Y ⧸ (T.subgroupOf Y) :=
    (QuotientGroup.mk' (T.subgroupOf Y)).comp (Subgroup.inclusion hXY)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf Y) q
    obtain ⟨i, hi, x, hx, hy⟩ :=
      CFSG.Quasithin.H13.P31Sec.exists_mul_of_sup_eq_top hIP y
    refine ⟨⟨(x : G), hx⟩, ?_⟩
    have hxY : (Subgroup.inclusion hXY (⟨(x : G), hx⟩ : X) : ↥Y) = x := by
      ext
      rfl
    show QuotientGroup.mk' (T.subgroupOf Y)
      (Subgroup.inclusion hXY (⟨(x : G), hx⟩ : X)) = QuotientGroup.mk' (T.subgroupOf Y) y
    have hi1 : QuotientGroup.mk' (T.subgroupOf Y) i = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff i).2 hi
    rw [hxY, hy, map_mul, hi1, one_mul]
  exact isCyclic_of_surjective f hf

private theorem pRank_sup_of_prime_le_normalizer {X T : Subgroup G}
    (hXcard : (Nat.card X).Prime) (hXT : X ≤ normalizer (T : Set G)) (hT2 : IsPGroup 2 T)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (X ⊔ T) ≤ 1 := by
  classical
  set Y : Subgroup G := X ⊔ T with hY
  have hTY : T ≤ Y := le_sup_right
  have hYnorm : Y ≤ normalizer (T : Set G) := sup_le hXT Subgroup.le_normalizer
  haveI hN : (T.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTY).2 hYnorm
  have hTtopzero : CFSG.Open.pRank p (⊤ : Subgroup ↥(T.subgroupOf Y)) = 0 := by
    refine GL83.I713.pRank_top_eq_zero_of_not_dvd hp ?_
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hk]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hTzero : CFSG.Open.pRank p (T.subgroupOf Y) = 0 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (T.subgroupOf Y)]
    exact hTtopzero
  have hIP : (T.subgroupOf Y) ⊔ (X.subgroupOf Y) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTY le_sup_left, sup_comm T X,
      Subgroup.subgroupOf_self]
  have hcycQ : IsCyclic (↥Y ⧸ (T.subgroupOf Y)) :=
    isCyclic_quotient_sup_of_prime_le_normalizer le_sup_left hXcard hIP
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (↥Y ⧸ (T.subgroupOf Y))) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isCyclic hp
      (S := ⊤) (Subgroup.isCyclic_of_le le_top)
  have hle := GL83.I713.pRank_top_le_add_pRank_quotient (G := ↥Y) hp (T.subgroupOf Y)
  rw [hTzero, zero_add] at hle
  have hYle : CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 1 := hle.trans hquot
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y] at hYle

theorem not_mem_uniqueSet_of_le_normalizer (D : Data G) (Ch : Choice2011 G)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {X : Subgroup G}
    (hp : (Nat.card X).Prime) (hodd : Odd (Nat.card X)) (hXM : X ≤ D.M)
    (hXN : X ≤ normalizer (D.T : Set G)) : X ∉ uniqueSet D.M := by
  intro hXU
  have hX2 : Nat.card X ≠ 2 := by
    rintro h2
    obtain ⟨j, hj⟩ := hodd
    rw [h2] at hj
    omega
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hYsolv : Group.IsSolvable ↥(X ⊔ D.T) :=
    isSolvable_sup_of_prime_le_normalizer hp hXN hT2
  have hYhall : IsHallOddIn X (X ⊔ D.T) :=
    isHallOddIn_sup_of_prime_le_normalizer hp hodd hXN hT2
  haveI : Fact (Nat.card X).Prime := ⟨hp⟩
  have hXcyc : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := Nat.card X) dvd_rfl
  haveI : IsCyclic ↥X := hXcyc
  have hXcomm : IsMulCommutative ↥X := inferInstance
  have hYrank : ∀ p ∈ piSet (X ⊔ D.T), p ≠ 2 → CFSG.Open.pRank p (X ⊔ D.T) ≤ 2 := by
    intro p hpPi hp2
    exact (pRank_sup_of_prime_le_normalizer hp hXN hT2 hpPi.1 hp2).trans (by norm_num)
  exact (h211 h1930 c X hp hX2 hYsolv ⟨X, hYhall, hXcomm⟩ hYrank hXU).2 hXN

end Step0

section Arithmetic

private theorem ordA_one_ne_ordTwistedA_two_two_pow {q n : ℕ}
    (hqodd : Odd q) (hq3 : 3 ≤ q) (hn2 : 2 ≤ n) :
    ordA 1 q ≠ ordTwistedA 2 (2 ^ n) := by
  intro h
  obtain ⟨r, -, hmul⟩ := CFSG.GroupTheory.two_part_ordTwistedA_two (by omega : 1 ≤ n)
  have hdvd : 2 ^ (n * 3) ∣ ordTwistedA 2 (2 ^ n) := by
    rw [hmul]
    exact dvd_mul_right _ _
  have hdvdA : 2 ^ (n * 3) ∣ ordA 1 q := by
    rw [h]
    exact hdvd
  have hle : 2 ^ (n * 3) ≤ q + 1 :=
    CFSG.GroupTheory.two_pow_le_of_dvd_ordA_one hqodd hq3 hdvdA
  have hge := CFSG.GroupTheory.ordA_one_ge hqodd hle
  rw [h] at hge
  have hsmall := CFSG.GroupTheory.ordTwistedA_two_small hn2
  omega

theorem not_lieModel_psl2_of_isSU3 {X : Type} [Group X] [Finite X] {n ℓ f : ℕ}
    (hX : IsSU3 X n) : ¬ CFSG.Blueprint.LieModel X .PSL 2 ℓ f := by
  intro hL
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact uc22p21k_not_isL2 hX.1 (Or.inr ⟨n, hX.2⟩) f hL
  · haveI : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL
    have hZ : Subgroup.center X = ⊥ := uc22p21k_center_eq_bot hX.1
    have hU : CFSG.Blueprint.LieModel X .PSU 3 2 n :=
      CFSG.Blueprint.LieModel.of_quotient_center hZ hX.2
    have hℓadm := CFSG.Blueprint.LieModel.admissible hL
    simp only [CFSG.Open.StatedLieAdmissible] at hℓadm
    have hℓprime : ℓ.Prime := hℓadm.1
    have hf1 : 1 ≤ f := hℓadm.2.1
    have hqodd : Odd (ℓ ^ f) := (hℓprime.odd_of_ne_two hℓ2).pow
    have hq3 : 3 ≤ ℓ ^ f := by
      have hℓ3 : 3 ≤ ℓ := by
        have := hℓprime.two_le
        omega
      calc 3 ≤ ℓ := hℓ3
        _ = ℓ ^ 1 := (pow_one ℓ).symm
        _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) hf1
    have hnadm := CFSG.Blueprint.LieModel.admissible hU
    simp only [CFSG.Open.StatedLieAdmissible] at hnadm
    have hn1 : 1 ≤ n := hnadm.2.1
    have hne : 2 ^ n ≠ 2 := by
      intro h2
      exact hnadm.2.2.2 (by rw [h2])
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      exact hne (by rw [this]; norm_num)
    have hcardA : Nat.card X = ordA 1 (ℓ ^ f) := by
      have := CFSG.Blueprint.LieModel.card_eq_lieOrd (t := .PSL) (n := 2) (p := ℓ) (f := f)
        (by norm_num) hL
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using this
    have hcardU : Nat.card X = ordTwistedA 2 (2 ^ n) := by
      have := CFSG.Blueprint.LieModel.card_eq_lieOrd (t := .PSU) (n := 3) (p := 2) (f := n)
        (by norm_num) hU
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using this
    exact ordA_one_ne_ordTwistedA_two_two_pow hqodd hq3 hn2 (hcardA.symm.trans hcardU)

private theorem modEq_two_pow_two_mul_of_dvd_sub_one {n r : ℕ} (hrn : r ∣ 2 ^ n - 1) :
    2 ^ (2 * n) ≡ 1 [MOD r] := by
  have hsquare : r ∣ 2 ^ (2 * n) - 1 := by
    rw [show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [mul_comm, pow_mul]]
    exact hrn.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mpr hsquare).symm

end Arithmetic

section Nine

variable {G : Type} [Group G] [Finite G]

private theorem hkey_of_h847 {D : Data G} {L X : Subgroup G} {n r : ℕ}
    (h847 : F08.R847 D) (hL : L ∈ calC D.M) (hXL : X ≤ L)
    (hXcard : Nat.card X = r) (hSU : IsSU3 (Bar2 L) n) (hrPrime : r.Prime) (hr2 : r ≠ 2)
    (hN : ¬ normalizer (X : Set G) ≤ D.M) (hmod : 2 ^ (2 * n) ≡ 1 [MOD r]) :
    ∀ p ∈ D.sig, p = 3 ∧ n ≡ 1 [MOD 6] ∧ CFSG.Open.evenRank G = 3 := by
  intro p hp
  rcases h847 L hL X hXL r hrPrime hr2 hXcard p hp (Or.inr ⟨n, hSU, hmod⟩) with
    hdir | hcase2 | hcase3
  · exact absurd hdir hN
  · obtain ⟨n', hSU', hn'6, -, hp3, he3, -⟩ := hcase2
    have hnn : n = n' :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.uc2_17_36b_isSU3_param_eq hSU hSU'
    exact ⟨hp3, by simpa [hnn] using hn'6, he3⟩
  · obtain ⟨ℓ, f, hlie, -, -, -, -⟩ := hcase3
    exact absurd hlie (not_lieModel_psl2_of_isSU3 hSU)

private theorem sig_eq_singleton_three {D : Data G} (hsig : D.sig.Nonempty)
    (h : ∀ p ∈ D.sig, p = 3) : D.sig = {3} := by
  obtain ⟨p0, hp0⟩ := hsig
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · rw [← h p0 hp0]
    exact hp0
  · intro p hp
    exact h p hp

private theorem s21_9NFull_of_key (D : Data G) (Ch : Choice2011 G) (hsig : D.sig.Nonempty)
    (h211 : S21_1 D Ch) (h846 : F08.R846 D) (h898 : F08.R898 D) (htor : S21_9TorusN D Ch)
    (hkey : ∀ (L X : Subgroup G) (n r : ℕ), L ∈ calC D.M → (L.subgroupOf D.M).Normal →
      X ≤ L → Nat.card X = r → IsSU3 (Bar2 L) n → r.Prime → r ≠ 2 →
        ¬ normalizer (X : Set G) ≤ D.M → r ∣ 2 ^ n - 1 →
          ∀ p ∈ D.sig, p = 3 ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ CFSG.Open.evenRank G = 3) :
    S21_9NFull D Ch := by
  intro h1930 c L hL hLN n hSU hnp2
  obtain hpow | ⟨s, hsPrime, hsdvd, hsOdd⟩ := Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
  · exact absurd hpow hnp2
  · have hs1 : 1 < s := hsPrime.one_lt
    have hne : 2 ^ s - 1 ≠ 1 := by
      have h2 : 2 < 2 ^ s := by
        simpa using Nat.pow_lt_pow_right (by norm_num) hs1
      omega
    obtain ⟨r, hrPrime, hrdvd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨X, hXcard, hXL, hXN⟩ :=
      htor h1930 c L hL hLN n hSU s hsOdd hsdvd r hrPrime hrdvd
    have hLM : L ≤ D.M := hL.1.le
    have hXM : X ≤ D.M := hXL.trans hLM
    have hs0 : 0 < s := by
      obtain ⟨k, hk⟩ := hsOdd
      omega
    have hrOdd : Odd r := (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hs0).of_dvd_nat hrdvd
    have hr2 : r ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hrOdd
      omega
    have hpX : (Nat.card X).Prime := by rw [hXcard]; exact hrPrime
    have hoddX : Odd (Nat.card X) := by rw [hXcard]; exact hrOdd
    have hXnotU : X ∉ uniqueSet D.M :=
      not_mem_uniqueSet_of_le_normalizer D Ch h211 h1930 c hpX hoddX hXM hXN
    have hN : ¬ normalizer (X : Set G) ≤ D.M := by
      intro hN
      exact hXnotU (h898 L hL n hSU s hsOdd hsdvd r hrPrime hrdvd X hXL hXcard hN)
    have hrn : r ∣ 2 ^ n - 1 := hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsdvd)
    have hkey' := hkey L X n r hL hLN hXL hXcard hSU hrPrime hr2 hN hrn
    have hsig3 : D.sig = {3} := sig_eq_singleton_three hsig fun p hp => (hkey' p hp).1
    obtain ⟨p0, hp0⟩ := hsig
    obtain ⟨-, hn6, he3⟩ := hkey' p0 hp0
    exact ⟨hn6, ⟨hsig3, he3⟩, fun q hq hq3 hqdiv => h846 L hL n hSU q hq hq3 hqdiv⟩

theorem s21_9NFull_of (D : Data G) (Ch : Choice2011 G) (hsig : D.sig.Nonempty)
    (h211 : S21_1 D Ch) (h846 : F08.R846 D) (h847 : F08.R847 D) (h898 : F08.R898 D)
    (htor : S21_9TorusN D Ch) : S21_9NFull D Ch :=
  s21_9NFull_of_key D Ch hsig h211 h846 h898 htor
    fun L X n r hL _ hXL hXcard hSU hrPrime hr2 hN hrn p hp => by
      obtain ⟨hp3, hn6, he3⟩ :=
        hkey_of_h847 h847 hL hXL hXcard hSU hrPrime hr2 hN
          (modEq_two_pow_two_mul_of_dvd_sub_one hrn) p hp
      exact ⟨hp3, Or.inl hn6, he3⟩

theorem s21_9NFull_of_r847SU3G4 (D : Data G) (Ch : Choice2011 G) (hsig : D.sig.Nonempty)
    (h211 : S21_1 D Ch) (h846 : F08.R846 D) (h847 : R847SU3G4 D) (h898 : F08.R898 D)
    (htor : S21_9TorusN D Ch) : S21_9NFull D Ch :=
  s21_9NFull_of_key D Ch hsig h211 h846 h898 htor
    fun L X n r hL hLN hXL hXcard hSU hrPrime hr2 hN hrn =>
      hkey_of_r847SU3G4 h847 hL hLN hXL hXcard hSU hrPrime hr2 hN hrn

theorem s21_9N_of_s21_9NFull {D : Data G} {Ch : Choice2011 G} (h : S21_9NFull D Ch) :
    S21_9N D Ch :=
  fun h1930 c L hL hLN n hSU hnp => (h h1930 c L hL hLN n hSU hnp).2.1.2

end Nine

end CFSG.LocalAnalysis.UniquenessCase.UC22
