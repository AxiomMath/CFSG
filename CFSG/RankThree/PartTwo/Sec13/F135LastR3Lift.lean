module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Lift
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last



open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem r3a_exists_elemAbelian_cube {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    {E : Subgroup N} (hE : CFSG.Open.IsElemAbelian p E) (hdvd : p ^ 3 ∣ Nat.card E) :
    ∃ K : Subgroup N, CFSG.Open.IsElemAbelian p K ∧ Nat.card K = p ^ 3 ∧ K ≤ E := by
  unfold CFSG.Open.IsElemAbelian at hE
  have h1 : Nat.card (⊥ : Subgroup N) ∣ p ^ 3 := by
    rw [Subgroup.card_bot]
    exact one_dvd _
  obtain ⟨K, hKcard, -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp h1 hdvd bot_le
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, hKE ha⟩ : E) ⟨b, hKE hb⟩)
  refine ⟨K, ?_, hKcard, hKE⟩
  unfold CFSG.Open.IsElemAbelian
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hE.2 x (hKE hx)⟩

theorem r3a_pRank_le_two {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N))
    (H : Subgroup N) (hH : CFSG.Open.IsTwoLocal H) : CFSG.Open.pRank p H ≤ 2 := by
  obtain ⟨T, hT, hT2, rfl⟩ := hH
  unfold CFSG.Open.pRank
  apply csSup_le'
  intro k hk
  obtain ⟨E, hE, hEel, hEcard⟩ := hk
  by_contra hk2
  have hdvd : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p (by omega)
  obtain ⟨K, hKel, hKcard, hKE⟩ := r3a_exists_elemAbelian_cube hp hEel hdvd
  exact hno K T hKel hKcard hT hT2 (hKE.trans hE)

theorem r3_odd_of_cube {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (R : Subgroup M)
    [R.Normal] (hR : ¬ p ∣ Nat.card R) {A : Subgroup M} (hA : CFSG.Open.IsElemAbelian p A)
    (hA3 : Nat.card A = p ^ 3)
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    Odd (Nat.card R) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card R := by
    rcases Nat.even_or_odd (Nat.card R) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have hFp : IsPGroup p A := IsPGroup.of_card hA3
  have hAN : A ≤ Subgroup.normalizer (R : Set M) := Subgroup.le_normalizer_of_normal
  obtain ⟨T, hT, hAT⟩ := exists_invariant_sylow_two hp hFp hAN hR
  have hpos : 0 < (Nat.card R).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have hTne : T ≠ ⊥ := by
    intro hbot
    subst hbot
    have hc := hT.card_eq
    rw [Subgroup.card_bot] at hc
    exact absurd hc (ne_of_lt (Nat.one_lt_two_pow hpos.ne'))
  exact hno A T hA hA3 hTne hT.isPGroup hAT

theorem r3_hnoN {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R)
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    ∀ A T : Subgroup (M ⧸ R), CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set (M ⧸ R)) := by
  intro A T hA hA3 hT hT2 hAT
  have hA2 : IsPGroup p A := IsPGroup.of_card hA3
  obtain ⟨F, hFp, hFmap, hFR⟩ := exists_pSubgroup_lift hp R hR hA2
  have hA' : CFSG.Open.IsElemAbelian p (F.map (QuotientGroup.mk' R)) := by
    rw [hFmap]
    exact hA
  obtain ⟨hFel, hFcard⟩ := isElemAbelian_of_lift R hFR hA'
  have hFcard3 : Nat.card F = p ^ 3 := by
    rw [hFcard, hFmap, hA3]
  have hFT : F.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (T : Set (M ⧸ R)) := by
    rw [hFmap]
    exact hAT
  obtain ⟨T', hT'ne, hT'2, hFT'⟩ := exists_two_lift hp hp2 R hR hFp hT hT2 hFT
  exact hno F T' hFel hFcard3 hT'ne hT'2 hFT'

theorem r3_localRank_lt {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N)) :
    CFSG.Assembly.RankThreeEven.localRank p N < 3 := by
  have hle : CFSG.Open.twoLocalPrimeRank p N ≤ 2 := by
    unfold CFSG.Open.twoLocalPrimeRank
    apply csSup_le'
    rintro k ⟨H, hH, rfl⟩
    exact r3a_pRank_le_two hp hno H hH
  show CFSG.Open.twoLocalPrimeRank p N < 3
  omega

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem r3_pPrimeCore_facts {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (CFSG.pPrimeCore p M) ∧
      CFSG.pPrimeCore p (M ⧸ CFSG.pPrimeCore p M) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, CFSG.pPrimeCore_quotient_eq_bot hp⟩
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp
    (CFSG.pPrimeCore_coprime_card (p := p) (G := M))

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3_map_center_le {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {Y : Subgroup M}
    (hY : Y ≤ Subgroup.center M) : Y.map (QuotientGroup.mk' R) ≤ Subgroup.center (M ⧸ R) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R g
  have hym : ∀ g : M, g * y = y * g := Subgroup.mem_center_iff.mp (hY hy)
  rw [← map_mul, ← map_mul, hym m]

theorem r3_inj_of_comp {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {E : Subgroup M}
    (h : Function.Injective ((QuotientGroup.mk' R).comp E.subtype)) :
    ∀ x ∈ E, ∀ y ∈ E, QuotientGroup.mk' R x = QuotientGroup.mk' R y → x = y := by
  intro x hx y hy hxy
  have hxy' : ((QuotientGroup.mk' R).comp E.subtype) ⟨x, hx⟩ =
      ((QuotientGroup.mk' R).comp E.subtype) ⟨y, hy⟩ := hxy
  exact congrArg Subtype.val (h hxy')

theorem r3_inf_comm_map {M : Type*} [Group M] (R : Subgroup M) [R.Normal] {E Y : Subgroup M}
    (hinj : ∀ x ∈ E, ∀ y ∈ E, QuotientGroup.mk' R x = QuotientGroup.mk' R y → x = y)
    (hYE : Y ≤ E) (h : Y ⊓ ⁅E, E⁆ = ⊥) :
    Y.map (QuotientGroup.mk' R) ⊓
      ⁅E.map (QuotientGroup.mk' R), E.map (QuotientGroup.mk' R)⁆ = ⊥ := by
  rw [← Subgroup.map_commutator E E (QuotientGroup.mk' R), eq_bot_iff]
  rintro g ⟨hgY, hgC⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hgY
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hgC
  have hcE : c ∈ E := Subgroup.commutator_le_of_le (le_refl E) (le_refl E) hc
  have hyc : c = y := hinj c hcE y (hYE hy) hcg
  have hyB : y ∈ Y ⊓ ⁅E, E⁆ := Subgroup.mem_inf.mpr ⟨hy, (by rw [← hyc]; exact hc)⟩
  rw [h, Subgroup.mem_bot] at hyB
  rw [Subgroup.mem_bot, hyB, map_one]

theorem r3_isElemAbelian_map {M N : Type*} [Group M] [Group N] (f : M →* N) {A : Subgroup M}
    {p : ℕ} (hA : CFSG.Open.IsElemAbelian p A) : CFSG.Open.IsElemAbelian p (A.map f) := by
  unfold CFSG.Open.IsElemAbelian at hA ⊢
  obtain ⟨hcomm, hpow⟩ := hA
  refine ⟨Subgroup.map_isMulCommutative A f, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hpow a ha, map_one]

end CFSG.RankThree.PartTwo.Sec13.F135Last
