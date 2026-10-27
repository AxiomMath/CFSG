module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofNoField
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallBridge
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec21.Item229Pre
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


section Certs


@[expose] def Item1134E27ST : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoS G → A ∈ partTwoT G → Nat.card A = 27 → c ∈ A → c ≠ 1 →
    L ∈ lStarAt A c →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    ((∃ E ∈ partTwoE G, E ≤ A ∧ Sec8.InvTwoBarNontrivial E L) ∨
      (∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
        ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
          Sec4.thetaQuotCentralizer L) ∨
      (¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 3)) ∧
        ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8)) →
    partTwoE G = partTwoF G →
    ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

theorem item1134E27ST_of (h91 : Sec11.Hyp91Never) : Item1134E27ST := by
  intro G _ _ A c L hst hS _ h27 hcA hc1 hL hC halt hEF x hxA
  suffices hk : ¬ (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) from
    ⟨fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩
  intro hk
  have hx1 : x ≠ 1 := by
    rintro rfl
    rcases hk with h | h
    · exact (Sec11.oneNotFieldKind G L).1 h
    · exact (Sec11.oneNotFieldKind G L).2 h
  have h81 : Sec8.Hyp81 G A c L x :=
    ⟨hst, hS.1, hcA, hc1, hL.2, hC, hxA, hx1, hk, fun hbig => absurd hbig (by omega),
      fun _ => hEF⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRW⟩ := Sec11.exists_isSylowOf_inf 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (Subgroup.normalizer (A : Set G))
  refine h91 G A c L x R ⟨h81, h27, ?_, hR, hRW, Or.inr hS⟩
  rcases halt with ⟨E, hE, hEA, hbar⟩ | hA' | hsmall
  · have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1])
    exact Or.inl (Or.inl (hEeq ▸ hbar))
  · exact Or.inl (Or.inr hA')
  · exact Or.inr hsmall

theorem item211NoFieldThreeT_of (hST : Item1134E27ST) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item211NoFieldThreeT := by
  intro G _ _ A E U c L hpair h27 hAT x hx
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hL : L ∈ lStarAt A c :=
    ⟨lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1),
      (lZeroStarAt_subset A c) hpairs.2.2.1⟩
  exact hST G A c L hpair.standing hpair.mem_S hAT (by rw [h27]; norm_num) hcA hpairs.2.1 hL
    (Item211Proof.sectionCentralizer_eq h45 h66 hpair)
    (Or.inl (Item211Proof.exists_invTwoBarNontrivial hpair))
    (hpair.side (mem_partTwoE_of_card hpair h27)) x hx

end Certs

namespace Item21Res6Proof

variable {G : Type} [Group G]

theorem exists_even_mulEquiv_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (h27 : Nat.card A = 3 ^ 3) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) := by
  obtain ⟨-, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  rcases hcase with ⟨-, n, hn, ⟨k, hk⟩, -, hKn, -⟩ | ⟨-, n, hn, ⟨k, hk⟩, -, hKn, -⟩ |
      ⟨-, n, hn, ⟨k, hk⟩, -, hKn | hKn, -⟩ | ⟨-, -, hKn | hKn, -⟩ | ⟨h81, -⟩
  · exact ⟨n, by omega, ⟨k, hk⟩, hKn⟩
  · exact ⟨n, by omega, ⟨k, hk⟩, hKn⟩
  · exact ⟨n, by omega, ⟨k, hk⟩, hKn⟩
  · exact ⟨2 * n, by omega, ⟨n, by omega⟩, hKn⟩
  · exact ⟨2, le_rfl, ⟨1, rfl⟩, hKn⟩
  · exact ⟨4, by norm_num, ⟨2, rfl⟩, hKn⟩
  · rw [h27] at h81
    norm_num at h81

theorem five_dvd_card_projSL_two {m : ℕ} (hm : 2 ≤ m) (he : Even m) :
    5 ∣ Nat.card (projSL 2 (GaloisField 2 m)) := by
  rw [card_projSL_two m (by omega)]
  obtain ⟨k, rfl⟩ := he
  have h1 : (2 ^ (k + k)) ^ 2 = 16 ^ k := by
    rw [← pow_mul, show (k + k) * 2 = 4 * k by ring, pow_mul]
    norm_num
  rw [h1]
  refine Dvd.dvd.mul_left ?_ _
  have h2 : 16 ^ k % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h3 : 1 ≤ 16 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem card_dvd_card_lBar_of_le [Finite G] {K X : Subgroup G} (hKX : K ≤ X)
    [hKs : IsSimpleGroup K] (hK3 : 3 ∣ Nat.card K) : Nat.card K ∣ Nat.card (lBar X) := by
  set ι : K →* lBar X := (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
    (Subgroup.inclusion hKX) with hι
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := X)
    Nat.prime_three
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ι.ker with h | h
  · have hinj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).mp h
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  · exfalso
    apply hN3
    have hle : (⊤ : Subgroup K).map (Subgroup.inclusion hKX) ≤ aschbacherSolvableCore 3 X := by
      rintro _ ⟨k, -, rfl⟩
      have hk : k ∈ ι.ker := h ▸ Subgroup.mem_top k
      rw [MonoidHom.mem_ker, hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hk
      exact hk
    have hcard := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKX), Subgroup.card_top]
      at hcard
    exact hK3.trans hcard

theorem not_five_dvd_card {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* projSL 2 (GaloisField 2 3)) ∨ Sec4.IsSLThreePiAt X 8) :
    ¬ 5 ∣ Nat.card X := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, card_projSL_two 3 (by norm_num)]
    norm_num
  · obtain ⟨F, _, _, h⟩ := h
    rcases h with ⟨-, h81, -⟩ | ⟨hF, -, ⟨e⟩⟩
    · norm_num at h81
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite F
      have hF' : Nat.card F = (2 ^ 3) ^ 2 := by rw [hF]; norm_num
      have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * 3)
        (by rw [← Nat.card_eq_fintype_card, hF', ← pow_mul])
      have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := F) (p := 2) (f := 3) hF'
      have h83 : (2 : ℕ) ^ 3 = 8 := by norm_num
      rw [h83] at hc
      rw [Nat.card_congr e.toEquiv, hc]
      norm_num

end Item21Res6Proof

open Item21Res6Proof

section Certs


theorem item228NoFieldThree_of (hN : Sec11.Item1134E27N) (hST : Item1134E27ST)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222) : Item228NoFieldThree := by
  intro G _ _ A E U c L hpair h27 φ hφ X hX hKX x hxA
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hXs : X ∈ lStarAt A a := ⟨hX, hXa⟩
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe haA ha1
      X hXa
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hCA : A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨haA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXa⟩) ?_
    rw [Nat.card_zpowers, ha3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S X hX)
      fun y hy => hAe.2 y hy.1
  have hsc : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 X).map X.subtype) =
      (Subgroup.zpowers a : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAX, hCA]
  obtain ⟨m, hm2, hme, ⟨eK⟩⟩ := exists_even_mulEquiv_kOf h222 hpair h27 hφ
  have hKs : IsSimpleGroup (kOf A φ) := by
    have := isSimpleGroup_projSL_two hm2
    exact eK.isSimpleGroup
  have hK3 : 3 ∣ Nat.card (kOf A φ) := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m (by omega)]
    have h4 : 4 ∣ (2 ^ m) ^ 2 := by
      rw [← pow_mul]
      exact (pow_dvd_pow 2 (by omega : 2 ≤ m * 2)).trans (by norm_num)
    have hm3 : 3 ∣ (2 ^ m) ^ 2 - 1 := by
      rw [← pow_mul, pow_mul']
      have h1 : 4 ^ m % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h2 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have h3 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h3]
      omega
    exact hm3.mul_left _
  have h5 : 5 ∣ Nat.card (lBar X) :=
    (Nat.card_congr eK.toEquiv ▸ five_dvd_card_projSL_two hm2 hme).trans
      (card_dvd_card_lBar_of_le hKX hK3)
  have hL8 : ¬ Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField 2 3)) :=
    fun h => not_five_dvd_card (X := lBar X) (Or.inl h) h5
  have hU8 : ¬ Sec4.IsSLThreePiAt (X ⧸ aschbacherSolvableCore 3 X) 8 :=
    fun h => not_five_dvd_card (X := lBar X) (Or.inr h) h5
  have hEF := hpair.side (mem_partTwoE_of_card hpair h27)
  have h27' : Nat.card A = 27 := by rw [h27]; norm_num
  by_cases hAT : A ∈ partTwoT G
  · exact hST G A a X hpair.standing hpair.mem_S hAT h27' haA ha1 hXs hsc
      (Or.inr (Or.inr ⟨hL8, hU8⟩)) hEF x hxA
  · exact hN G A a X hpair.standing hpair.mem_S.1 hAT h27' haA ha1 hXs hsc hL8 hU8
      (fun _ => hEF) x hxA

end Certs

end CFSG.RankThree.PartTwo.Sec21
