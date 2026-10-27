module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypesON
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypesInner
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypesOuter
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofList

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedSL)

open Item2130Res3Proof

namespace Item2130Res3Proof

theorem not_isHeisCentral_of_center_eq_bot {X Y : Type} [Group X] [Group Y]
    (hY : Subgroup.center Y = ⊥) : ¬ Sec4.IsHeisCentral X Y := by
  rintro ⟨U, V, -, hcomm, -, ⟨φ⟩, hcard⟩
  have : Finite (U ⊓ V : Subgroup X) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial (U ⊓ V : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨z, hz⟩ := exists_ne (1 : (U ⊓ V : Subgroup X))
  have hzV : (z : X) ∈ V := z.2.2
  have hzZ : (⟨z, hzV⟩ : V) ∈ Subgroup.center V := by
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (hcomm z z.2.1 v v.2).symm
  have hφZ : φ ⟨z, hzV⟩ ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨v, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzZ v]
  rw [hY, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφZ
  have h1 : (z : X) = 1 := congrArg Subtype.val hφZ
  exact hz (Subtype.ext h1)

theorem center_eq_bot_of_isoLThreePi' {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hq : IsQuasisimple X) (h : Sec4.IsoLThreePi X p e) : Subgroup.center X = ⊥ := by
  have hp : p.Prime := Fact.out
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · exact Sec13.Res5Proof.center_eq_bot_of_projSL (n := 3) ⟨hp, he, by norm_num,
      prod_ne_of_fst_ne (by norm_num), prod_ne_of_fst_ne (by norm_num)⟩ hq φ
  · by_cases h2 : p ^ e = 2
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (h2 ▸ dvd_pow_self p (by omega))
      subst hp2
      have he1 : e = 1 := by
        have : 2 ^ e = 2 ^ 1 := by rw [h2, pow_one]
        exact Nat.pow_right_injective le_rfl this
      subst he1
      exact (Sec4.false_of_mulEquiv_projSU_three_two hq φ).elim
    · exact Sec13.Res5Proof.center_eq_bot_of_projSU (n := 3) ⟨hp, he, le_rfl,
        prod_ne_of_snd_ne h2⟩ hq φ

theorem isSLThreePiAt_of_SL3 {X : Type} [Group X] {n : ℕ} (hn : 0 < n) (hne : Even n)
    (φ : X ≃* SL3 n) : Sec4.IsSLThreePiAt X (2 ^ n) := by
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, Or.inl ⟨GaloisField.card 2 n (by omega),
    ?_, ⟨φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _)⟩⟩⟩
  obtain ⟨k, rfl⟩ := hne
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

end Item2130Res3Proof

@[expose] def Item2130TypesHeis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b →
      (Sec4.IsTripleCover (lBar Y) (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover (lBar Y) Blueprint.NativeSporadic.M22 ∨ Sec4.IsSLThreePi (lBar Y)) →
      ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y)

@[expose] def Item2130Heis125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b →
      (Sec4.IsTripleCover (lBar Y) (alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover (lBar Y) Blueprint.NativeSporadic.M22 ∨ Sec4.IsSLThreePi (lBar Y)) →
      Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) →
        Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)

theorem item2130TypesHeis_of (h : Item2130Heis125) : Item2130TypesHeis := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY htype hH
  have hW := h G A E U c L b U₀ Y hcfg h9 hC hAY htype hH
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hC.b_mem.1
  rcases hcfg.irred (Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hC.b_mem)
      (inf_le_right.trans hW) with hbot | htop
  · exact hC.b_ne_one (Subgroup.zpowers_eq_bot.mp hbot)
  · have h3 := Sec13.card_zpowers_of_pow_three hb3 hC.b_ne_one
    rw [htop, h9] at h3
    norm_num at h3

section Certs


@[expose] def Item2130NoFieldY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField

@[expose] def Item2130TypesLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b → Sec4.IsSLThreePiTheta Y →
      ¬ Sec4.IsHeisCentral ↥(Sec13.lBarA b Y A) (lBar Y) →
      (∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧ ¬ KFacts.InducesStdKind Y x .graphField) →
        c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)

end Certs

theorem item2130TypesInspection_of
    (h47 : Sec4.Item4_7) (hNF : Item2130NoFieldY)
    (hHeis : Item2130TypesHeis) (hL3 : Item2130TypesLThree) : Item2130TypesInspection := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY hl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNF' := hNF G A E U c L b U₀ Y hcfg h9 hC
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hq : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  suffices hii : Sec4.IsSLThreePiTheta Y by
    refine hL3 G A E U c L b U₀ Y hcfg h9 hC hAY hii ?_ hNF'
    obtain ⟨p, e, hp, he, hSL | hL⟩ := hii
    · exact hHeis G A E U c L b U₀ Y hcfg h9 hC hAY (Or.inr (Or.inr ⟨p ^ e, hSL⟩))
    · exact not_isHeisCentral_of_center_eq_bot (center_eq_bot_of_isoLThreePi' he hq hL)
  by_cases hout : ∃ a ∈ A, Sec4.InducesOuterTheta a Y
  · obtain ⟨a, haA, ha⟩ := hout
    exact isSLThreePiTheta_of_inducesOuterTheta h47 hcfg hC hNF' haA ha
  push Not at hout
  by_cases hbY : b ∈ Y
  swap
  · exact absurd (le_sup_of_forall_inner hcfg hC hout hbY) hAY
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 3 ^ 3 := by rw [hcfg.card_eq, h9]; norm_num
  have h81 : ¬ Nat.card A = 3 ^ 4 := by rw [hA27]; norm_num
  have hbA : b ∈ A := hC.b_mem.1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hZ := center_ne_bot hbY (hAe.2 b hbA) hC.b_ne_one hYC
  rcases hl with ⟨x, hx, hk⟩ | ⟨-, hH, hT⟩ | ⟨-, p, hp, hp3, h3⟩ | ⟨-, ⟨φ⟩, -⟩ | ⟨h, -⟩ |
      ⟨-, h6⟩ | ⟨h, -⟩ | ⟨-, hON⟩ | ⟨-, ⟨n, hn, hne, h9'⟩, -⟩ | ⟨-, ⟨n, -, -, h10⟩, -⟩ |
      ⟨-, h11, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  ·
    rcases hk with hk | hk
    · exact ((hNF' x hx).1 hk).elim
    · exact ((hNF' x hx).2 hk).elim
  ·
    exact (hHeis G A E U c L b U₀ Y hcfg h9 hC hAY (hT.imp_right Or.inl) hH).elim
  ·
    rcases h3 with h | h | h | h | ⟨e, he, hSL | hL⟩
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inl h)) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inl h))) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inr (Or.inl h)))) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inr (Or.inr (Or.inl h))))) hZ
    · exact ⟨p, e, hp, he, Or.inl hSL⟩
    · exact ⟨p, e, hp, he, Or.inr hL⟩
  ·
    exact absurd (center_eq_bot_of_alt7 hq φ) hZ
  · exact absurd h h81
  ·
    exact absurd (center_eq_bot_of_table hq h6) hZ
  · exact absurd h h81
  ·
    exact (false_of_tripleCover_ON hcfg h9 hC hbY hON).elim
  ·
    rcases h9' with ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact absurd (center_eq_bot_of_lThree hn hq φ) hZ
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ⟨2, n, inferInstance, hn, Or.inl (isSLThreePiAt_of_SL3 hn hne φ)⟩
  ·
    exact absurd (center_eq_bot_of_chevTwo hq h10) hZ
  ·
    exact absurd (center_eq_bot_of_rankTwoEven hq h11) hZ
  · exact absurd h h81
  · exact absurd h h81

theorem item2130LocalTypes_of_items
    (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h41 : Sec4.Item4_1LargePrime) (h47 : Sec4.Item4_7) (hNF : Item2130NoFieldY)
    (hHeis : Item2130Heis125) (hL3 : Item2130TypesLThree) : Item2130LocalTypes :=
  item2130LocalTypes_of h417 h611 h45 h66 h41
    (item2130TypesInspection_of h47 hNF (item2130TypesHeis_of hHeis) hL3)

end CFSG.RankThree.PartTwo.Sec21
