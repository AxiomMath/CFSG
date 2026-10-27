module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89G2
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.LieType.Chevalley.ExactG2FiniteOrder

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item812Res3

theorem card_ne_seven_twenty_of_isoGTwoEven
    {H : Type} [Group H] {m : ℕ} (hH : IsoGTwoEven H m) : Nat.card H ≠ 720 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hH
  have hcard : Nat.card H = (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact (CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1
  intro hc
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · rw [hcard] at hc
      norm_num at hc
  · have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm : 2 ^ 2 ≤ 2 ^ m)
    have h1 : 4096 ≤ (2 ^ m) ^ 6 := (Nat.pow_le_pow_left hq 6 : 4 ^ 6 ≤ (2 ^ m) ^ 6)
    have h2' : 16 ≤ (2 ^ m) ^ 2 := (Nat.pow_le_pow_left hq 2 : 4 ^ 2 ≤ (2 ^ m) ^ 2)
    have h2 : 1 ≤ (2 ^ m) ^ 6 - 1 := by omega
    have h3 : 1 ≤ (2 ^ m) ^ 2 - 1 := by omega
    have h4 : 4096 ≤ (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) :=
      calc 4096 = 4096 * 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem eq_one_of_card_projSp_two {m : ℕ} (hm : 1 ≤ m)
    (hc : Nat.card (projSp 2 (GaloisField 2 m)) = 720) : m = 1 := by
  by_contra hm1
  have hm2 : 2 ≤ m := by omega
  rw [CFSG.RankThree.PartTwo.Sec21.card_projSp_two hm2,
    CFSG.RankThree.PartTwo.Sec21.ordBC_two_eq (by omega)] at hc
  have hq : 4 ≤ 2 ^ m := (Nat.pow_le_pow_right (by norm_num) hm2 : 2 ^ 2 ≤ 2 ^ m)
  have h1 : 256 ≤ (2 ^ m) ^ 4 := (Nat.pow_le_pow_left hq 4 : 4 ^ 4 ≤ (2 ^ m) ^ 4)
  have h2' : 16 ≤ (2 ^ m) ^ 2 := (Nat.pow_le_pow_left hq 2 : 4 ^ 2 ≤ (2 ^ m) ^ 2)
  have h2 : 15 ≤ (2 ^ m) ^ 2 - 1 := by omega
  have h3 : 255 ≤ (2 ^ m) ^ 4 - 1 := by omega
  have h4 : 720 < (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
    calc 720 < 256 * (15 * 255) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  omega

end Item812Res3

@[expose] def Item89XY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) ∧
        (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1)))

theorem item89XY_of (h88 : Item88) (h84 : Pair84A) (hJ : KF89J) (hD4 : KF89TrialityD4)
    (hRee : KF89ReeF4) : Item89XY := by
  intro G _ _ A c L a b X n h Y hY hIJ
  have h8 := h88 G A c L a b X n h Y hY hIJ
  obtain ⟨hY', hJ'⟩ := hJ G A c L a b X n h Y hY hIJ h8
  have hout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  exact ⟨projSp_of_perfectResidual_barCentralizer kF89GTwo hD4 hRee h hout hJ', hY'⟩

theorem item89XY_of_d4
    (h88 : Item88) (h84 : Pair84A) (hJ : KF89J) (hD4 : KF89D4OtherClass) : Item89XY :=
  item89XY_of h88 h84 hJ (kF89TrialityD4_of hD4) kF89ReeF4

@[expose] def Pair89InConfig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, ∃ (c' : G) (L' : Subgroup G) (a' b' : G) (X' : Subgroup G) (n' : ℕ),
      Sec8Pair G A c' L' a' b' X' n' ∧
        ((b', X') = p ∨
          ((c', L') = p ∧ IsUnitaryTwo (L' ⧸ aschbacherSolvableCore 3 L') (3 * n')))

theorem Sec8Pair.eq_one_of_isUnitaryTwo (hXY : Item89XY) (h87 : Item87) (h84 : Pair84A)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n)) : n = 1 := by
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  obtain ⟨hX, -⟩ := hXY G A c L a b X n h Y hY hIJ
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  have hX' : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * 1))) := by
    simpa using hX
  obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero ha3 hout hX'
  have hC : Nat.card (barCentralizer (Subgroup.zpowers a) X) = 720 := by
    rw [Nat.card_congr ι.toEquiv, Item812Res2.card_projSp_two_one]
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  rcases h.centralizer_of_unitary ⟨3 * n, hU⟩ with hG2 | hSp
  · exact absurd hC (Item812Res3.card_ne_seven_twenty_of_isoGTwoEven hG2)
  · obtain ⟨κ⟩ := hSp
    rw [Nat.card_congr κ.toEquiv] at hC
    exact Item812Res3.eq_one_of_card_projSp_two hn1 hC

theorem pair89Omega_of (hXY : Item89XY) (h87 : Item87) (h84 : Pair84A)
    (hcfg : Pair89InConfig) : Pair89Omega := by
  intro G _ _ A c L a b X n h Y hY hIJ h8 hX hY' p hp
  obtain ⟨c', L', a', b', X', n', h', hcase⟩ := hcfg G A c L a b X n h p hp
  rcases hcase with hp' | ⟨hp', hU⟩
  · subst hp'
    obtain ⟨Y'', hY'', hIJ''⟩ := h87 G A c' L' a' b' X' n' h'
    exact Or.inr (hXY G A c' L' a' b' X' n' h' Y'' hY'' hIJ'').1
  · subst hp'
    have hn1 := h'.eq_one_of_isUnitaryTwo hXY h87 h84 hU
    subst hn1
    exact Or.inl hU

theorem item89_of_split (h88 : Item88) (hXY : Item89XY) (hΩ : Pair89Omega) : Item89 := by
  intro G _ _ A c L a b X n h Y hY hIJ
  obtain ⟨hX, hY'⟩ := hXY G A c L a b X n h Y hY hIJ
  exact ⟨hX, hY', hΩ G A c L a b X n h Y hY hIJ (h88 G A c L a b X n h Y hY hIJ) hX hY'⟩

end CFSG.RankThree.PartTwo.Sec8
