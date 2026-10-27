module

public import CFSG.RankThree.PartTwo.Sec15.Item15More
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item154Pi (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (L : Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0 A LB, ∀ X ∈ scriptY4 A LB, X ≤ Y →
    ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
      ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨
      (∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) ∧
        IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) ∧
        L ≠ (L ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L) ∨
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) ∧
        (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).relIndex R = 4 ∧
        (∀ r ∈ R, r ^ 2 ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) ∧
        ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
          R ⊓ Subgroup.centralizer ({d} : Set G) ≤ centralizerSection Y (CFSG.Open.pCoreOf 2 Y))

omit [Finite G] in
theorem item154_of_item154Pi {A : Subgroup G} {LB : Subgroup G → Subgroup G} {L : Subgroup G}
    (h : Item154Pi A LB L) : Item154 A LB L := by
  intro Y hY X hX hXY R hR
  rcases h Y hY X hX hXY R hR with h1 | ⟨n, m, hn, hm, hY', hXε, -, hL⟩ | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨n, m, hn, hm, hY', hXε, hL⟩)
  · exact Or.inr (Or.inr h3)

theorem card_quot_pCore_eq_of_eq_sup {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K = X ⊔ CFSG.Open.pCoreOf 2 K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := CFSG.Open.pCoreOf 2 K with hD
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hDK : D ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hXP : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hPD : P ≤ D := by
    have hPDK : P ⊔ D ≤ K := sup_le (hPX.trans hXK) hDK
    have hnorm : K ≤ Subgroup.normalizer ((P ⊔ D : Subgroup G) : Set G) := by
      calc K = X ⊔ D := hK
        _ ≤ Subgroup.normalizer ((P ⊔ D : Subgroup G) : Set G) :=
          sup_le (le_normalizer_sup hXP (hXK.trans hKD))
            ((le_sup_right : D ≤ P ⊔ D).trans Subgroup.le_normalizer)
    have hPD2 : IsPGroup 2 (P ⊔ D : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hP2 hD2 (hPX.trans (hXK.trans hKD))
    exact le_sup_left.trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPDK hnorm hPD2)
  have hXD : X ⊓ D = P := by
    refine le_antisymm ?_ (le_inf hPX hPD)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hXK.trans hKD)) (hD2.to_le inf_le_right)
  have h1 := Sec6.card_sup_mul_card_inf (hXK.trans hKD)
  rw [← hK, hXD] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have hcD : Nat.card (CFSG.pCore 2 ↥K) = Nat.card D := by
    rw [hD, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
  have hcP : Nat.card (CFSG.pCore 2 ↥X) = Nat.card P := by
    rw [hP, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  rw [h2, h3, hcD, hcP] at h1
  have hpos : 0 < Nat.card D * Nat.card P := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * (Nat.card D * Nat.card P)
      = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * Nat.card D * Nat.card P := by ring
    _ = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card P * Nat.card D := h1
    _ = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * (Nat.card D * Nat.card P) := by ring

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one

private theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) :=
  ((Nat.even_pow' (by omega)).mpr even_two).add_one

theorem exists_card_mul_of_isLThreeEpsAt {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (hX : IsLThreeEpsAt X 2 k) :
    ∃ g u : ℕ, g ∣ 3 ∧ Odd u ∧ Nat.card X * g = 2 ^ (3 * k) * u := by
  have h2k : 1 ≤ 2 * k := by omega
  have h3k : 1 ≤ 3 * k := by omega
  rcases hX with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 k)
    rw [GaloisField.card 2 k (by omega), ← Nat.card_congr φ.toEquiv] at hc
    simp only [← pow_mul] at hc
    refine ⟨Nat.gcd 3 (2 ^ k - 1), (2 ^ (2 * k) - 1) * (2 ^ (3 * k) - 1), Nat.gcd_dvd_left 3 _,
      (odd_two_pow_sub_one h2k).mul (odd_two_pow_sub_one h3k), ?_⟩
    rw [mul_comm 3 k, mul_comm 2 k]
    exact hc
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 k hk
    rw [← Nat.card_congr φ.toEquiv] at hc
    simp only [← pow_mul] at hc
    refine ⟨Nat.gcd 3 (2 ^ k + 1), (2 ^ (2 * k) - 1) * (2 ^ (3 * k) + 1), Nat.gcd_dvd_left 3 _,
      (odd_two_pow_sub_one h2k).mul (odd_two_pow_add_one h3k), ?_⟩
    rw [mul_comm 3 k, mul_comm 2 k]
    exact hc

theorem false_of_card_eq_projSL {X : Type} [Group X] {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hX : IsLThreeEpsAt X 2 n)
    (hc : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))) =
      Nat.card X) : False := by
  have hnm : 1 ≤ 2 * n * m := by nlinarith
  obtain ⟨g₁, u₁, hg₁, -, h₁⟩ :=
    exists_card_mul_of_isLThreeEpsAt hnm (Or.inl ⟨MulEquiv.refl _⟩)
  obtain ⟨g₂, u₂, -, hu₂, h₂⟩ := exists_card_mul_of_isLThreeEpsAt hn hX
  rw [hc] at h₁
  have hcop : Nat.Coprime (2 ^ (3 * (2 * n * m))) g₁ :=
    Nat.Coprime.coprime_dvd_right hg₁ (Nat.Coprime.pow_left _ (by norm_num))
  have hd : 2 ^ (3 * (2 * n * m)) ∣ Nat.card X :=
    hcop.dvd_of_dvd_mul_right (h₁ ▸ Dvd.intro _ rfl)
  have hd' : 2 ^ (3 * n) * 2 ∣ Nat.card X := by
    rw [← pow_succ]
    exact (Nat.pow_dvd_pow 2 (by nlinarith)).trans hd
  have hd'' : 2 ^ (3 * n) * 2 ∣ 2 ^ (3 * n) * u₂ := h₂ ▸ hd'.mul_right g₂
  have h2u : 2 ∣ u₂ := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd''
  exact (Nat.not_even_iff_odd.mpr hu₂) (even_iff_two_dvd.mpr h2u)

theorem false_of_j2_a5 {X K : Subgroup G} (hXK : X ≤ K) (hK : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (φK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2)
    (φX : ↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) : False := by
  have hc := card_quot_pCore_eq_of_eq_sup hXK hK
  rw [Nat.card_congr φK.toEquiv, Nat.card_congr φX.toEquiv, KFacts.KS14.card_nativeJ2,
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at hc
  norm_num at hc

end CFSG.RankThree.PartTwo.Sec16
