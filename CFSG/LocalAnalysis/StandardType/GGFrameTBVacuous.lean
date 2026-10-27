module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB

theorem not_ggTorusTBGroup_of_card_lt {p r k : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : 0 < p) (hk : k ≤ r)
    (hX : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ k)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')} :
    ¬ GGTorusTBGroup p r R I L' ψ A := by
  rintro ⟨hψ, hker, hperf, hAe, hAI, hr, -, -⟩
  have hXA : IsElemAbelian p (TypeA.inducedSub ψ A) := TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hX _ hXI hXA
  rw [hcardX] at hlt
  have hpow := Nat.pow_le_pow_right hp hk
  omega

theorem frameTBVacuous_of_labelAll {lab : LargeEvenLabel} {k : ℕ} (hk : k ≤ 6)
    (h : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ k) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ r : ℕ, 6 ≤ r → ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
        (A : Subgroup (MulAut L')), ¬ GGTorusTBGroup 3 r R I L' ψ A :=
  h.mono fun _ _ _ _ hX _ hr _ _ _ _ _ =>
    not_ggTorusTBGroup_of_card_lt (by norm_num) (by omega) hX

theorem charP_two_of_nat_card_eq_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hK])

section E6


theorem largeEvenLabelAll_card_lt_E6_two :
    LargeEvenLabelAll ⟨.E6, 0, 1⟩ fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 6 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X _ hX => ?_⟩
  have h := TableBExc.E6Three.card_le_of_isElemAbelian_aut_E6_two (K := K) (by simpa using hK) hX
  exact lt_of_le_of_lt h (by norm_num)

end E6

section F4


theorem largeEvenLabelAll_card_lt_F4_two :
    LargeEvenLabelAll ⟨.F4, 0, 1⟩ fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 6 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X _ hX => ?_⟩
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_nat_card_eq_two hK2
  have h := TableBF4Two.card_le_mulAut (K := K) hK2 hX
  exact lt_of_le_of_lt h (by norm_num)

end F4

section Holds


theorem ggFrameTBVacuousInput_holds : GGFrameTBVacuousInput := by
  rintro ⟨t, l, n⟩ hlab hn htab
  dsimp only at hn htab
  subst hn
  have hs : LargeEvenSplit 3 ⟨t, l, 1⟩ := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  cases t with
  | A | twA | B | C | D | twD | twE6 | E7 | E8 => exact absurd trivial htab
  | G2 =>
    obtain ⟨-, -, h⟩ := hlab
    dsimp only at h
    omega
  | twB2 | twF4 =>
    obtain ⟨-, -, -, h⟩ := hlab
    dsimp only at h
    omega
  | E6 =>
    obtain ⟨-, rfl⟩ := hlab
    exact frameTBVacuous_of_labelAll le_rfl largeEvenLabelAll_card_lt_E6_two
  | F4 =>
    obtain ⟨-, rfl⟩ := hlab
    exact frameTBVacuous_of_labelAll le_rfl largeEvenLabelAll_card_lt_F4_two
  | triD4 =>
    exact frameTBVacuous_of_labelAll (k := 3) (by norm_num)
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
        (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) Nat.prime_three hlab rfl hs)
  | B2der =>
    exact frameTBVacuous_of_labelAll (k := 3) (by norm_num)
      (largeEvenLabelAll_card_lt_b2derThree ⟨rfl, rfl⟩)
  | G2der =>
    exact frameTBVacuous_of_labelAll (k := 3) (by norm_num)
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der Nat.prime_three hlab rfl hs)
  | twF4der =>
    exact frameTBVacuous_of_labelAll (k := 3) (by norm_num)
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds Nat.prime_three hlab rfl hs)

end Holds

end CFSG.StandardType.FrameRoute
