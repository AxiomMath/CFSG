module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitField
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldUni
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthLTwD
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTwDOmegaFieldInnR : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGFieldInnR p m (OrthRest.RMinus K m b c) (LargeEvenInnSet (OrthRest.RMinus K m b c))

namespace LIDTwDF

section Labels


theorem not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := fun h4 => hp2 (by
  have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

theorem largeEvenLabelAll_twD3_data {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twD) (hl : lab.rank = 3)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpq
  subst htag hl
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hp4 := not_dvd_four hp hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hdq : (4, 2 ^ n) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
  have hD : 4 / p + 1 < 3 := by
    have : 4 / p ≤ 4 / 3 := Nat.div_le_div_left hp3 (by norm_num)
    omega
  have hr2 : 2 ≤ ggUnitaryTorusRank p 4 := by
    simp only [ggUnitaryTorusRank, hp4, ↓reduceIte]
    omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, hq, ⟨ggUnitaryTorusRank p 4, hr2,
    ggTorusLift_unitary hK hn (by norm_num) hdq hp hpq,
    ggFieldInnR_unitary_toral hK hn (by norm_num) hdq hD hp hpq⟩,
    InndiagSU.ggOutdiagOdd_unitary hK hn (by norm_num)
      (fun ⟨h1, _⟩ => absurd h1 (by norm_num)) p⟩

theorem largeEvenLabelAll_twDrest_data (hΩ : GGTwDOmegaFieldInnR) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (htag : lab.tag = .twD) (hl : 4 ≤ lab.rank)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpq
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hQ
  exact ⟨K, i1, i2, hK, b, c, hbc, hq, ⟨l - 1, by omega,
    ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpq hbc,
    hΩ K n (l - 1) p b c hK (by omega) hp hpq hbc⟩,
    ggOutdiagOdd_of_prime OrthRest.ggOutdiagPrime_inn⟩

theorem data_torus {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I) :
    (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I := by
  obtain ⟨⟨r, hr, hlift, -⟩, hO⟩ := h
  exact ⟨⟨r, hr, hlift⟩, hO⟩

theorem largeEvenLabelAll_twDField_data (hΩ : GGTwDOmegaFieldInnR) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGOrthLTwDFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I) ∧ GGOutdiagOdd p R I := by
  obtain ⟨ht, hl, hpq, -⟩ := h
  by_cases h3 : lab.rank = 3
  · exact largeEvenLabelAll_twD3_data hp hlab ht h3 hpq
  · exact largeEvenLabelAll_twDrest_data hΩ hp ht (by omega) hpq

end Labels

end LIDTwDF

section Holds


theorem ggBstarInnerDiagLInputOn_of_le_twDField_of_omega (hΩ : GGTwDOmegaFieldInnR)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGOrthLTwDFieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  by_cases hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)
  · exact ggInnerDiagOnLab_bstar_of_fieldInn
      (fun _ _ hp hlab hs => (LIDTwDF.largeEvenLabelAll_twDField_data hΩ hp hlab
        (hS _ _ hs)).mono fun _ _ _ _ hP => hP.1) hC hM hinn
  · obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => S p lab)
      (P' := fun R _ I _ => (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I)
      (fun lab hlab hs => (LIDTwDF.largeEvenLabelAll_twDField_data hΩ hp hlab
        (hS p lab hs)).mono fun _ _ _ _ hP => LIDTwDF.data_torus hP)
      (fun _ _ _ _ _ _ hP => hP.1) hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r, hr2, hlift⟩, hOD⟩ :=
      largeEvenRawDatum_exists hraw
    have hnc := UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift
    obtain ⟨-, -, -, -, -, hβ, hS', hst⟩ := hC.1
    rcases ggInnLocal_or_delta hp hβ.2.1 hS' hnc hL θ hBN h3 hOD hst.2.1 with hU | hT₀
    · exact absurd hU hinn
    · exact ggInnerDiagOnLab_bstar_of_moved hC hnc hM hT₀

end Holds

end CFSG.StandardType
