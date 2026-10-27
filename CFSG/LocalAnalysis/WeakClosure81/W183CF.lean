module

public import CFSG.Quasithin.Background.E1Sections
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossChar
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
import CFSG.LocalAnalysis.WeakClosure81.W183CF3Aux1
public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor
  lieSylowExponent)

@[expose] def OddTranspFactor (T : Type) [Group T] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
  (∃ n f : ℕ, LieModel T .PSp n 2 f ∨ LieModel T .PSU n 2 f ∨ LieModel T .POmegaPlus n 2 f ∨
      LieModel T .POmegaMinus n 2 f ∨ LieModel T .PSL 2 2 f ∨ LieModel T .PSL 4 2 f ∨
      LieModel T .twistedB2 0 2 f) ∨
  (∃ q n f : ℕ, (q = 3 ∨ q = 5) ∧ f ≤ 2 ∧
      (LieModel T .PSL 2 q f ∨ LieModel T .PSp 2 q 1 ∨ LieModel T .PSL 4 q 1 ∨
        LieModel T .PSU 4 q 1 ∨ LieModel T .POmegaOdd n q 1 ∨ LieModel T .POmegaPlus n q 1 ∨
        LieModel T .POmegaMinus n q 1)) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi22 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi23 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi24Prime

@[expose] def OddTranspositionCompFactorInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ →
    ∀ (T : Type) [Group T], CFSG.Quasithin.E1.IsCompositionFactor X T →
      (∃ a b : T, a * b ≠ b * a) → OddTranspFactor T

@[expose] def Socle186Shape (S : Type) [Group S] : Prop :=
  CFSG.Quasithin.F6.IsL2 2 2 S ∨ LieModel S .PSU 3 2 2 ∨
  LieModel S .PSL 3 2 1 ∨ LieModel S .PSL 3 2 2 ∨
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ LieModel S .PSp 2 2 2 ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e S) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 3 ∧ LieModel S .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel S .PSU 3 p 1))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel S .PSp 2 p 1)

@[expose] def Tail1812TwoNoSectionCF : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Socle186Shape T → OddTranspFactor T →
    CFSG.Quasithin.F6.IsL2 2 2 T ∨ LieModel T .PSU 3 2 2 ∨
      Nonempty (T ≃* alternatingGroup (Fin 6)) ∨ LieModel T .PSp 2 2 2 ∨
      CFSG.Quasithin.F6.IsL2 5 2 T ∨ LieModel T .PSp 2 5 1 ∨ LieModel T .PSp 2 3 1

@[expose] def ArtinDistinctOddOrders : Prop :=
  ∀ (T T' : Type) [Group T] [Group T'] [Finite T] [Finite T'], IsSimpleGroup T → IsSimpleGroup T' →
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → p ≠ q → (q = 3 ∨ q = 5) →
      ((∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨ LieModel T .PSL 3 p 1 ∨
        LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1) →
      ((∃ f : ℕ, f ≤ 2 ∧ LieModel T' .PSL 2 q f) ∨ LieModel T' .PSp 2 q 1 ∨
        LieModel T' .PSL 4 q 1 ∨ LieModel T' .PSU 4 q 1 ∨
        (∃ n : ℕ, LieModel T' .POmegaOdd n q 1 ∨ LieModel T' .POmegaPlus n q 1 ∨
          LieModel T' .POmegaMinus n q 1)) →
      Nat.card T ≠ Nat.card T'

private theorem w183_card_PSL_3_2_1 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 3 2 1) : Nat.card T = 168 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]

private theorem w183_card_PSL_3_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 3 2 2) : Nat.card T = 20160 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
  rw [hd] at hM
  have hnum : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by
    simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]
  rw [hnum] at hM
  omega

private theorem w183_card_PSU_3_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSU 3 2 2) : Nat.card T = 62400 := by
  obtain ⟨-, hM, -⟩ := hO T .PSU 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSU 3 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  have h2 : Even (2 : ℕ) := by decide
  have h3 : ¬ Even (3 : ℕ) := by decide
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair, h2, h3]

private theorem w183_card_PSp_2_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSp 2 2 2) : Nat.card T = 979200 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]

private theorem w183_card_PSL_2_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 2 2 2) : Nat.card T = 60 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 2 = {2} by decide]

theorem w183_not_isSporadic_fischer
    (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Socle186Shape T ∨ ∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ p ≠ 2 ∧ LieModel T t n p f) :
    ¬ (CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic T .Fi24Prime) := by
  have hsp22 : CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder .Fi22 = 64561751654400 := by
    norm_num [CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder,
      CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors]
  have hsp23 : CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder .Fi23 =
      4089470473293004800 := by
    norm_num [CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder,
      CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors]
  have hsp24 : CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder .Fi24Prime =
      1255205709190661721292800 := by
    norm_num [CFSG.ComponentClassification.GSThmB.QPUSpor.sporOrder,
      CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors]
  have oddKey : ∀ m : ℕ, (m = 64561751654400 ∨ m = 4089470473293004800 ∨
      m = 1255205709190661721292800) →
      CFSG.ComponentClassification.HarrisLit.T1.SporRow.OddLieOrder m → False := by
    intro m hmm hodd
    rcases hmm with hh | hh | hh
    · rw [hh] at hodd
      exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_sporOrder .Fi22
        (hsp22 ▸ hodd)
    · rw [hh] at hodd
      exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_sporOrder .Fi23
        (hsp23 ▸ hodd)
    · rw [hh] at hodd
      exact CFSG.ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_sporOrder .Fi24Prime
        (hsp24 ▸ hodd)
  have key : ∀ m : ℕ, (m = 64561751654400 ∨ m = 4089470473293004800 ∨
      m = 1255205709190661721292800) → Nat.card T = m → False := by
    intro m hmm hm
    rcases h with hS | ⟨t, n, p, f, hp, hp2, hmodel⟩
    · rcases hS with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
      · have hc : Nat.card T = 60 := w183_card_PSL_2_2_2 hO (Or.inl ⟨by decide, h1⟩)
        omega
      · have hc : Nat.card T = 62400 := w183_card_PSU_3_2_2 hO h2
        omega
      · have hc : Nat.card T = 168 := w183_card_PSL_3_2_1 hO h3
        omega
      · have hc : Nat.card T = 20160 := w183_card_PSL_3_2_2 hO h4
        omega
      · obtain ⟨e⟩ := h5
        have hc : Nat.card T = 360 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          norm_num
        omega
      · have hc : Nat.card T = 979200 := w183_card_PSp_2_2_2 hO h6
        omega
      · rcases h7 with ⟨p, e, hp, hp2, -, hL⟩
        have hmodel : LieModel T .PSL 2 p e := Or.inl ⟨by decide, hL⟩
        refine oddKey m hmm ?_
        obtain ⟨-, h1', h2'⟩ := hO T .PSL 2 p e hmodel.admissible hmodel
        rw [← hm]
        exact ⟨.PSL, 2, p, e, hp, hp2, hmodel.admissible, h1', h2'⟩
      · rcases h8 with ⟨p, hp, hp2, h8'⟩
        refine oddKey m hmm ?_
        rw [← hm]
        rcases h8' with ⟨-, hL⟩ | ⟨-, hL⟩
        · obtain ⟨-, h1', h2'⟩ := hO T .PSL 3 p 1 hL.admissible hL
          exact ⟨.PSL, 3, p, 1, hp, hp2, hL.admissible, h1', h2'⟩
        · obtain ⟨-, h1', h2'⟩ := hO T .PSU 3 p 1 hL.admissible hL
          exact ⟨.PSU, 3, p, 1, hp, hp2, hL.admissible, h1', h2'⟩
      · rcases h9 with ⟨p, hp, hp2, hL⟩
        refine oddKey m hmm ?_
        obtain ⟨-, h1', h2'⟩ := hO T .PSp 2 p 1 hL.admissible hL
        rw [← hm]
        exact ⟨.PSp, 2, p, 1, hp, hp2, hL.admissible, h1', h2'⟩
    · refine oddKey m hmm ?_
      obtain ⟨-, h1', h2'⟩ := hO T t n p f hmodel.admissible hmodel
      rw [← hm]
      exact ⟨t, n, p, f, hp, hp2, hmodel.admissible, h1', h2'⟩
  rintro (h22 | h23 | h24)
  · obtain ⟨e⟩ := h22
    refine key _ (Or.inl rfl) ?_
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.Fi22 = 64561751654400
    exact CFSG.Sporadic.Fi22.card_Fi22
  · obtain ⟨e⟩ := h23
    refine key _ (Or.inr (Or.inl rfl)) ?_
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.Fi23 = 4089470473293004800
    exact CFSG.Sporadic.Fi23.card_Fi23
  · obtain ⟨e⟩ := h24
    refine key _ (Or.inr (Or.inr rfl)) ?_
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime = 1255205709190661721292800
    exact CFSG.Sporadic.Fi24.card_Fi24prime

private theorem w183_factorial_ne_336 {n : ℕ} (hn : 5 ≤ n) (h : n.factorial = 336) : False := by
  rcases le_or_gt n 6 with h6 | h7
  · interval_cases n <;> norm_num at h
  · have h5040 : 5040 ≤ n.factorial := by
      have h7' : 7 ≤ n := by omega
      have hle := Nat.factorial_le h7'
      norm_num at hle
      exact hle
    omega

theorem w183_not_oddTranspFactor_PSL_3_2_1
    (hO : LieOrderFormulasInput)
    {T : Type} [Group T] (h : LieModel T .PSL 3 2 1) : ¬ OddTranspFactor T := by
  intro hF
  have hv2 : (Nat.card T).factorization 2 = 3 := by
    obtain ⟨-, -, hf⟩ := hO T .PSL 3 2 1 h.admissible h
    rw [hf]
    simp [lieSylowExponent]
  rcases hF with ⟨n, hn, ⟨e⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq, hf, h3⟩ | h4
  · have hnf : n.factorial = 336 := by
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h1 : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hc : Nat.card T = 168 := w183_card_PSL_3_2_1 hO h
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2 : n.factorial / 2 * 2 = n.factorial := Nat.div_mul_cancel hdvd
      omega
    exact w183_factorial_ne_336 hn hnf
  · rcases h2 with ht | ht | ht | ht | ht | ht | ht
    · have h3 : 3 = n ^ 2 * f := by
        have := (hO T .PSp n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn2 : 2 ≤ n := ht.admissible.2.2.1
      have hf1 : 1 ≤ f := ht.admissible.2.1
      nlinarith [sq_nonneg (n : ℤ)]
    · have h3 : 3 = n * (n - 1) / 2 * f := by
        have := (hO T .PSU n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn3 : 3 ≤ n := ht.admissible.2.2.1
      have hf1 : 1 ≤ f := ht.admissible.2.1
      rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | hn4
      · norm_num at h3
        have hf1' : f = 1 := by omega
        have hadm := ht.admissible.2.2.2
        rw [hf1'] at hadm
        exact absurd rfl hadm
      · have h6 : 6 ≤ n * (n - 1) / 2 := by
          have h12 : 12 ≤ n * (n - 1) := by
            have h1 : 3 ≤ n - 1 := by omega
            calc 12 = 4 * 3 := by norm_num
              _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 h1
          omega
        nlinarith
    · have h3 : 3 = n * (n - 1) * f := by
        have := (hO T .POmegaPlus n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn4 : 4 ≤ n := ht.admissible.2.2
      have hf1 : 1 ≤ f := ht.admissible.2.1
      have h12 : 12 ≤ n * (n - 1) := by
        have h1 : 3 ≤ n - 1 := by omega
        calc 12 = 4 * 3 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 h1
      have h12f : 12 ≤ n * (n - 1) * f := by
        calc 12 ≤ n * (n - 1) := h12
          _ = n * (n - 1) * 1 := by ring
          _ ≤ n * (n - 1) * f := Nat.mul_le_mul_left _ hf1
      omega
    · have h3 : 3 = n * (n - 1) * f := by
        have := (hO T .POmegaMinus n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn4 : 4 ≤ n := ht.admissible.2.2
      have hf1 : 1 ≤ f := ht.admissible.2.1
      have h12 : 12 ≤ n * (n - 1) := by
        have h1 : 3 ≤ n - 1 := by omega
        calc 12 = 4 * 3 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 h1
      have h12f : 12 ≤ n * (n - 1) * f := by
        calc 12 ≤ n * (n - 1) := h12
          _ = n * (n - 1) * 1 := by ring
          _ ≤ n * (n - 1) * f := Nat.mul_le_mul_left _ hf1
      omega
    · have hf3 : f = 3 := by
        have := (hO T .PSL 2 2 f ht.admissible ht).2.2
        rw [hv2] at this
        have h1 : 3 = f := by simpa [lieSylowExponent] using this
        omega
      have hcard' : Nat.card T = 504 := by
        obtain ⟨-, hM, -⟩ := hO T .PSL 2 2 f ht.admissible ht
        rw [hf3] at hM
        have hd : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
        rw [hd, mul_one] at hM
        rw [hM]
        simp [lieOrderNumerator]
      have hc : Nat.card T = 168 := w183_card_PSL_3_2_1 hO h
      omega
    · have h3 : 3 = 6 * f := by
        have := (hO T .PSL 4 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hf1 : 1 ≤ f := ht.admissible.2.1
      omega
    · have h3 : 3 = 2 * f := by
        have := (hO T .twistedB2 0 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hf1 : 1 ≤ f := ht.admissible.2.1
      omega
  · have hM := (hO T .PSL 3 2 1 h.admissible h).2.1
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .PSL 2 q f ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, -, -, h7⟩ | ⟨hpsu, -⟩
      · omega
      · rcases hq with rfl | rfl <;> interval_cases f <;> omega
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .PSp 2 q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨hpsu, -⟩
      · omega
      · exact absurd ht' (by decide)
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .PSL 4 q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, -, hn2, -⟩ | ⟨hpsu, -⟩
      · omega
      · omega
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .PSU 4 q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨hpsu, -⟩
      · omega
      · exact absurd ht' (by decide)
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .POmegaOdd n q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨hpsu, -⟩
      · omega
      · exact absurd ht' (by decide)
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .POmegaPlus n q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨hpsu, -⟩
      · omega
      · exact absurd ht' (by decide)
      · exact absurd hpsu (by decide)
    · have hp2 : q ≠ 2 := by omega
      have hM' := (hO T .POmegaMinus n q 1 ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨hpsu, -⟩
      · omega
      · exact absurd ht' (by decide)
      · exact absurd hpsu (by decide)
  · exact w183_not_isSporadic_fischer hO (Or.inl (Or.inr (Or.inr (Or.inl h)))) h4

theorem w183_not_psl34_equiv_alt8 {T : Type} [Group T]
    (h : LieModel T .PSL 3 2 2) : ¬ Nonempty (T ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  have hX : CFSG.Open.StatedClassicalModel T .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, -, hE⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated T hX
  exact (hE (Fin 8) (by simp)).false e

private theorem w183_factorial_eq_40320 {n : ℕ} (hn : 5 ≤ n) (h : n.factorial = 40320) : n = 8 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hle : n.factorial ≤ 5040 := by
      have := Nat.factorial_le (show n ≤ 7 by omega)
      norm_num at this
      exact this
    omega
  · have hle : 362880 ≤ n.factorial := by
      have := Nat.factorial_le (show 9 ≤ n by omega)
      norm_num at this
      exact this
    omega

theorem w183_not_oddTranspFactor_PSL_3_2_2
    (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : LieModel T .PSL 3 2 2) : ¬ OddTranspFactor T := by
  intro hF
  have hv2 : (Nat.card T).factorization 2 = 6 := by
    obtain ⟨-, -, hf⟩ := hO T .PSL 3 2 2 h.admissible h
    rw [hf]
    simp [lieSylowExponent]
  have hcard : Nat.card T = 20160 := w183_card_PSL_3_2_2 hO h
  rcases hF with ⟨n, hn, ⟨e⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq, hf, h3⟩ | h4
  · have hn8 : n = 8 := by
      refine w183_factorial_eq_40320 hn ?_
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h1 : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2 : n.factorial / 2 * 2 = n.factorial := Nat.div_mul_cancel hdvd
      omega
    subst hn8
    exact w183_not_psl34_equiv_alt8 h ⟨e⟩
  · rcases h2 with ht | ht | ht | ht | ht | ht | ht
    · have h3 : 6 = n ^ 2 * f := by
        have := (hO T .PSp n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn2 : 2 ≤ n := ht.admissible.2.2.1
      have hf1 : 1 ≤ f := ht.admissible.2.1
      rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
      · norm_num at h3
        omega
      · have h9 : 9 ≤ n ^ 2 := by nlinarith
        nlinarith
    · have h3 : 6 = n * (n - 1) / 2 * f := by
        have := (hO T .PSU n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn3 : 3 ≤ n := ht.admissible.2.2.1
      have hf1 : 1 ≤ f := ht.admissible.2.1
      rcases (by omega : n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | hn5
      · have hf2 : f = 2 := by omega
        rw [hf2] at ht
        have hc := w183_card_PSU_3_2_2 hO ht
        omega
      · have hf1' : f = 1 := by omega
        rw [hf1'] at ht
        have hc : Nat.card T = 25920 := by
          obtain ⟨-, hM, -⟩ := hO T .PSU 4 2 1 ht.admissible ht
          have hd : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
          rw [hd, mul_one] at hM
          rw [hM]
          have h2 : Even (2 : ℕ) := by decide
          have h3' : ¬ Even (3 : ℕ) := by decide
          have h4 : Even (4 : ℕ) := by decide
          simp [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide, h2, h3', h4]
        omega
      · have h10 : 10 ≤ n * (n - 1) / 2 := by
          have h20 : 20 ≤ n * (n - 1) := by
            have h1 : 4 ≤ n - 1 := by omega
            calc 20 = 5 * 4 := by norm_num
              _ ≤ n * (n - 1) := Nat.mul_le_mul hn5 h1
          omega
        nlinarith
    · have h3 : 6 = n * (n - 1) * f := by
        have := (hO T .POmegaPlus n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn4 : 4 ≤ n := ht.admissible.2.2
      have hf1 : 1 ≤ f := ht.admissible.2.1
      have h12 : 12 ≤ n * (n - 1) := by
        have h1 : 3 ≤ n - 1 := by omega
        calc 12 = 4 * 3 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 h1
      have h12f : 12 ≤ n * (n - 1) * f := by
        calc 12 ≤ n * (n - 1) := h12
          _ = n * (n - 1) * 1 := by ring
          _ ≤ n * (n - 1) * f := Nat.mul_le_mul_left _ hf1
      omega
    · have h3 : 6 = n * (n - 1) * f := by
        have := (hO T .POmegaMinus n 2 f ht.admissible ht).2.2
        rw [hv2] at this
        simpa [lieSylowExponent] using this
      have hn4 : 4 ≤ n := ht.admissible.2.2
      have hf1 : 1 ≤ f := ht.admissible.2.1
      have h12 : 12 ≤ n * (n - 1) := by
        have h1 : 3 ≤ n - 1 := by omega
        calc 12 = 4 * 3 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 h1
      have h12f : 12 ≤ n * (n - 1) * f := by
        calc 12 ≤ n * (n - 1) := h12
          _ = n * (n - 1) * 1 := by ring
          _ ≤ n * (n - 1) * f := Nat.mul_le_mul_left _ hf1
      omega
    · have hf6 : f = 6 := by
        have := (hO T .PSL 2 2 f ht.admissible ht).2.2
        rw [hv2] at this
        have h1 : 6 = f := by simpa [lieSylowExponent] using this
        omega
      rw [hf6] at ht
      have hc : Nat.card T = 262080 := by
        obtain ⟨-, hM, -⟩ := hO T .PSL 2 2 6 ht.admissible ht
        have hd : lieOrderDivisor .PSL 2 (2 ^ 6) = 1 := by decide
        rw [hd, mul_one] at hM
        rw [hM]
        simp [lieOrderNumerator]
      omega
    · have hf1 : f = 1 := by
        have := (hO T .PSL 4 2 f ht.admissible ht).2.2
        rw [hv2] at this
        have h1 : 6 = 6 * f := by simpa [lieSylowExponent] using this
        omega
      rw [hf1] at ht
      exact w183_not_psl34_equiv_alt8 h
        ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff T).mp ht)
    · have hf3 : f = 3 := by
        have := (hO T .twistedB2 0 2 f ht.admissible ht).2.2
        rw [hv2] at this
        have h1 : 6 = 2 * f := by simpa [lieSylowExponent] using this
        omega
      rw [hf3] at ht
      have hc : Nat.card T = 29120 := by
        obtain ⟨-, hM, -⟩ := hO T .twistedB2 0 2 3 ht.admissible ht
        simp only [lieOrderDivisor, mul_one] at hM
        rw [hM]
        simp [lieOrderNumerator]
      omega
  · have hM := (hO T .PSL 3 2 2 h.admissible h).2.1
    have key : ∀ (tag : StatedLieTag) (m k : ℕ), LieModel T tag m q k → False := by
      intro tag m k ht
      have hp2 : q ≠ 2 := by omega
      have hM' := (hO T tag m q k ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith h.admissible ht.admissible hp2 hM hM'
        with ⟨-, h12, -, -, -, -⟩ | ⟨-, -, hf1, -, -, -⟩ | ⟨hpsu, -⟩
      · omega
      · omega
      · exact absurd hpsu (by decide)
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    all_goals exact key _ _ _ ht
  · exact w183_not_isSporadic_fischer hO (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) h4

theorem w183_not_oddTranspFactor_IsL2
    (hO : LieOrderFormulasInput)
    (hA : ArtinDistinctOddOrders) {T : Type} [Group T] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 9 < p ^ e) (h25 : p ^ e ≠ 25) (h : CFSG.Quasithin.F6.IsL2 p e T) :
    ¬ OddTranspFactor T := by
  have hmodel : LieModel T .PSL 2 p e := Or.inl ⟨by decide, h⟩
  have hadm_l := hmodel.admissible
  have hfin : Finite T := (hO T .PSL 2 p e hadm_l hmodel).1
  haveI : Finite T := hfin
  have hsimp : IsSimpleGroup T := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hMl := (hO T .PSL 2 p e hadm_l hmodel).2.1
  have hfl : (Nat.card T).factorization p = e := by
    simpa [lieSylowExponent] using (hO T .PSL 2 p e hadm_l hmodel).2.2
  have hshapeT : (∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨
      LieModel T .PSL 3 p 1 ∨ LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1 :=
    Or.inl ⟨e, hq, h⟩
  intro hF
  rcases hF with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq35, hf, h3⟩ | h4
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with h5 | h6 | h7 | h8 | h9
    · have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
      have h2M := CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd
        (q' := p ^ e) (by omega) hodd hMl
      have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2card : 2 * Nat.card T = n.factorial := by
        rw [hcard, mul_comm]
        exact Nat.div_mul_cancel hdvd
      refine w183_alt_factorial_ne_psl2 hp hp2 hq (Or.inl h5) ?_
      rw [← h2card]
      exact h2M.symm
    · have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
      have h2M := CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd
        (q' := p ^ e) (by omega) hodd hMl
      have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2card : 2 * Nat.card T = n.factorial := by
        rw [hcard, mul_comm]
        exact Nat.div_mul_cancel hdvd
      refine w183_alt_factorial_ne_psl2 hp hp2 hq (Or.inr (Or.inl h6)) ?_
      rw [← h2card]
      exact h2M.symm
    · exact w183_alt_seven_nine_false hO hp hp2 hmodel (Or.inl h7) e'
    · have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
      have h2M := CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd
        (q' := p ^ e) (by omega) hodd hMl
      have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2card : 2 * Nat.card T = n.factorial := by
        rw [hcard, mul_comm]
        exact Nat.div_mul_cancel hdvd
      refine w183_alt_factorial_ne_psl2 hp hp2 hq (Or.inr (Or.inr h8)) ?_
      rw [← h2card]
      exact h2M.symm
    · exact w183_alt_seven_nine_false hO hp hp2 hmodel (Or.inr h9) e'
  · have key : ∀ (tag : StatedLieTag) (m : ℕ), LieModel T tag m 2 f → False := by
      intro tag m ht
      have hMc := (hO T tag m 2 f ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith ht.admissible hadm_l hp2 hMc hMl with
        ⟨-, -, -, ht', -, h5⟩ | ⟨-, -, -, ht', -, h7⟩ | ⟨-, -, -, ht', -, -⟩
      · exact absurd h5 (by omega)
      · exact absurd h7 (by omega)
      · exact absurd ht' (by decide)
    rcases h2 with ht | ht | ht | ht | ht | ht | ht
    all_goals exact key _ _ ht
  · have diffChar : ∀ (tag : StatedLieTag) (m g : ℕ), LieModel T tag m q g → p ≠ q →
        ((∃ f : ℕ, f ≤ 2 ∧ LieModel T .PSL 2 q f) ∨ LieModel T .PSp 2 q 1 ∨
          LieModel T .PSL 4 q 1 ∨ LieModel T .PSU 4 q 1 ∨
          (∃ n : ℕ, LieModel T .POmegaOdd n q 1 ∨ LieModel T .POmegaPlus n q 1 ∨
            LieModel T .POmegaMinus n q 1)) → False := by
      intro tag m g ht hpq hshapeT'
      exact (hA T T hsimp hsimp p q hp
        (hq35.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)) hp2 hpq hq35
        hshapeT hshapeT') rfl
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = f := by
          simpa [lieSylowExponent] using (hO T .PSL 2 p f ht.admissible ht).2.2
        have hef : e = f := by omega
        have hf1 : 1 ≤ f := ht.admissible.2.1
        rw [hef] at hq h25
        rcases hp35 with rfl | rfl <;> interval_cases f <;>
          first | (norm_num at hq; done) | norm_num at h25
      · exact diffChar _ _ _ ht hpq (Or.inl ⟨f, hf, ht⟩)
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = 4 := by
          simpa [lieSylowExponent] using (hO T .PSp 2 p 1 ht.admissible ht).2.2
        have he4 : e = 4 := by omega
        exact w183_psl2_psp2_ne hp35 he4 hMl (hO T .PSp 2 p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inl ht))
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSL 4 p 1 ht.admissible ht).2.2
        have he6 : e = 6 := by omega
        exact w183_psl2_psl4_ne hp35 he6 hMl (hO T .PSL 4 p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inl ht)))
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSU 4 p 1 ht.admissible ht).2.2
        have he6 : e = 6 := by omega
        exact w183_psl2_psu4_ne hp35 he6 hMl (hO T .PSU 4 p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inl ht))))
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = n ^ 2 := by
          simpa [lieSylowExponent] using (hO T .POmegaOdd n p 1 ht.admissible ht).2.2
        have hen : e = n ^ 2 := by omega
        have hn3 : 3 ≤ n := ht.admissible.2.2.1
        exact w183_psl2_pomegaOdd_ne hp hp2 hn3 hen hMl
          (hO T .POmegaOdd n p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inl ht⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaPlus n p 1 ht.admissible ht).2.2
        have hen : e = n * (n - 1) := by omega
        have hn4 : 4 ≤ n := ht.admissible.2.2
        exact w183_psl2_pomegaPlus_ne hp hp2 hn4 hen hMl
          (hO T .POmegaPlus n p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inl ht)⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hp35 : p = 3 ∨ p = 5 := hq35
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaMinus n p 1 ht.admissible ht).2.2
        have hen : e = n * (n - 1) := by omega
        have hn4 : 4 ≤ n := ht.admissible.2.2
        exact w183_psl2_pomegaMinus_ne hp hp2 hn4 hen hMl
          (hO T .POmegaMinus n p 1 ht.admissible ht).2.1
      · exact diffChar _ _ _ ht hpq
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inr ht)⟩))))
  · exact absurd h4 (w183_not_isSporadic_fischer hO
      (Or.inr ⟨.PSL, 2, p, e, hp, hp2, hmodel⟩))


theorem w183_not_oddTranspFactor_PSL_3_p_1
    (hO : LieOrderFormulasInput)
    (hA : ArtinDistinctOddOrders) {T : Type} [Group T] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : LieModel T .PSL 3 p 1) : ¬ OddTranspFactor T := by
  have hfin : Finite T := (hO T .PSL 3 p 1 h.admissible h).1
  haveI : Finite T := hfin
  have hsimp : IsSimpleGroup T :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hMl := (hO T .PSL 3 p 1 h.admissible h).2.1
  have hfl : (Nat.card T).factorization p = 3 := by
    simpa [lieSylowExponent] using (hO T .PSL 3 p 1 h.admissible h).2.2
  have hshapeT : (∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨
      LieModel T .PSL 3 p 1 ∨ LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1 :=
    Or.inr (Or.inl h)
  intro hF
  rcases hF with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq35, hf, h3⟩ | h4
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with h5 | h6 | h7 | h8 | h9
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inl h5) (Or.inl rfl) hfac
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inl h6)) (Or.inl rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inl h7) e'
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inr h8)) (Or.inl rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inr h9) e'
  · have key : ∀ (tag : StatedLieTag) (m : ℕ), LieModel T tag m 2 f → False := by
      intro tag m ht
      have hMc := (hO T tag m 2 f ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith ht.admissible h.admissible hp2 hMc
        hMl with
        ⟨-, -, -, ht', hn', -⟩ | ⟨-, -, -, ht', hn', -⟩ | ⟨-, -, -, ht', -, -⟩
      · exact absurd hn' (by omega)
      · exact absurd hn' (by omega)
      · exact absurd ht' (by decide)
    rcases h2 with ht | ht | ht | ht | ht | ht | ht
    all_goals exact key _ _ ht
  · have diffChar : ∀ (tag : StatedLieTag) (m g : ℕ), LieModel T tag m q g → p ≠ q →
        ((∃ f : ℕ, f ≤ 2 ∧ LieModel T .PSL 2 q f) ∨ LieModel T .PSp 2 q 1 ∨
          LieModel T .PSL 4 q 1 ∨ LieModel T .PSU 4 q 1 ∨
          (∃ n : ℕ, LieModel T .POmegaOdd n q 1 ∨ LieModel T .POmegaPlus n q 1 ∨
            LieModel T .POmegaMinus n q 1)) → False := by
      intro tag m g ht hpq hshapeT'
      exact (hA T T hsimp hsimp p q hp
        (hq35.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)) hp2 hpq hq35
        hshapeT hshapeT') rfl
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = f := by
          simpa [lieSylowExponent] using (hO T .PSL 2 p f ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inl ⟨f, hf, ht⟩)
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 4 := by
          simpa [lieSylowExponent] using (hO T .PSp 2 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inl ht))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSL 4 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inl ht)))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSU 4 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inl ht))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n ^ 2 := by
          simpa [lieSylowExponent] using (hO T .POmegaOdd n p 1 ht.admissible ht).2.2
        exact w183_three_ne_sq (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inl ht⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaPlus n p 1 ht.admissible ht).2.2
        exact w183_three_ne_rect (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inl ht)⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaMinus n p 1 ht.admissible ht).2.2
        exact w183_three_ne_rect (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inr ht)⟩))))
  · exact absurd h4 (w183_not_isSporadic_fischer hO
      (Or.inr ⟨.PSL, 3, p, 1, hp, hp2, h⟩))

theorem w183_not_oddTranspFactor_PSU_3_p_1
    (hO : LieOrderFormulasInput)
    (hA : ArtinDistinctOddOrders) {T : Type} [Group T] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : LieModel T .PSU 3 p 1) : ¬ OddTranspFactor T := by
  have hfin : Finite T := (hO T .PSU 3 p 1 h.admissible h).1
  haveI : Finite T := hfin
  have hsimp : IsSimpleGroup T :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hMl := (hO T .PSU 3 p 1 h.admissible h).2.1
  have hfl : (Nat.card T).factorization p = 3 := by
    simpa [lieSylowExponent] using (hO T .PSU 3 p 1 h.admissible h).2.2
  have hshapeT : (∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨
      LieModel T .PSL 3 p 1 ∨ LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1 :=
    Or.inr (Or.inr (Or.inl h))
  intro hF
  rcases hF with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq35, hf, h3⟩ | h4
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with h5 | h6 | h7 | h8 | h9
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inl h5) (Or.inl rfl) hfac
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inl h6)) (Or.inl rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inl h7) e'
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 3 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inr h8)) (Or.inl rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inr h9) e'
  · have key : ∀ (tag : StatedLieTag) (m : ℕ), LieModel T tag m 2 f → False := by
      intro tag m ht
      have hMc := (hO T tag m 2 f ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith ht.admissible h.admissible hp2 hMc
        hMl with
        ⟨-, -, -, ht', -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨-, -, -, ht', -, -⟩
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    rcases h2 with ht | ht | ht | ht | ht | ht | ht
    all_goals exact key _ _ ht
  · have diffChar : ∀ (tag : StatedLieTag) (m g : ℕ), LieModel T tag m q g → p ≠ q →
        ((∃ f : ℕ, f ≤ 2 ∧ LieModel T .PSL 2 q f) ∨ LieModel T .PSp 2 q 1 ∨
          LieModel T .PSL 4 q 1 ∨ LieModel T .PSU 4 q 1 ∨
          (∃ n : ℕ, LieModel T .POmegaOdd n q 1 ∨ LieModel T .POmegaPlus n q 1 ∨
            LieModel T .POmegaMinus n q 1)) → False := by
      intro tag m g ht hpq hshapeT'
      exact (hA T T hsimp hsimp p q hp
        (hq35.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)) hp2 hpq hq35
        hshapeT hshapeT') rfl
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = f := by
          simpa [lieSylowExponent] using (hO T .PSL 2 p f ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inl ⟨f, hf, ht⟩)
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 4 := by
          simpa [lieSylowExponent] using (hO T .PSp 2 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inl ht))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSL 4 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inl ht)))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = 6 := by
          simpa [lieSylowExponent] using (hO T .PSU 4 p 1 ht.admissible ht).2.2
        omega
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inl ht))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n ^ 2 := by
          simpa [lieSylowExponent] using (hO T .POmegaOdd n p 1 ht.admissible ht).2.2
        exact w183_three_ne_sq (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inl ht⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaPlus n p 1 ht.admissible ht).2.2
        exact w183_three_ne_rect (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inl ht)⟩))))
    · by_cases hpq : p = q
      · subst hpq
        have hfc : (Nat.card T).factorization p = n * (n - 1) := by
          simpa [lieSylowExponent] using (hO T .POmegaMinus n p 1 ht.admissible ht).2.2
        exact w183_three_ne_rect (by rw [← hfc]; exact hfl)
      · exact diffChar _ _ _ ht hpq
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inr ht)⟩))))
  · exact absurd h4 (w183_not_isSporadic_fischer hO
      (Or.inr ⟨.PSU, 3, p, 1, hp, hp2, h⟩))

theorem w183_not_oddTranspFactor_PSp_2_p_1
    (hO : LieOrderFormulasInput)
    (hA : ArtinDistinctOddOrders) {T : Type} [Group T] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp7 : 7 ≤ p) (h : LieModel T .PSp 2 p 1) : ¬ OddTranspFactor T := by
  have hfin : Finite T := (hO T .PSp 2 p 1 h.admissible h).1
  haveI : Finite T := hfin
  have hsimp : IsSimpleGroup T :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hMl := (hO T .PSp 2 p 1 h.admissible h).2.1
  have hfl : (Nat.card T).factorization p = 4 := by
    simpa [lieSylowExponent] using (hO T .PSp 2 p 1 h.admissible h).2.2
  have hshapeT : (∃ e : ℕ, 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e T) ∨
      LieModel T .PSL 3 p 1 ∨ LieModel T .PSU 3 p 1 ∨ LieModel T .PSp 2 p 1 :=
    Or.inr (Or.inr (Or.inr h))
  intro hF
  rcases hF with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, f, h2⟩ | ⟨q, n, f, hq35, hf, h3⟩ | h4
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n) with h5 | h6 | h7 | h8 | h9
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 4 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inl h5) (Or.inr rfl) hfac
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 4 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inl h6)) (Or.inr rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inl h7) e'
    · have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have hfac : (n.factorial / 2).factorization p = 4 := by rw [← hcard]; exact hfl
      exact w183_factorial_factorization hp hp2 (Or.inr (Or.inr h8)) (Or.inr rfl) hfac
    · exact w183_alt_seven_nine_false hO hp hp2 h (Or.inr h9) e'
  · have key : ∀ (tag : StatedLieTag) (m : ℕ), LieModel T tag m 2 f → False := by
      intro tag m ht
      have hMc := (hO T tag m 2 f ht.admissible ht).2.1
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith ht.admissible h.admissible hp2 hMc
        hMl with
        ⟨-, -, -, ht', -, -⟩ | ⟨-, -, -, ht', -, -⟩ | ⟨-, -, -, ht', -, h3'⟩
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
      · have hp3 : p = 3 := by simpa using h3'
        omega
    rcases h2 with ht | ht | ht | ht | ht | ht | ht
    all_goals exact key _ _ ht
  · have hqprime : q.Prime := hq35.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)
    have hpq : p ≠ q := by rintro rfl; rcases hq35 with h | h <;> omega
    have diffChar : ∀ (tag : StatedLieTag) (m g : ℕ), LieModel T tag m q g → p ≠ q →
        ((∃ f : ℕ, f ≤ 2 ∧ LieModel T .PSL 2 q f) ∨ LieModel T .PSp 2 q 1 ∨
          LieModel T .PSL 4 q 1 ∨ LieModel T .PSU 4 q 1 ∨
          (∃ n : ℕ, LieModel T .POmegaOdd n q 1 ∨ LieModel T .POmegaPlus n q 1 ∨
            LieModel T .POmegaMinus n q 1)) → False := by
      intro tag m g ht hpq hshapeT'
      exact (hA T T hsimp hsimp p q hp hqprime hp2 hpq hq35 hshapeT hshapeT') rfl
    rcases h3 with ht | ht | ht | ht | ht | ht | ht
    · exact diffChar _ _ _ ht hpq (Or.inl ⟨f, hf, ht⟩)
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inl ht))
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inl ht)))
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inl ht))))
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inl ht⟩))))
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inl ht)⟩))))
    · exact diffChar _ _ _ ht hpq (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (Or.inr ht)⟩))))
  · exact absurd h4 (w183_not_isSporadic_fischer hO
      (Or.inr ⟨.PSp, 2, p, 1, hp, hp2, h⟩))

theorem tail1812TwoNoSectionCF_of_lieOrderFormulas
    (hO : LieOrderFormulasInput) (hA : ArtinDistinctOddOrders) : Tail1812TwoNoSectionCF := by
  intro T _ _ hS hF
  rcases hS with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact absurd hF (w183_not_oddTranspFactor_PSL_3_2_1 hO h3)
  · exact absurd hF (w183_not_oddTranspFactor_PSL_3_2_2 hO h4)
  · exact Or.inr (Or.inr (Or.inl h5))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h6)))
  · rcases h7 with ⟨p, e, hp, hp2, hq, hL⟩
    by_cases h25 : p ^ e = 25
    · have hp5 : p = 5 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact absurd h2 hp2
        · have he0 : e ≠ 0 := by rintro rfl; simp at hq
          have hdvd : p ∣ 25 := h25 ▸ dvd_pow_self p he0
          have hdvd5 : p ∣ 5 := by
            rw [show (25 : ℕ) = 5 ^ 2 by norm_num] at hdvd
            exact hp.dvd_of_dvd_pow hdvd
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hdvd5
      subst hp5
      have he2 : e = 2 := by
        have h55 : 5 ^ e = 5 ^ 2 := h25.trans (by norm_num)
        exact Nat.pow_right_injective (by norm_num) h55
      subst he2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))
    · exact absurd hF (w183_not_oddTranspFactor_IsL2 hO hA hp hp2 hq h25 hL)
  · rcases h8 with ⟨p, hp, hp2, h8⟩
    rcases h8 with ⟨-, hL⟩ | ⟨-, hL⟩
    · exact absurd hF (w183_not_oddTranspFactor_PSL_3_p_1 hO hA hp hp2 hL)
    · exact absurd hF (w183_not_oddTranspFactor_PSU_3_p_1 hO hA hp hp2 hL)
  · rcases h9 with ⟨p, hp, hp2, hL⟩
    have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact absurd h2 hp2
      · have h2le : 2 ≤ p := hp.two_le
        omega
    have hpd : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
      by_cases h3 : p = 3
      · exact Or.inl h3
      by_cases h5 : p = 5
      · exact Or.inr (Or.inl h5)
      refine Or.inr (Or.inr ?_)
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      have h6 : p ≠ 6 := by rintro rfl; norm_num at hp
      omega
    rcases hpd with rfl | rfl | hp7
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))
    · exact absurd hF (w183_not_oddTranspFactor_PSp_2_p_1 hO hA hp hp2 hp7 hL)

end CFSG.LocalAnalysis.WeakClosure81

end
