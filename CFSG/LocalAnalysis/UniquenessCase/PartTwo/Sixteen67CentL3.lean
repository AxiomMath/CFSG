module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentTransport
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3L
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReducePSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Subgroup
open CFSG.AGLEmbedding.LinearThreeKit
open CFSG.AGLEmbedding.ToralReduce
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isCyclic_and_card_centralizer_sl_three {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : ¬ 3 ∣ Nat.card K - 1) {u : Matrix.SpecialLinearGroup (Fin 3) K} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) :
    IsCyclic (centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) ∧
      Nat.card (centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) =
        Nat.card K ^ 2 - 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hq' : ¬ 3 ∣ Fintype.card K - 1 := by
    rwa [← Nat.card_eq_fintype_card]
  have hus : u ∉ scalars 3 K := by
    rw [scalars_eq_bot_of_not_dvd hq, Subgroup.mem_bot]
    exact hu1
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_smul_of_pow_three (coe_pow_eq_one hu3) u.prop
    (ne_smul_one_of_notMem_scalars hus) (one_pow 3)
  have hfl : IsFixedLine 3 u w :=
    isFixedLine_of_fixed (by decide : Odd 3) h3 hu3 hu1 hw0 (by simpa using hw)
  have hcyc : IsCyclic (centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) :=
    hfl.isCyclic_centralizer_of_not_dvd Nat.prime_three hq'
  have hns : ∀ r : K, ¬ (centPoly u).IsRoot r := by
    intro r hr
    exact hq' ((hfl.exists_isRoot_iff_dvd Nat.prime_three).mp ⟨r, hr⟩)
  haveI : Fact (Irreducible (centPoly u)) := ⟨IsFixedLine.irreducible_centPoly hns⟩
  have hne : centPoly u ≠ 0 := (quadPoly_monic _).ne_zero
  have hdim : Module.finrank K (AdjoinRoot (centPoly u)) = 2 :=
    (finrank_quotient_span_eq_natDegree (K := K) (f := centPoly u)).trans
      (quadPoly_natDegree _)
  haveI : Module.Finite K (AdjoinRoot (centPoly u)) := (AdjoinRoot.powerBasis hne).finite
  have hcard : Nat.card (centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) =
      Nat.card K ^ 2 - 1 := by
    rw [Nat.card_congr hfl.centralizerEquiv.toEquiv, Nat.card_units,
      Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot (centPoly u)), hdim]
  exact ⟨hcyc, hcard⟩

theorem isCyclic_and_card_centralizer_of_lieModel_psl {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hq : p ^ f % 3 = 2) (hL : CFSG.Blueprint.LieModel J .PSL 3 p f) {x : J} (hx : orderOf x = 3) :
    IsCyclic (centralizer ({x} : Set J)) ∧
      Nat.card (centralizer ({x} : Set J)) = (p ^ f) ^ 2 - 1 := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    have hq' : Nat.card K % 3 = 2 := by rw [hK]; exact hq
    have hq'' : ¬ 3 ∣ Nat.card K - 1 := by
      rintro ⟨k, hk⟩
      have hpos : 1 ≤ Nat.card K := le_of_lt Finite.one_lt_card
      have hmod : Nat.card K % 3 = 1 := by
        have : Nat.card K = 3 * k + 1 := by omega
        rw [this]; omega
      omega
    have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod hf hK hq'
    let e₁ : J ≃* PSL(3, K) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
    let e₂ : PSL(3, K) ≃* SL(3, K) :=
      (QuotientGroup.quotientMulEquivOfEq (center_SL3_eq_bot (cube_roots_trivial hq'))).trans
        QuotientGroup.quotientBot
    let e' : J ≃* SL(3, K) := e₁.trans e₂
    have hx3 : x ^ 3 = 1 := by simpa [hx] using pow_orderOf_eq_one x
    have hu3 : (e' x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hu1 : e' x ≠ 1 := by
      intro h1
      have hx1 : x = 1 := e'.injective (by rw [h1, map_one])
      rw [hx1, orderOf_one] at hx
      omega
    obtain ⟨hcycSL, hcardSL⟩ := isCyclic_and_card_centralizer_sl_three h3 hq'' hu3 hu1
    refine ⟨?_, ?_⟩
    · have h := isCyclic_centralizer_singleton_mulEquiv e'.symm (e' x) hcycSL
      have hsub : centralizer ({e'.symm (e' x)} : Set J) = centralizer ({x} : Set J) := by
        rw [MulEquiv.symm_apply_apply e' x]
      exact hsub ▸ h
    · have h := card_centralizer_singleton_mulEquiv e'.symm (e' x)
      simp only [MulEquiv.symm_apply_apply] at h
      rw [h, hcardSL, hK]
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
