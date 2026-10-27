module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FRational
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Counting

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem card_le_three_mul_card_inf_psu (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ (psuConj h).range : Subgroup _) := by
  have := h.finite
  set N := (psuConj h).range with hNdef
  set C := (psuField h).range with hCdef
  have hcycK := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psuField h).rangeRestrict (psuField h).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact SetLike.mem_coe.mpr (Sec19.seitzU1_psuField_conj_mem σ (SetLike.mem_coe.mp hx))
    · intro hx
      have h2 := Sec19.seitzU1_psuField_conj_mem σ⁻¹ (SetLike.mem_coe.mp hx)
      rw [map_inv] at h2
      have e : (psuField h σ)⁻¹ * (psuField h σ * x * (psuField h σ)⁻¹) *
          ((psuField h σ)⁻¹)⁻¹ = x := by group
      rw [e] at h2
      exact SetLike.mem_coe.mpr h2
  have hBNC : ∀ b ∈ E, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  exact Sec4.card_le_three_mul_card_inf hE hcyc hCN hBNC

theorem card_inf_psuConj_range_eq_nine [Finite K] (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    Nat.card (E ⊓ (psuConj h).range : Subgroup _) = 9 := by
  have h1 := card_le_three_mul_card_inf_psu hq hE
  have h2 : Nat.card (E ⊓ (psuConj h).range : Subgroup _) ≤ 9 :=
    Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 _
      (CFSG.Open.IsElemAbelian.mono hE inf_le_left) inf_le_right
  omega

theorem not_le_psuConj_range_of_card [Finite K] (h3 : (3 : K) ≠ 0)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E) (hc : 9 < Nat.card E) :
    ¬ E ≤ (psuConj h).range := by
  intro hle
  have := Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 E hE hle
  omega

end Counting

section Claim4

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem glAut_eq_map (σ : K ≃+* K) (g : GL (Fin 3) K) :
    glAut σ g = GeneralLinearGroup.map (σ : K →+* K) g :=
  Units.ext rfl

theorem exists_rational_rep_psu [Finite K] (hq : 2 < p ^ f) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x) {M : unitaryIsom3 h}
    (hcomm : psuConj h M * psuField h σ = psuField h σ * psuConj h M) :
    ∃ (u : Kˣ) (g' : GL (Fin 3) K),
      (M : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) u * g' ∧
      ∀ i j, (g' : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
  have h1 : psuConj h ⟨glAut σ M, glAut_mem_unitaryIsom3 σ M.2⟩ = psuConj h M := by
    rw [← psuField_mul_psuConj_mul_inv, ← hcomm, mul_inv_cancel_right]
  have h2 : psuConj h (M⁻¹ * ⟨glAut σ M, glAut_mem_unitaryIsom3 σ M.2⟩) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := Sec19.Item19Res6Proof.exists_scalar_of_psuConj_eq_one h2
  have h4 : (M : GL (Fin 3) K)⁻¹ * glAut σ M = GeneralLinearGroup.scalar (Fin 3) c := hc
  refine exists_rational_rep_of_map hσ hk (g₁ := (M : GL (Fin 3) K)) (c := c) ?_
  rw [← glAut_eq_map]
  calc glAut σ M = (M : GL (Fin 3) K) * ((M : GL (Fin 3) K)⁻¹ * glAut σ M) := by group
    _ = (M : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by rw [h4]

end Claim4

end CFSG.RankThree.PartTwo.Sec4.E27
