module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelCore

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

private theorem ggOmW6b_field_card {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨(n : ℕ), PNat.one_le n, by rw [Nat.card_eq_fintype_card, hn]⟩

private theorem ggOmW6b_outTwoPartLeTwo_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) :
    GGOutTwoPartLeTwo (matrixDerived (Qm n hn4 b c)) := by
  have hf : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  refine ggGraphInv_outTwoPartLeTwo_of_mul
    (Subgroup.zpowers (AutOm.frobAut hn4 hirr)) ?_ ?_
  · intro α
    obtain ⟨ι, hι, k, hk⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf α
    exact ⟨ι, by simpa only [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hι,
      AutOm.frobAut hn4 hirr ^ k, Subgroup.npow_mem_zpowers _ k, hk⟩
  · rw [Nat.card_zpowers]
    have h2 : (AutOm.frobAut hn4 hirr) ^ 2 = 1 := by
      have h := AutOm.frobAut_pow_two_mul hn4 hirr hf
      simpa using h
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)

private noncomputable abbrev ggOmW6bA_inner (Γ : Type) [Group Γ] : Subgroup (MulAut Γ) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner Γ

private theorem ggOmW6b_normal_form {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (α : MulAut (matrixDerived (Qm n hn4 b c))) (hα2 : α * α = 1)
    (hout : ∀ c' : matrixDerived (Qm n hn4 b c), α ≠ MulAut.conj c') :
    ∃ x : matrixDerived (Qm n hn4 b c), α = MulAut.conj x * AutOm.tailRefl hn4 := by
  obtain ⟨ι, hι, k, hk⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf α
  have hιmem : ι ∈ inner (matrixDerived (Qm n hn4 b c)) := hι
  obtain ⟨c', hc'⟩ := hι
  rw [← hc'] at hιmem hk
  let τ : MulAut (matrixDerived (Qm n hn4 b c)) := AutOm.frobAut hn4 hirr
  have hk' : α = MulAut.conj c' * τ ^ k := hk
  have h2 : (MulAut.conj c' * τ ^ k) * (MulAut.conj c' * τ ^ k) = 1 := by
    rw [← hk']
    exact hα2
  have hpow : τ ^ (2 * k) = τ ^ k * τ ^ k := by rw [two_mul k, pow_add]
  have hprod : MulAut.conj c' * (τ ^ k * MulAut.conj c' * (τ ^ k)⁻¹) * τ ^ (2 * k) = 1 := by
    rw [hpow, ← h2]
    group
  have hA : MulAut.conj c' * (τ ^ k * MulAut.conj c' * (τ ^ k)⁻¹) ∈
      ggOmW6bA_inner (matrixDerived (Qm n hn4 b c)) :=
    (ggOmW6bA_inner _).mul_mem hιmem ((inner_normal _).conj_mem _ hιmem _)
  have hmem : τ ^ (2 * k) ∈ ggOmW6bA_inner (matrixDerived (Qm n hn4 b c)) := by
    have hinv : τ ^ (2 * k) =
        (MulAut.conj c' * (τ ^ k * MulAut.conj c' * (τ ^ k)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right hprod
    rw [hinv]
    exact (ggOmW6bA_inner _).inv_mem hA
  have hinf : (inner (matrixDerived (Qm n hn4 b c)) :
      Subgroup (MulAut (matrixDerived (Qm n hn4 b c)))) ⊓ Subgroup.zpowers τ = ⊥ :=
    AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1
  have h2k : τ ^ (2 * k) = 1 := by
    have hbot : τ ^ (2 * k) ∈ (⊥ : Subgroup (MulAut (matrixDerived (Qm n hn4 b c)))) := by
      rw [← hinf]
      exact ⟨hmem, Subgroup.npow_mem_zpowers τ (2 * k)⟩
    exact Subgroup.mem_bot.mp hbot
  have hsq : (τ ^ k) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm k 2]; exact h2k
  by_cases h1 : τ ^ k = 1
  · exfalso
    exact hout c' (by rw [hk', h1, mul_one])
  · refine ⟨c', ?_⟩
    have hτ : τ ^ k = AutOm.tailRefl hn4 :=
      AutOm.eq_tailRefl_of_mem_zpowers hn4 hirr hf hf1
        (Subgroup.npow_mem_zpowers τ k) hsq h1
    rw [hk', hτ]

private theorem ggOmW6b_reflMat_not_mem_statedOmega {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.RankThree.PartOne.AUTSL.reflMat (Qm n hn4 b c) (AutOm.tailVec n (by omega))
        (AutOm.tailVec_form_ne_zero n (by omega) b c) ∉ CFSG.Open.StatedOmega ⇑(Qm n hn4 b c) := by
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have h := reflMat_not_mem_derived (Q := Qm n hn4 b c) hnd hT
    (AutOm.tailVec n (by omega)) (AutOm.tailVec_form_ne_zero n (by omega) b c)
  rwa [matrixDerived_eq_statedOmega] at h

private theorem ggOmW6b_graph_clauses {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (b0 : matrixDerived (Qm n hn4 b c)) (hodd : Odd (orderOf b0))
    (α : MulAut (matrixDerived (Qm n hn4 b c))) (hα2 : α * α = 1) (hαb : α b0 = b0)
    (hfix : ∀ g ∈ Subgroup.centralizer ({b0} : Set (matrixDerived (Qm n hn4 b c))), α g = g)
    (x : matrixDerived (Qm n hn4 b c)) (hα : α = MulAut.conj x * AutOm.tailRefl hn4) :
    Nat.card K = 2 ∧ GGGraphInvFixClauses α := by
  have h8 : 8 ≤ 2 * n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hw : Qm n hn4 b c (AutOm.tailVec n (by omega)) ≠ 0 :=
    AutOm.tailVec_form_ne_zero n (by omega) b c
  have hRΩ : reflMat (Qm n hn4 b c) (AutOm.tailVec n (by omega)) hw ∉
      CFSG.Open.StatedOmega ⇑(Qm n hn4 b c) :=
    ggOmW6b_reflMat_not_mem_statedOmega hn4 hirr
  have hρ : AutOm.tailRefl hn4 =
      reflAut (Qm n hn4 b c) (AutOm.tailVec n (by omega)) hw := rfl
  obtain ⟨s, hsO, hsΩ, hs2, hconj⟩ :=
    ggGraphInv_graph_lift (Qm n hn4 b c) hnd h8 x (AutOm.tailVec n (by omega)) hw hRΩ α hα2
      (by rw [hα, hρ])
  have hbΩ : (b0 : GL (Fin (2 * n)) K) ∈ CFSG.Open.StatedOmega ⇑(Qm n hn4 b c) := by
    rw [← matrixDerived_eq_statedOmega]
    exact b0.2
  have hodd' : Odd (orderOf (b0 : GL (Fin (2 * n)) K)) := by
    rwa [Subgroup.orderOf_coe]
  have hsb : s * (b0 : GL (Fin (2 * n)) K) = (b0 : GL (Fin (2 * n)) K) * s :=
    ggGraphInv_conjBy_commute (Qm n hn4 b c) α s hconj b0 hαb
  have hsC : ∀ g ∈ Subgroup.centralizer ({(b0 : GL (Fin (2 * n)) K)} :
      Set (GL (Fin (2 * n)) K)) ⊓ CFSG.Open.StatedOmega ⇑(Qm n hn4 b c),
      s * g = g * s := by
    intro g hg
    have hgΩ : g ∈ matrixDerived (Qm n hn4 b c) := by
      rw [matrixDerived_eq_statedOmega]
      exact hg.2
    let g' : matrixDerived (Qm n hn4 b c) := ⟨g, hgΩ⟩
    have hg' : g' ∈ Subgroup.centralizer
        ({b0} : Set (matrixDerived (Qm n hn4 b c))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      first
        | simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg.1)
        | simpa using (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
    have hcomm := ggGraphInv_conjBy_commute (Qm n hn4 b c) α s hconj g' (hfix g' hg')
    simpa [g'] using hcomm
  exact ggGraphInv_three_conclusions_of_transvection (Qm n hn4 b c) hnd h8
    (b0 : GL (Fin (2 * n)) K) hbΩ hodd' α s hsO hsΩ hs2 hsb hsC hconj

theorem ggGraphInvInputModel_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGGraphInvInputModel (matrixDerived (Qm n hn4 b c)) := by
  intro p b0 α hp hp2 hb1 hbp hα2 hout hαb _hcomp hfix
  have hodd : Odd (orderOf b0) := ggGraphInv_odd_orderOf hp hp2 hb1 hbp
  obtain ⟨f, hf1, hf⟩ := ggOmW6b_field_card (K := K)
  obtain ⟨x, hx⟩ := ggOmW6b_normal_form hn4 hirr hf hf1 α hα2 hout
  obtain ⟨hK, hcl⟩ := ggOmW6b_graph_clauses hn4 hirr b0 hodd α hα2 hαb hfix x hx
  exact ⟨ggOmW6b_outTwoPartLeTwo_of_card_two hn4 hirr hK, hcl⟩

end CFSG.StandardType
