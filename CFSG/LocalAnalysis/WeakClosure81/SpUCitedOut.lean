module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.RankThree.PartOne.OutStructure CFSG.Open

private theorem spUCited_zpow_eq_one_or_self {X : Type*} [Group X] {y : MulAut X}
    (hy : y ^ 2 = 1) (m : ℤ) : y ^ m = 1 ∨ y ^ m = y := by
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hy, one_zpow]
  · right
    rw [zpow_add, zpow_one, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hy,
      one_zpow, one_mul]

private theorem spUCited_outPNice_two_statedProj_ge_three {K : Type} [Field K] [Finite K]
    [CharP K 2] {r : ℕ} (hr : 3 ≤ r) : OutPNice 2 (StatedProj (StatedSp r K)) :=
  outPNice_StatedSp (p := 2) hr Nat.prime_two

private theorem spUCited_outPNice_two_statedProj_two {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = 2 ^ n) :
    OutPNice 2 (StatedProj (StatedSp 2 K)) := by
  have : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card, hcard])
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hcard
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hn hFr hord
      hzp
  have : Finite (StatedProj (StatedSp 2 K)) := inferInstance
  exact outPNice_of_isCyclic_outer Nat.prime_two hcyc

theorem spUCited_outPChain_two_of_isSpGp {L : Type} [Group L] [Finite L] {m n : ℕ}
    (hm : 4 ≤ m) (h : IsSpGp L m n) : OutPChain 2 L := by
  obtain ⟨k, rfl, F, hFld, hFin, hcard, ⟨e⟩⟩ := h
  letI := hFld
  letI := hFin
  have : Fintype F := Fintype.ofFinite F
  have hk2 : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := by
    have h2 : 2 ≤ Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    by_contra hlt
    have hn0 : n = 0 := by omega
    rw [hcard, hn0, pow_zero] at h2
    omega
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card, hcard])
  haveI : NeZero k := ⟨by omega⟩
  let e' : L ≃* StatedProj (StatedSp k F) :=
    e.trans (MulEquiv.ofBijective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj k F)
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo))
  by_cases hk3 : 3 ≤ k
  · exact OutPChain.of_mulEquiv e'
      (spUCited_outPNice_two_statedProj_ge_three (K := F) hk3).toChain
  · have hk_eq : k = 2 := by omega
    subst hk_eq
    exact OutPChain.of_mulEquiv e'
      (spUCited_outPNice_two_statedProj_two (K := F) hn1 hcard).toChain

theorem spUCited_outPChain_two_of_isPSUGp {L : Type} [Group L] [Finite L] {m n : ℕ}
    (hm : 4 ≤ m) (h : IsPSUGp L m n) : OutPChain 2 L := by
  have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible h).2.1
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    intro hd
    have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have hsub : 2 ∣ (2 ^ n + 1) - 2 ^ n := Nat.dvd_sub hd hdvd
    rw [Nat.add_sub_cancel_left] at hsub
    exact absurd hsub (by norm_num)
  have hdiag : ¬ 2 ∣ Nat.gcd m (2 ^ n + 1) := fun hd =>
    hodd (hd.trans (Nat.gcd_dvd_right m (2 ^ n + 1)))
  exact (outPNice_PSU (n := m) (m := n) Nat.prime_two
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)) hdiag).toChain

theorem spUCited_inner_mul_of_outPChain_two {L : Type} [Group L] (h : OutPChain 2 L)
    {α β : MulAut L} (hα : α * α = 1) (hβ : β * β = 1) (hc : α * β = β * α)
    (hαo : α ∉ (MulAut.conj : L →* MulAut L).range)
    (hβo : β ∉ (MulAut.conj : L →* MulAut L).range) :
    α * β ∈ (MulAut.conj : L →* MulAut L).range := by
  have hα2 : α ^ (2 ^ 1) ∈ (MulAut.conj : L →* MulAut L).range := by
    rw [pow_one, pow_two, hα]
    exact Subgroup.one_mem _
  have hβ2 : β ^ (2 ^ 1) ∈ (MulAut.conj : L →* MulAut L).range := by
    rw [pow_one, pow_two, hβ]
    exact Subgroup.one_mem _
  have hβ2' : β ^ 2 = 1 := by rw [pow_two, hβ]
  have hα2' : α ^ 2 = 1 := by rw [pow_two, hα]
  rcases h.comparable hc hα2 hβ2 with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases spUCited_zpow_eq_one_or_self hβ2' m with h1 | h1
    · rw [h1, mul_one] at hm
      exact absurd hm hαo
    · rw [h1] at hm
      exact hm
  · rcases spUCited_zpow_eq_one_or_self hα2' m with h1 | h1
    · rw [h1, mul_one] at hm
      exact absurd hm hβo
    · rw [h1, ← hc] at hm
      exact hm

theorem spPSUOutFact_holds : SpPSUOutFact := by
  intro L _ _ m n hm hL α β hα hβ hc hαo hβo
  rcases hL with hL | hL
  · exact spUCited_inner_mul_of_outPChain_two (spUCited_outPChain_two_of_isSpGp hm hL) hα hβ hc
      hαo hβo
  · exact spUCited_inner_mul_of_outPChain_two (spUCited_outPChain_two_of_isPSUGp hm hL) hα hβ hc
      hαo hβo

end CFSG.LocalAnalysis.WeakClosure81

end
