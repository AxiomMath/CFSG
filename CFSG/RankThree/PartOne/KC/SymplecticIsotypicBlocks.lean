module

public import Mathlib
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicSpecial

public section

namespace CFSG.RankThree.PartOne.KCSpIsotypic

open Polynomial Module Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

theorem dualPoly_id (h : K[X]) : dualPoly (RingHom.id K) h = reciprocalPolynomial h := by
  simp [dualPoly, reciprocalPolynomial]

theorem reverse_X_sub_one_eq : (X - 1 : K[X]).reverse = 1 - X := by
  have h : (X - 1 : K[X]) = X + C (-1) := by simp [sub_eq_add_neg]
  have hX : (X : K[X]).reverse = 1 := by
    have h1 := Polynomial.reverse_mul_X (1 : K[X])
    rw [one_mul] at h1
    rw [h1]
    simpa using Polynomial.reverse_C (1 : K)
  rw [h, Polynomial.reverse_add_C, hX]
  simp [sub_eq_add_neg]

theorem reciprocalPolynomial_X_sub_one : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := by
  unfold reciprocalPolynomial
  have h2 : (X - 1 : K[X]).coeff 0 = -1 := by simp
  rw [h2, reverse_X_sub_one_eq, inv_neg, inv_one, map_neg, map_one]
  ring

theorem orbitFactor_spForm (x : StatedSp r K) (h : K[X]) :
    orbitFactor (spForm r K) (spLin r K x) h =
      supportedUnitary (spForm r K) (spLin r K x) {h, reciprocalPolynomial h} := by
  unfold orbitFactor
  rw [dualPoly_id]

theorem map_spSupported (x : StatedSp r K) (O : Set K[X]) :
    (spSupported x O).map (spLin r K) = supportedUnitary (spForm r K) (spLin r K x) O :=
  Subgroup.map_comap_eq_self ((supportedUnitary_le_sesq x O).trans range_spLin.ge)

@[expose] noncomputable def spOrbitEquiv (x : StatedSp r K) {O : Set K[X]} {h : K[X]}
    (hO : ({h, reciprocalPolynomial h} : Set K[X]) = O) :
    orbitFactor (spForm r K) (spLin r K x) h ≃* spSupported x O :=
  (MulEquiv.subgroupCongr (by rw [orbitFactor_spForm, hO])).trans
    (comapSpLinEquiv _ (supportedUnitary_le_sesq x O)).symm

theorem coe_spOrbitEquiv (x : StatedSp r K) {O : Set K[X]} {h : K[X]}
    (hO : ({h, reciprocalPolynomial h} : Set K[X]) = O)
    (g : orbitFactor (spForm r K) (spLin r K x) h) :
    spLin r K ((spOrbitEquiv x hO g : spSupported x O) : StatedSp r K) =
      ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K))) := by
  have h1 := coe_comapSpLinEquiv (supportedUnitary (spForm r K) (spLin r K x) O)
    (supportedUnitary_le_sesq x O) (spOrbitEquiv x hO g)
  have h2 : comapSpLinEquiv (supportedUnitary (spForm r K) (spLin r K x) O)
      (supportedUnitary_le_sesq x O) (spOrbitEquiv x hO g) =
        MulEquiv.subgroupCongr (by rw [orbitFactor_spForm, hO]) g :=
    (comapSpLinEquiv _ (supportedUnitary_le_sesq x O)).apply_symm_apply _
  rw [h2] at h1
  exact h1.symm

theorem spEnd_orbitEquiv (x : StatedSp r K) {O : Set K[X]} {h : K[X]}
    (hO : ({h, reciprocalPolynomial h} : Set K[X]) = O)
    (g : orbitFactor (spForm r K) (spLin r K x) h) (v : Fin r ⊕ Fin r → K) :
    spEnd ((spOrbitEquiv x hO g : spSupported x O) : StatedSp r K) v =
      ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) v := by
  have := coe_spOrbitEquiv x hO g
  change ((spLin r K ((spOrbitEquiv x hO g : spSupported x O) : StatedSp r K) :
    LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K _) v = _
  rw [this]

theorem exists_finset_card_four_of_card {E : Type*} [Finite E] (h : 4 ≤ Nat.card E) :
    ∃ s : Finset E, s.card = 4 := by
  have := Fintype.ofFinite E
  have h4 : 4 ≤ (Finset.univ : Finset E).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

theorem spBlockFacts_of_spPaired {ℓ f p : ℕ} (hp5 : 5 ≤ p) (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hP : SpPairedBlock ℓ f p x h) :
    SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨φ, hφ, -⟩ := hP.factor
  refine spBlockFacts_of_paired ((spOrbitEquiv x rfl).trans φ) (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]
  · have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hle := Nat.le_of_dvd (by omega) hP.dvd
    have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      omega
    have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
    exact exists_finset_card_four_of_card hcard

theorem spBlockFacts_of_spSelfDual {ℓ f p : ℕ} (hp5 : 5 ≤ p) (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hself : reciprocalPolynomial (h : K[X]) = h)
    (hS : SpSelfDualBlock ℓ f p x h) : SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨d, -, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  refine spBlockFacts_of_selfDual hE hHf hHfl ((spOrbitEquiv x hO).trans φ) (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  · have hN : 4 ≤ (ℓ ^ f) ^ d := by
      have hle := Nat.le_of_dvd (by positivity) hpd
      omega
    rw [← pow_mul] at hN
    exact hN

theorem spBlockFacts_of_spFixed {ℓ f p : ℕ} {x : StatedSp r K}
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hq : 4 ≤ Nat.card K ∨
      (Nat.card K = 3 ∧ 4 ≤ Module.finrank K (primaryComponent (spEnd x) (X - 1))) ∨
      (Nat.card K = 2 ∧ 6 ≤ Module.finrank K (primaryComponent (spEnd x) (X - 1)))) :
    SpBlockFacts (spForm r K) (spLin r K x) ⟨X - 1, hmem⟩ := by
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hmem
  have hO : ({(X - 1 : K[X]), reciprocalPolynomial (X - 1 : K[X])} : Set K[X]) = {X - 1} := by
    rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  refine spBlockFacts_of_fixed (a := ⟨X - 1, hmem⟩) hsq rfl spForm_isAlt
    blocks.fixed_nondegenerate ((spOrbitEquiv x hO).trans φ) (fun g v => ?_) hq
  rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]

theorem spBlockFacts {ℓ f p : ℕ} {x : StatedSp r K} (hp5 : 5 ≤ p) (hq : 3 < ℓ ^ f)
    (hK : Nat.card K = ℓ ^ f) (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x)) :
    SpBlockFacts (spForm r K) (spLin r K x) h := by
  by_cases h1 : (h : K[X]) = X - 1
  · obtain ⟨h0, hm⟩ := h
    change h0 = X - 1 at h1
    subst h1
    exact spBlockFacts_of_spFixed hsq blocks hm (Or.inl (by omega))
  · by_cases h2 : reciprocalPolynomial (h : K[X]) = h
    · exact spBlockFacts_of_spSelfDual hp5 (by omega) h2 (blocks.selfDual h h1 h2)
    · exact spBlockFacts_of_spPaired hp5 (by omega) (blocks.paired h (Ne.symm h2))

end CFSG.RankThree.PartOne.KCSpIsotypic
