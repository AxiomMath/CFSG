module

public import CFSG.RankThree.PartOne.TCP.SurvIso
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting
public import CFSG.RankThree.PartOne.TCP.SurvPrimary

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.PartOne.KCSpComm CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

section Elementary

theorem units_eq_one_of_pow_two_pow {E : Type*} [Field E] [CharP E 2] {u : Eˣ} {k : ℕ}
    (h : u ^ 2 ^ k = 1) : u = 1 := by
  have h1 : ((u : E) - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, one_pow, sub_self]
  exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1))

end Elementary

section Struct

variable {K : Type} [Field K] [Finite K] {f p : ℕ}

omit [Finite K] in
theorem natDegree_X_sub_one : (X - 1 : K[X]).natDegree = 1 := by
  simpa using natDegree_X_sub_C (1 : K)

theorem spBlockIdx_unique {x : StatedSp 2 K} {ℓ : ℕ}
    (hD : SpData ℓ f 2 p K x) (hord : orderOf (Nat.card K : ZMod p) = 2)
    (blocks : SpPrimaryBlocks ℓ f p x (proj 2 K x))
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm 2 K u v = 0) (hWx : ∀ w ∈ W, spEnd x w ∈ W) :
    Nonempty (SpBlockIdx x) ∧ Subsingleton (SpBlockIdx x) := by
  classical
  have hsq := hD.squarefree
  have H := hD.primaryData
  have hp := hD.prime
  have hxp := hD.pow_eq_one
  have hX : spEnd x ^ p = 1 := spEnd_pow hxp
  have hsum : ∑ a : primaryFactors (spEnd x),
      (a : K[X]).natDegree * primaryMultiplicity (spEnd x) (a : K[X]) = 4 := by
    rw [← finrank_eq_sum_degree_mul_multiplicity hsq]
    simp [Module.finrank_fintype_fun_eq_card]
  have hdeg : ∀ a : primaryFactors (spEnd x), (a : K[X]) ≠ X - 1 → 2 ≤ (a : K[X]).natDegree := by
    intro a ha1
    have h2 := two_dvd_natDegree_of_mem hp hX hord a.2 ha1
    have h0 : 0 < (a : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
    omega
  have hfin : ∀ a : primaryFactors (spEnd x), finrank K (primaryComponent (spEnd x) (a : K[X])) =
      (a : K[X]).natDegree * primaryMultiplicity (spEnd x) (a : K[X]) := fun a => by
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    exact finrank_primaryComponent (spEnd x) (a : K[X])
  have hmpos : ∀ a : primaryFactors (spEnd x), 1 ≤ primaryMultiplicity (spEnd x) (a : K[X]) := by
    intro a
    have h1 : 1 ≤ finrank K (primaryComponent (spEnd x) (a : K[X])) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq a.2)
    rw [hfin a] at h1
    rcases Nat.eq_zero_or_pos (primaryMultiplicity (spEnd x) (a : K[X])) with h0 | h0
    · rw [h0, mul_zero] at h1
      omega
    · exact h0
  have hfixed : ∀ a : primaryFactors (spEnd x), (a : K[X]) = X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) (a : K[X]) := by
    intro a ha1
    obtain ⟨s, hs, -⟩ := blocks.rank
    have h1 : 1 ≤ finrank K (primaryComponent (spEnd x) (a : K[X])) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq a.2)
    have h2 := hfin a
    have hV : primaryComponent (spEnd x) (a : K[X]) = primaryComponent (spEnd x) (X - 1) := by
      rw [ha1]
    have hd1 : (a : K[X]).natDegree = 1 := by
      rw [ha1]
      exact natDegree_X_sub_one
    rw [hV] at h1 h2
    rw [hd1, one_mul] at h2
    omega
  have hterm : ∀ a : SpBlockIdx x, 2 ≤ (a.1 : K[X]).natDegree *
      primaryMultiplicity (spEnd x) (a.1 : K[X]) ∧ ((a.1 : K[X]) ≠ X - 1 →
      4 ≤ (a.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (a.1 : K[X])) := by
    intro a
    have hm := a.2
    have hd1 : 1 ≤ (a.1 : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.1.2)
    refine ⟨by nlinarith, fun ha1 => ?_⟩
    have := hdeg a.1 ha1
    nlinarith
  refine ⟨?_, ⟨fun a b => ?_⟩⟩
  ·
    by_contra hne
    rw [not_nonempty_iff] at hne
    have hall : ∀ a : primaryFactors (spEnd x), primaryMultiplicity (spEnd x) (a : K[X]) ≤ 1 := by
      intro a
      by_contra hlt
      exact hne.false ⟨a, by omega⟩
    obtain ⟨a, ha, hne'⟩ := exists_inf_primaryComponent_ne_bot (T := spEnd x) hsq hW0 hWx
    have ha1 : a ≠ X - 1 := by
      intro h1
      have h2 : 2 ≤ primaryMultiplicity (spEnd x) a := hfixed ⟨a, ha⟩ h1
      have h3 : primaryMultiplicity (spEnd x) a ≤ 1 := hall ⟨a, ha⟩
      omega
    have hm1 : primaryMultiplicity (spEnd x) a = 1 := by
      have h2 : 1 ≤ primaryMultiplicity (spEnd x) a := hmpos ⟨a, ha⟩
      have h3 : primaryMultiplicity (spEnd x) a ≤ 1 := hall ⟨a, ha⟩
      omega
    exact false_of_invariant_isotropic_block H ha
      (reciprocalPolynomial_eq_of_mem hp hX hord ha ha1) hm1 hWiso hWx hne'
  ·
    by_contra hab
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    obtain ⟨ha2, ha4⟩ := hterm a
    obtain ⟨hb2, hb4⟩ := hterm b
    have hle : (a.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (a.1 : K[X]) +
        (b.1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (b.1 : K[X]) ≤ 4 := by
      rw [← hsum, ← Finset.sum_pair hab' (f := fun c : primaryFactors (spEnd x) =>
        (c : K[X]).natDegree * primaryMultiplicity (spEnd x) (c : K[X]))]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    by_cases ha1 : (a.1 : K[X]) = X - 1
    · have hb1 : (b.1 : K[X]) ≠ X - 1 := fun h => hab' (Subtype.ext (ha1.trans h.symm))
      have := hb4 hb1
      linarith
    · have := ha4 ha1
      linarith

theorem sp4_survivor_component {x : StatedSp 2 K} (hD : SpData 2 f 2 p K x)
    (hord : orderOf (Nat.card K : ZMod p) = 2) (blocks : SpPrimaryBlocks 2 f p x (proj 2 K x))
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW0 : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm 2 K u v = 0) (hWx : ∀ w ∈ W, spEnd x w ∈ W) :
    ∃ D : Subgroup (StatedSp 2 K), CFSG.IsQuasisimple ↥D ∧
      D ≤ Subgroup.centralizer ({x} : Set (StatedSp 2 K)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), ∀ d ∈ D, g * d * g⁻¹ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
        ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)), ⁅g, h⁆ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D) := by
  classical
  obtain ⟨hne, hsub⟩ := spBlockIdx_unique hD hord blocks hW0 hWiso hWx
  obtain ⟨b⟩ := hne
  have facts := hD.blockFacts blocks
  have hall : ∀ a : SpBlockIdx x, a = b := fun a => hsub.elim a b
  have hjoin : (⨆ a : SpBlockIdx x, specialBlock (spForm 2 K) (spLin 2 K x) (a.1 : K[X])) =
      specialBlock (spForm 2 K) (spLin 2 K x) (b.1 : K[X]) := by
    apply le_antisymm
    · exact iSup_le fun a => by rw [hall a]
    · exact le_iSup (fun a : SpBlockIdx x =>
        specialBlock (spForm 2 K) (spLin 2 K x) (a.1 : K[X])) b
  have hCM : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 2 K)),
      spLin 2 K g ∈ unitaryCentralizer (spForm 2 K) (spLin 2 K x) := fun g hg => by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hg
  have hchar : CharP K 2 := hD.charP
  refine ⟨spPull x (b.1 : K[X]), spPull_isQuasisimple (facts b.1) b.2,
    spPull_le_centralizer x _, spPull_normalized x _, ?_, ?_⟩
  · intro g hg h hh
    have hcomm := Subgroup.commutator_mem_commutator (hCM g hg) (hCM h hh)
    rw [commutator_unitaryCentralizer_eq_iSup blocks facts, hjoin] at hcomm
    change spLin 2 K ⁅g, h⁆ ∈ specialBlock (spForm 2 K) (spLin 2 K x) (b.1 : K[X])
    rw [map_commutatorElement]
    exact hcomm
  · intro g hg hk
    obtain ⟨k, hk⟩ := hk
    have hg2 : g ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have hdet : ∀ a : primaryFactors (spEnd x), ∃ hgl : spLin 2 K g ∈
        gl_centralizer (spLin 2 K x),
        blockDetHom (spLin 2 K x) (a : K[X]) ⟨spLin 2 K g, hgl⟩ = 1 := by
      intro a
      refine ⟨(hCM g hg).2, ?_⟩
      have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
      have : CharP (AdjoinRoot (a : K[X])) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 2
      refine units_eq_one_of_pow_two_pow (k := k) ?_
      rw [← map_pow]
      have h1 : (⟨spLin 2 K g, (hCM g hg).2⟩ : gl_centralizer (spLin 2 K x)) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        change (spLin 2 K g) ^ 2 ^ k = 1
        rw [← map_pow, hg2, map_one]
      rw [h1, map_one]
    have hmem := mem_iSup_specialBlock_of_det_one hD blocks facts (hCM g hg) hdet
    rw [hjoin] at hmem
    exact hmem

end Struct

end CFSG.RankThree.PartOne.TCP
