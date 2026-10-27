module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spAdjointOrbits (x : StatedSp r K) : Set (Set (Module.End K (Fin r ⊕ Fin r → K))) :=
  {O | ∃ z : commutant (spEnd x), IsPrimitiveCentralIdempotent K z ∧
    O = {(z : Module.End K (Fin r ⊕ Fin r → K)), spAdj (z : Module.End K (Fin r ⊕ Fin r → K))}}

@[expose] noncomputable def spKappa (x : StatedSp r K) : ℕ :=
  (spAdjointOrbits x).ncard

open _root_.Classical in
theorem two_mul_card_image_le_sum {α : Type*} (F : Finset α) (ι : α → α)
    (hι : ∀ h ∈ F, ι h ∈ F) (hιι : ∀ h ∈ F, ι (ι h) = h) (w : α → ℕ)
    (hfix : ∀ h ∈ F, ι h = h → 2 ≤ w h) (hpair : ∀ h ∈ F, ι h ≠ h → 2 ≤ w h + w (ι h)) :
    2 * (F.image fun h => ({h, ι h} : Set α)).card ≤ ∑ h ∈ F, w h := by
  set φ : α → Set α := fun h => {h, ι h} with hφ
  have hmaps : ∀ h ∈ F, φ h ∈ F.image φ := fun h hh => Finset.mem_image_of_mem φ hh
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have h2 : ∀ O ∈ F.image φ, 2 ≤ ∑ h ∈ F with φ h = O, w h := by
    intro O hO
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.mp hO
    have hmem1 : h0 ∈ F.filter (fun h => φ h = φ h0) := Finset.mem_filter.mpr ⟨hh0, rfl⟩
    by_cases hfix' : ι h0 = h0
    · exact (hfix h0 hh0 hfix').trans
        (Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) hmem1)
    · have hmem2 : ι h0 ∈ F.filter (fun h => φ h = φ h0) := by
        refine Finset.mem_filter.mpr ⟨hι h0 hh0, ?_⟩
        simp only [hφ, hιι h0 hh0]
        exact Set.pair_comm _ _
      have hsub : ({h0, ι h0} : Finset α) ⊆ F.filter (fun h => φ h = φ h0) := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hmem1
        · rw [Finset.mem_singleton.mp hy]
          exact hmem2
      calc 2 ≤ w h0 + w (ι h0) := hpair h0 hh0 hfix'
        _ = ∑ h ∈ ({h0, ι h0} : Finset α), w h := (Finset.sum_pair (Ne.symm hfix')).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  calc 2 * (F.image φ).card = (F.image φ).card • 2 := by rw [smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ h2

section Degrees

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {y : Module.End K V}

open _root_.Classical in
theorem sum_natDegree_erase_le {p : ℕ} (hp : p.Prime) (hsq : Squarefree (minpoly K y))
    (hyp : y ^ p = 1) :
    ∑ h ∈ (primaryFactors y).erase (X - C 1), h.natDegree ≤ p - 1 := by
  classical
  set F := primaryFactors y with hF
  set F' := F.erase (X - C 1) with hF'
  set g : K[X] := ∏ h ∈ F', h with hg
  have hmin : minpoly K y ∣ X ^ p - 1 := minpoly.dvd K y (by simp [hyp])
  have hgdvd : g ∣ X ^ p - 1 := by
    refine dvd_trans ?_ hmin
    rw [← prod_primaryFactors hsq]
    exact Finset.prod_dvd_prod_of_subset F' F id (Finset.erase_subset _ _)
  have hcop : IsCoprime (X - C 1 : K[X]) g := by
    refine IsCoprime.prod_right fun h hh => ?_
    rw [(irreducible_X_sub_C (1 : K)).coprime_iff_not_dvd]
    intro hdvd
    have hhF : h ∈ F := Finset.mem_of_mem_erase hh
    exact (Finset.ne_of_mem_erase hh) (eq_of_monic_of_associated
      (monic_of_mem_primaryFactors hhF) (monic_X_sub_C 1)
      ((irreducible_X_sub_C (1 : K)).associated_of_dvd (irreducible_of_mem_primaryFactors hhF)
        hdvd).symm)
  have hdvd1 : (X - C 1 : K[X]) ∣ X ^ p - 1 := by
    simpa using sub_one_dvd_pow_sub_one (X : K[X]) p
  have hprod : (X - C 1 : K[X]) * g ∣ X ^ p - 1 := hcop.mul_dvd hdvd1 hgdvd
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun h hh =>
    (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).ne_zero
  have hX0 : (X ^ p - 1 : K[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : K) hp.ne_zero).ne_zero
    simpa using this
  have hdeg : 1 + g.natDegree ≤ p := by
    have h1 := natDegree_le_of_dvd hprod hX0
    rw [natDegree_mul (X_sub_C_ne_zero 1) hg0, natDegree_X_sub_C] at h1
    have h2 : (X ^ p - 1 : K[X]).natDegree = p := by
      simpa using natDegree_X_pow_sub_C (n := p) (r := (1 : K))
    omega
  have hsum : ∑ h ∈ F', h.natDegree = g.natDegree := by
    rw [hg, natDegree_prod _ _ fun h hh =>
      (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).ne_zero]
  omega

theorem primaryMultiplicity_pos' (hsq : Squarefree (minpoly K y)) (a : primaryFactors y) :
    0 < primaryMultiplicity y (a : K[X]) := by
  have hne := primaryComponent_ne_bot hsq a.2
  have : Nontrivial ↥(primaryComponent y (a : K[X])) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

end Degrees

section Bounds

variable {ℓ f p : ℕ} {x : StatedSp r K}

open _root_.Classical in
theorem ncard_reciprocalOrbits_le (D : SpData ℓ f r p K x)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) :
    (reciprocalOrbits (spEnd x)).ncard ≤ 1 + (p - 1) / 2 ∧
      (reciprocalOrbits (spEnd x)).ncard ≤ r := by
  have : Finite K := D.finite
  have hsq := D.squarefree
  have H := D.primaryData
  set F := primaryFactors (spEnd x) with hF
  set φ : K[X] → Set K[X] := fun h => {h, reciprocalPolynomial h} with hφ
  have hι : ∀ h ∈ F, reciprocalPolynomial h ∈ F := fun h hh => H.reciprocal_mem hh
  have hιι : ∀ h ∈ F, reciprocalPolynomial (reciprocalPolynomial h) = h := fun h hh =>
    H.reciprocal_reciprocal hh
  have hcard : (reciprocalOrbits (spEnd x)).ncard = (F.image φ).card := by
    have : reciprocalOrbits (spEnd x) = ((F.image φ : Finset (Set K[X])) : Set (Set K[X])) := by
      rw [Finset.coe_image]
      rfl
    rw [this, Set.ncard_coe_finset]
  have hX1 : (X - C 1 : K[X]) = X - 1 := by simp
  have hselfX : reciprocalPolynomial (X - C 1 : K[X]) = X - C 1 := by
    rw [hX1]
    exact CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one
  have hhalf : ∀ h ∈ F, h ≠ X - C 1 → reciprocalPolynomial h = h → 2 ≤ h.natDegree := by
    intro h hh h1 h2
    obtain ⟨d, hd, -⟩ := (blocks.selfDual ⟨h, hh⟩ (by rw [← hX1]; exact h1) h2).exists_half
    have hd' : h.natDegree = 2 * d := hd
    have := (irreducible_of_mem_primaryFactors hh).natDegree_pos
    omega
  refine ⟨?_, ?_⟩
  · set N := F.erase (X - C 1) with hN
    have hNcl : ∀ h ∈ N, reciprocalPolynomial h ∈ N := by
      intro h hh
      have hhF := Finset.mem_of_mem_erase hh
      refine Finset.mem_erase.mpr ⟨fun h1 => Finset.ne_of_mem_erase hh ?_, hι h hhF⟩
      rw [← hιι h hhF, h1, hselfX]
    have h1 : 2 * (N.image φ).card ≤ ∑ h ∈ N, h.natDegree := by
      refine two_mul_card_image_le_sum N reciprocalPolynomial hNcl
        (fun h hh => hιι h (Finset.mem_of_mem_erase hh)) (fun h => h.natDegree) ?_ ?_
      · intro h hh h2
        exact hhalf h (Finset.mem_of_mem_erase hh) (Finset.ne_of_mem_erase hh) h2
      · intro h hh _
        have h3 := (irreducible_of_mem_primaryFactors (Finset.mem_of_mem_erase hh)).natDegree_pos
        have h4 := (irreducible_of_mem_primaryFactors
          (hι h (Finset.mem_of_mem_erase hh))).natDegree_pos
        omega
    have h2 : ∑ h ∈ N, h.natDegree ≤ p - 1 :=
      sum_natDegree_erase_le D.prime hsq (spEnd_pow D.pow_eq_one)
    have hsub : F.image φ ⊆ insert (φ (X - C 1)) (N.image φ) := by
      intro O hO
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hO
      by_cases h1 : h = X - C 1
      · rw [h1]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem φ (Finset.mem_erase.mpr ⟨h1, hh⟩))
    have h3 : (F.image φ).card ≤ (N.image φ).card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [hcard]
    omega
  · have hw : ∀ h ∈ F, 0 < primaryMultiplicity (spEnd x) h := fun h hh =>
      primaryMultiplicity_pos' hsq ⟨h, hh⟩
    have hdeg : ∀ h ∈ F, 0 < h.natDegree := fun h hh =>
      (irreducible_of_mem_primaryFactors hh).natDegree_pos
    have h1 : 2 * (F.image φ).card ≤ ∑ h ∈ F, h.natDegree * primaryMultiplicity (spEnd x) h := by
      refine two_mul_card_image_le_sum F reciprocalPolynomial hι hιι
        (fun h => h.natDegree * primaryMultiplicity (spEnd x) h) ?_ ?_
      · intro h hh h2
        by_cases h1 : h = X - C 1
        · subst h1
          obtain ⟨s, hs, -⟩ := blocks.rank
          rw [← hX1] at hs
          have hfact : Fact (Irreducible (X - C 1 : K[X])) :=
            ⟨irreducible_of_mem_primaryFactors hh⟩
          have h3 : Module.finrank K (primaryComponent (spEnd x) (X - C 1)) =
              (X - C 1 : K[X]).natDegree * primaryMultiplicity (spEnd x) (X - C 1) :=
            finrank_primaryComponent (x := spEnd x) (a := X - C 1)
          rw [natDegree_X_sub_C, one_mul] at h3
          have h4 : 0 < Module.finrank K (primaryComponent (spEnd x) (X - C 1)) := by
            have hne := primaryComponent_ne_bot hsq hh
            have : Nontrivial ↥(primaryComponent (spEnd x) (X - C 1)) :=
              Submodule.nontrivial_iff_ne_bot.mpr hne
            exact Module.finrank_pos
          rw [natDegree_X_sub_C, one_mul]
          omega
        · have h3 := hhalf h hh h1 h2
          have h4 := hw h hh
          nlinarith
      · intro h hh _
        have h3 := hdeg h hh
        have h4 := hdeg _ (hι h hh)
        have h5 := hw h hh
        have h6 := hw _ (hι h hh)
        nlinarith
    have h2 : ∑ h ∈ F, h.natDegree * primaryMultiplicity (spEnd x) h = 2 * r := by
      have h3 := finrank_eq_sum_degree_mul_multiplicity hsq
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h3
      rw [Finset.sum_coe_sort F (fun h => h.natDegree * primaryMultiplicity (spEnd x) h)] at h3
      omega
    rw [hcard]
    omega

theorem spKappa_le (D : SpData ℓ f r p K x) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) :
    spKappa x ≤ 1 + (p - 1) / 2 ∧ spKappa x < p ∧ spKappa x ≤ r := by
  have hfin : (reciprocalOrbits (spEnd x)).Finite :=
    (Finset.finite_toSet (primaryFactors (spEnd x))).image _
  have hsub : spAdjointOrbits x ⊆
      (fun O : Set K[X] => (primaryProjection (spEnd x)) '' O) '' reciprocalOrbits (spEnd x) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h, hh, hzh⟩ := (blocks.primitiveCentral z).mp hz
    refine ⟨{h, reciprocalPolynomial h}, ⟨h, hh, rfl⟩, ?_⟩
    show (primaryProjection (spEnd x)) '' ({h, reciprocalPolynomial h} : Set K[X]) = _
    rw [Set.image_pair, hzh, blocks.adj_primitiveCentral h hh]
  have hle : spKappa x ≤ (reciprocalOrbits (spEnd x)).ncard :=
    (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  obtain ⟨h1, h2⟩ := ncard_reciprocalOrbits_le D blocks
  have hp3 := D.three_lt
  refine ⟨hle.trans h1, ?_, hle.trans h2⟩
  have := hle.trans h1
  omega

end Bounds

end CFSG.RankThree.PartOne.KCSpComm
