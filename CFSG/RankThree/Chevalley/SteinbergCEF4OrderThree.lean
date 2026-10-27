module

public import CFSG.RankThree.Chevalley.SteinbergCEF4OrderThreeCheck

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace
  CFSG.LieType.Steinberg.Adjoint

namespace F4Weyl

theorem exists_A2_of_conj_preserves {S : Set (Fin Tag.F4.rank → ℤ)} (hS : S ≠ ∅)
    (hinv : ∀ α ∈ S, (f4Coxeter ^ 4) • α ∈ S) {u : WeylGroup .F4} {J : Set (Fin Tag.F4.rank)}
    (hJ : J ≠ Set.univ) (hu : (fun α => u • α) '' S = parabolicRoots .F4 J) :
    ∃ (i j : Fin Tag.F4.rank) (ε : ℤ),
      ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
      (ε = 1 ∨ ε = -1) ∧ J = {i, j} ∧
      ∀ β ∈ parabolicRoots .F4 {i, j},
        (u * f4Coxeter ^ 4 * u⁻¹) • β = ((simple .F4 i * simple .F4 j) ^ ε) • β := by
  classical
  have hw'J := conj_smul_mem_parabolicRoots hinv hu
  set Jf := J.toFinset with hJfdef
  have hJf : (Jf : Set (Fin Tag.F4.rank)) = J := Set.coe_toFinset J
  rw [← hJf] at hw'J hu hJ
  have hJne : Jf.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.coe_empty, parabolicRoots_empty, Set.image_eq_empty] at hu
    exact hS hu
  have hJu : Jf ≠ Finset.univ := fun h => hJ (by rw [h, Finset.coe_univ])
  set w' := u * f4Coxeter ^ 4 * u⁻¹ with hw'
  set c := restrCols Jf w' with hc
  have hcm := restrCols_mem_colChoices hw'J
  have hcol : ∀ i ∈ Jf, c i = w' • Pi.single i 1 := fun i hi => by
    rw [hc, restrCols, ite_eq_left hi]
  have hsingle : ∀ i ∈ Jf, (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      parabolicRoots .F4 (Jf : Set (Fin Tag.F4.rank)) := fun i hi =>
    ⟨isRoot_single .F4 i, fun k hk => by
      rw [Pi.single_apply, ite_eq_right]
      rintro rfl
      exact hk hi⟩
  have hcond1 : ∀ i ∈ Jf, colMap c (c i) + c i + Pi.single i 1 = 0 := by
    intro i hi
    have hci : c i ∈ parabolicRoots .F4 (Jf : Set (Fin Tag.F4.rank)) := by
      rw [hcol i hi]
      exact hw'J _ (hsingle i hi)
    rw [← smul_eq_colMap_restrCols Jf w' hci.2, hcol i hi]
    have h := conj_quadratic f4OrderThree_relation u (Pi.single i 1)
    simpa only [one_smul] using h
  have hcond2 : ∀ β ∈ parabolicRootList Jf, colMap c β ∈ parabolicRootList Jf := by
    intro β hβ
    rw [mem_parabolicRootList] at hβ ⊢
    rw [← smul_eq_colMap_restrCols Jf w' hβ.2]
    exact hw'J β hβ
  rw [eq_cols4 c] at hcond1 hcond2
  have hres := order_three_restriction_check Jf hJne hJu _ (hcm _) _ (hcm _) _ (hcm _) _ (hcm _)
    hcond1 hcond2
  rw [← eq_cols4 c] at hres
  have hact : ∀ (l : List (Fin 4)), c = restrCols Jf (f4WordProd l) →
      ∀ β ∈ parabolicRoots .F4 (Jf : Set (Fin Tag.F4.rank)), w' • β = f4WordProd l • β := by
    intro l hl β hβ
    rw [smul_eq_colMap_restrCols Jf w' hβ.2, ← hc, hl, ← smul_eq_colMap_restrCols Jf _ hβ.2]
  rcases hres with ⟨hJ01, hc' | hc'⟩ | ⟨hJ23, hc' | hc'⟩
  · refine ⟨f4Index 0, f4Index 1, 1, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, ?_, fun β hβ => ?_⟩
    · rw [← hJf, hJ01, coe_pair_finset]
    · rw [zpow_one, ← f4WordProd_pair]
      exact hact [0, 1] (by rw [hc', restrCols_f4WordProd]) β (by rwa [hJ01, coe_pair_finset])
  · refine ⟨f4Index 0, f4Index 1, -1, Or.inl ⟨rfl, rfl⟩, Or.inr rfl, ?_, fun β hβ => ?_⟩
    · rw [← hJf, hJ01, coe_pair_finset]
    · rw [zpow_neg_one, ← f4WordProd_pair, inv_f4WordProd_pair]
      exact hact [1, 0] (by rw [hc', restrCols_f4WordProd]) β (by rwa [hJ01, coe_pair_finset])
  · refine ⟨f4Index 2, f4Index 3, 1, Or.inr ⟨rfl, rfl⟩, Or.inl rfl, ?_, fun β hβ => ?_⟩
    · rw [← hJf, hJ23, coe_pair_finset]
    · rw [zpow_one, ← f4WordProd_pair]
      exact hact [2, 3] (by rw [hc', restrCols_f4WordProd]) β (by rwa [hJ23, coe_pair_finset])
  · refine ⟨f4Index 2, f4Index 3, -1, Or.inr ⟨rfl, rfl⟩, Or.inr rfl, ?_, fun β hβ => ?_⟩
    · rw [← hJf, hJ23, coe_pair_finset]
    · rw [zpow_neg_one, ← f4WordProd_pair, inv_f4WordProd_pair]
      exact hact [3, 2] (by rw [hc', restrCols_f4WordProd]) β (by rwa [hJ23, coe_pair_finset])

end F4Weyl

open F4Weyl

theorem F4_order_three_Weyl_lattice_and_surviving_A2_kernels :
    weylMatrix (τ := .F4) (f4Coxeter ^ 4) =
      !![0, 1, -1, 0; 1, 1, -1, -1; 2, 2, -2, -1; 0, 2, -1, -1] ∧
    weylMatrix (f4Coxeter ^ 4) * weylMatrix (f4Coxeter ^ 4) + weylMatrix (f4Coxeter ^ 4) + 1 =
      0 ∧
    orderOf (f4Coxeter ^ 4) = 3 ∧
    f4OrderThreeBasis.det = -1 ∧ Function.Bijective f4OrderThreeBasis.mulVec ∧
    ∀ p : ℕ, p.Prime → 3 < p → ∀ a : (ZMod p)ˣ, orderOf a = 3 →
      ∀ v : Fin Tag.F4.rank → ZMod p, v ≠ 0 →
      (dualMatrix (ZMod p) (f4Coxeter ^ 4)).mulVec v = (a : ZMod p) • v →
      (charRootKernel v = ∅ ∨
        ∃ (u : WeylGroup .F4) (i j : Fin Tag.F4.rank) (ε : ℤ),
          ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
          (ε = 1 ∨ ε = -1) ∧
          (fun α => u • α) '' charRootKernel v = parabolicRoots .F4 {i, j} ∧
          ∀ x ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {i, j}),
            weylAct .F4 (u * f4Coxeter ^ 4 * u⁻¹) x =
              weylAct .F4 ((simple .F4 i * simple .F4 j) ^ ε) x) ∧
      (charRootKernel v ≠ ∅ → (charRootKernel v).ncard = 6 ∧
        ∀ α ∈ charRootKernel v, ∀ β ∈ charRootKernel v, iform α α = iform β β) := by
  refine ⟨weylMatrix_f4OrderThree, by rw [weylMatrix_f4OrderThree]; exact
    f4OrderThreeMatrix_relation, orderOf_f4OrderThree, det_f4OrderThreeBasis,
    bijective_mulVec_f4OrderThreeBasis, fun p hp hp3 a _ v hv heig => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hinv : ∀ α ∈ charRootKernel v, (f4Coxeter ^ 4) • α ∈ charRootKernel v :=
    fun α hα => (smul_mem_charRootKernel_iff heig α).2 hα
  have key : charRootKernel v ≠ ∅ → ∃ (u : WeylGroup .F4) (i j : Fin Tag.F4.rank) (ε : ℤ),
      ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
      (ε = 1 ∨ ε = -1) ∧
      (fun α => u • α) '' charRootKernel v = parabolicRoots .F4 {i, j} ∧
      ∀ β ∈ parabolicRoots .F4 {i, j},
        (u * f4Coxeter ^ 4 * u⁻¹) • β = ((simple .F4 i * simple .F4 j) ^ ε) • β := by
    intro hne
    obtain ⟨u, J, hJ, hu⟩ := exists_smul_charRootKernel_eq_parabolicRoots hp3 hv
    obtain ⟨i, j, ε, hij, hε, rfl, hact⟩ := exists_A2_of_conj_preserves hne hinv hJ hu
    exact ⟨u, i, j, ε, hij, hε, hu, hact⟩
  refine ⟨?_, fun hne => ?_⟩
  · by_cases hne : charRootKernel v = ∅
    · exact Or.inl hne
    · obtain ⟨u, i, j, ε, hij, hε, hu, hact⟩ := key hne
      exact Or.inr ⟨u, i, j, ε, hij, hε, hu, weylAct_eqOn_span hact⟩
  · obtain ⟨u, i, j, ε, hij, -, hu, -⟩ := key hne
    have hinj : Function.Injective fun α : Fin Tag.F4.rank → ℤ => u • α := MulAction.injective u
    have hcard : (charRootKernel v).ncard = (parabolicRoots .F4 {i, j}).ncard := by
      rw [← hu, Set.ncard_image_of_injective _ hinj]
    have hlen : ∃ n : ℤ, (parabolicRoots .F4 {i, j}).ncard = 6 ∧
        ∀ β ∈ parabolicRoots .F4 {i, j}, iform β β = n := by
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨4, ?_, fun β hβ => ?_⟩
        · rw [← coe_pair_finset, parabolicRoots_eq_toFinset, Set.ncard_coe_finset,
            parabolicRootList_card_01]
        · rw [← coe_pair_finset, ← mem_parabolicRootList] at hβ
          exact iform_parabolicRootList_01 β hβ
      · refine ⟨2, ?_, fun β hβ => ?_⟩
        · rw [← coe_pair_finset, parabolicRoots_eq_toFinset, Set.ncard_coe_finset,
            parabolicRootList_card_23]
        · rw [← coe_pair_finset, ← mem_parabolicRootList] at hβ
          exact iform_parabolicRootList_23 β hβ
    obtain ⟨n, h6, hn⟩ := hlen
    refine ⟨hcard.trans h6, fun α hα β hβ => ?_⟩
    have hα' : u • α ∈ parabolicRoots .F4 {i, j} := hu ▸ ⟨α, hα, rfl⟩
    have hβ' : u • β ∈ parabolicRoots .F4 {i, j} := hu ▸ ⟨β, hβ, rfl⟩
    rw [← iform_smul u α α, ← iform_smul u β β, hn _ hα', hn _ hβ']

end CFSG.RankThree.Chevalley
