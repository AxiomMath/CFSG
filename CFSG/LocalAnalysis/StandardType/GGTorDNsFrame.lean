module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MPlane
public import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusType
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.TorDNs

open QuadraticMap CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.Open
  CFSG.StandardType.OmNsRootGen CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_spanningCoherentFrame (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ)
    (hℓ : 4 ≤ ℓ) (htype : IsPlusType Q ↔ Even ℓ) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (U : Fin ℓ → Submodule F V) (e : Fin ℓ → ↥(orthDerived Q)) (u : Fin ℓ → V) (c t : F),
      IsCoherentFrame Q p U e E u c t ∧ (⨆ j, U j) = ⊤ := by
  classical
  obtain ⟨k, U, e₀, hF₀, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega : 3 ≤ ℓ) hE hsc
  have hk : 1 ≤ k := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨e, u, c, t, hF, -⟩ := exists_coherentFrame hF₀ hp hp2 hpq hk
  rcases hcase with ⟨hkℓ, htop⟩ | ⟨hkℓ, f, f', hf, hf', hQf, hQf', hff'⟩
  · subst k
    exact ⟨U, e, u, c, t, hF, htop⟩
  · exfalso
    let P : CFSG.ClassicalGroups.Orthogonal.HypPair Q := ⟨f, f', hQf, hQf', hff'⟩
    have hdimH : Module.finrank F (Submodule.span F {f, f'}) = 2 := by
      have h := CFSG.ClassicalGroups.Orthogonal.HypPair.finrank_span P
      simpa using h
    have hHplus : IsPlusType (Q.comp (Submodule.span F {f, f'}).subtype) := by
      have hmem : f ∈ Submodule.span F {f, f'} := Submodule.subset_span (by simp)
      refine ⟨Submodule.span F {⟨f, hmem⟩}, ?_, ?_⟩
      · have hfnz : (⟨f, hmem⟩ : ↥(Submodule.span F {f, f'})) ≠ 0 := by
          intro h0
          have hf0 : f = 0 := congrArg Subtype.val h0
          rw [hf0] at hff'
          simpa using hff'
        rw [finrank_span_singleton hfnz, hdimH]
      · intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        show Q ((a • (⟨f, hmem⟩ : ↥(Submodule.span F {f, f'})) :
          ↥(Submodule.span F {f, f'})) : V) = 0
        rw [Submodule.coe_smul, QuadraticMap.map_smul, hQf, smul_zero]
    have hHnd : (polarBilin (Q.comp (Submodule.span F {f, f'}).subtype)).Nondegenerate :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4.nondeg_comp_subtype'
        (CFSG.ClassicalGroups.Orthogonal.polarNondegOn_span_pair_of_polar_eq_one hff')
    have hHle : Submodule.span F {f, f'} ≤ polarPerp Q (⨆ j, U j) := by
      intro x hx
      rw [mem_polarPerp_iff]
      intro y hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
      have h1 : polar Q y f = 0 := (mem_polarPerp_iff.1 hf) y hy
      have h2 : polar Q y f' = 0 := (mem_polarPerp_iff.1 hf') y hy
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h1, h2]
      ring
    have hdisj : Disjoint (⨆ j, U j) (Submodule.span F {f, f'}) :=
      (hF₀.toIsPlaneSystem.isCompl_iSup).disjoint.mono_right hHle
    have horth : ∀ x ∈ (⨆ j, U j), ∀ y ∈ Submodule.span F {f, f'}, polar Q x y = 0 :=
      fun x hx y hy => (mem_polarPerp_iff.1 (hHle hy)) x hx
    have hWuniv : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by
      rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ]
    have hdimW : Module.finrank F ((⨆ j : Fin k, U j) : Submodule F V) = 2 * k := by
      have h := hF₀.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin k))
      rw [hWuniv, Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hWnd : (polarBilin (Q.comp (⨆ j, U j).subtype)).Nondegenerate := by
      have h := hF₀.toIsPlaneSystem.nondeg_biSup (Finset.univ : Finset (Fin k))
      rw [hWuniv] at h
      exact h
    have htopWH : (⨆ j, U j) ⊔ Submodule.span F {f, f'} = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h := Submodule.finrank_sup_add_finrank_inf_eq (⨆ j, U j)
        (Submodule.span F {f, f'})
      rw [disjoint_iff.1 hdisj, finrank_bot, add_zero, hdimW, hdimH] at h
      rw [h, hdim, ← hkℓ]
      ring
    have hWtype : IsPlusType (Q.comp (⨆ j, U j).subtype) ↔ Even k := by
      have h := hF₀.toIsPlaneSystem.isPlusType_biSup_iff (Finset.univ : Finset (Fin k))
      rw [hWuniv, Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hsup := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4.isPlusType_sup_iff'
      (Q := Q) hdisj horth hWnd hHnd (d₁ := k) (d₂ := 1) hk le_rfl hdimW
      (by simpa using hdimH)
    have hQtype : IsPlusType Q ↔ Even k := by
      rw [← isPlusType_comp_top_iff, ← htopWH, hsup]
      simp [hWtype, hHplus]
    have hEven : Even k ↔ Even ℓ := hQtype.symm.trans htype
    rw [← hkℓ, Nat.even_add_one] at hEven
    by_cases hkE : Even k
    · exact (hEven.mp hkE) hkE
    · exact hkE (hEven.mpr hkE)

theorem exists_nonFullCoherentFrame (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ)
    (hℓ : 4 ≤ ℓ) (htype : IsPlusType Q ↔ Odd ℓ) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (k : ℕ) (U : Fin k → Submodule F V) (e : Fin k → ↥(orthDerived Q)) (u : Fin k → V)
      (c t : F) (f f' : V),
      IsCoherentFrame Q p U e E u c t ∧ k + 1 = ℓ ∧
      f ∈ polarPerp Q (⨆ j, U j) ∧ f' ∈ polarPerp Q (⨆ j, U j) ∧
      Q f = 0 ∧ Q f' = 0 ∧ polar Q f f' = 1 := by
  classical
  obtain ⟨k, U, e₀, hF₀, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega : 3 ≤ ℓ) hE hsc
  have hk : 1 ≤ k := by rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨e, u, c, t, hF, -⟩ := exists_coherentFrame hF₀ hp hp2 hpq hk
  rcases hcase with ⟨hkℓ, htop⟩ | ⟨hkℓ, f, f', hf, hf', hQf, hQf', hff'⟩
  ·
    exfalso
    have hWuniv : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by
      rw [← Finset.iSup_coe, Finset.coe_univ, iSup_univ]
    have hWtype : IsPlusType (Q.comp (⨆ j, U j).subtype) ↔ Even k := by
      have h := hF₀.toIsPlaneSystem.isPlusType_biSup_iff (Finset.univ : Finset (Fin k))
      rwa [hWuniv, Finset.card_univ, Fintype.card_fin] at h
    have hQtype : IsPlusType Q ↔ Even k := by
      rw [← isPlusType_comp_top_iff, ← htop, hWtype]
    rw [hkℓ] at hQtype
    by_cases he : Even ℓ
    · exact (Nat.not_even_iff_odd.mpr (htype.mp (hQtype.mpr he))) he
    · exact he (hQtype.mp (htype.mpr (Nat.not_even_iff_odd.mp he)))
  · exact ⟨k, U, e, u, c, t, f, f', hF, hkℓ, hf, hf', hQf, hQf', hff'⟩

end CFSG.StandardType.TorDNs

end
