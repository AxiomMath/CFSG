module

public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.LieType.Chevalley.RootGramDet
public import CFSG.LieType.Chevalley.NonClosedRootCensus

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TauCeti

open scoped commutatorElement

open Matrix

theorem famD4Index_gram_std {τ : Tag} :
    (Matrix.of fun i j : Fin τ.rank =>
      iform (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))) = τ.symmetrizedCartan := by
  ext i j
  simp only [Matrix.of_apply, iform]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem famD4Index_det_std_E8 : (Tag.symmetrizedCartan Tag.E8).det = 1 := by
  have h : Tag.symmetrizedCartan Tag.E8 = Tag.cartan Tag.E8 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [h]
  have hdet : (Tag.cartan Tag.E8).det = (CartanMatrix.E 8).det := by
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [hdet, CartanMatrix.E_det (show 3 ≤ 8 by norm_num)]
  norm_num

theorem famD4Index_toRat_sum {τ : Tag} {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (f : ι → Fin τ.rank → ℤ) :
    CFSG.HardMathSupport.Timmesfeld.RootAut.toRat (∑ i ∈ s, c i • f i) =
      ∑ i ∈ s, (c i : ℚ) • CFSG.HardMathSupport.Timmesfeld.RootAut.toRat (f i) := by
  funext k
  simp [CFSG.HardMathSupport.Timmesfeld.RootAut.toRat, Finset.sum_apply]

theorem famD4Index_linearIndependent_simpleRoots_int {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) :
    LinearIndependent ℤ (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hQ := Fintype.linearIndependent_iff.1 (linearIndependent_toRat hΨ)
  have hcQ : ∑ β : simpleRoots Ψ, ((c β : ℤ) : ℚ) • toRat (β : Fin τ.rank → ℤ) = 0 := by
    have h := congrArg toRat hc
    rw [show toRat (0 : Fin τ.rank → ℤ) = 0 by ext k; simp [toRat]] at h
    rw [famD4Index_toRat_sum (Finset.univ : Finset ↥(simpleRoots Ψ)) c
      (fun i : ↥(simpleRoots Ψ) => (i : Fin τ.rank → ℤ))] at h
    simpa using h
  intro β
  have := hQ (fun β => ((c β : ℤ) : ℚ)) hcQ β
  exact_mod_cast this

theorem famD4Index_finrank_span_simpleRoots {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) :
    Module.finrank ℤ (Submodule.span ℤ (simpleRoots Ψ : Set (Fin τ.rank → ℤ))) =
      (simpleRoots Ψ).card := by
  classical
  have h := finrank_span_eq_card (famD4Index_linearIndependent_simpleRoots_int hΨ)
  rw [show (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) =
      Set.range (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ)) from by
    ext x; simp]
  simpa [Fintype.card_coe] using h

theorem famD4Index_finrank_span_eq_compRank {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  have hspan : Submodule.span ℤ Ψ =
      Submodule.span ℤ (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) := by
    refine le_antisymm (Submodule.span_le.2 fun α hα => ?_) (Submodule.span_mono ?_)
    · obtain ⟨c, hc⟩ := exists_coords hΨ hα
      rw [hc]
      exact Submodule.sum_mem _ fun β hβ => Submodule.smul_mem _ _ (Submodule.subset_span hβ)
    · intro β hβ; exact simpleRoots_subset hβ
  rw [hspan, famD4Index_finrank_span_simpleRoots hΨ, compRank_eq_card hΨ]

theorem famD4Index_det_gram_simpleRoots {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : compRank Ψ = 4) (hc : Ψ.ncard = 24) :
    (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin τ.rank → ℤ) γ).det = 4 := by
  classical
  have hne : Ψ.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hc
  obtain ⟨t, e, ht, hts, he, hcard, hN⟩ := exists_dynkinType (Or.inr hτ) hΨ hne
  have hrank : t.rank = 4 := by
    rw [← hcard, ← compRank_eq_card hΨ, hr]
  have hnum : t.numRoots = 24 := by rw [← hN, hc]
  have htD : t = .D 4 := by
    rcases t with n | n | n | n | _ | _ | _ | _ | _
    · simp only [TauCeti.DynkinType.rank_A] at hrank
      rw [hrank] at hnum
      simp only [TauCeti.DynkinType.numRoots_A] at hnum
      norm_num at hnum
    · simp only [TauCeti.DynkinType.rank_B] at hrank
      rw [hrank] at hnum
      simp only [TauCeti.DynkinType.numRoots_B] at hnum
      norm_num at hnum
    · simp only [TauCeti.DynkinType.rank_C] at hrank
      rw [hrank] at hnum
      simp only [TauCeti.DynkinType.numRoots_C] at hnum
      norm_num at hnum
    · simp only [TauCeti.DynkinType.rank_D] at hrank
      rw [hrank]
    · simp only [TauCeti.DynkinType.rank_E6] at hrank; omega
    · simp only [TauCeti.DynkinType.rank_E7] at hrank; omega
    · simp only [TauCeti.DynkinType.rank_E8] at hrank; omega
    · simp only [TauCeti.DynkinType.rank_F4] at hrank
      simp only [TauCeti.DynkinType.numRoots_F4] at hnum
      norm_num at hnum
    · simp only [TauCeti.DynkinType.rank_G2] at hrank; omega
  have hmat : (Matrix.of fun β γ : simpleRoots Ψ => iform (β : Fin τ.rank → ℤ) γ) =
      t.cartanMatrix.submatrix e e := by
    ext β γ
    rw [Matrix.of_apply, Matrix.submatrix_apply, he]
  rw [hmat, Matrix.det_submatrix_equiv_self e t.cartanMatrix, htD,
    TauCeti.DynkinType.cartanMatrix_D]
  exact CartanMatrix.D_det (by norm_num)

end CFSG.StandardType.TableCRes
