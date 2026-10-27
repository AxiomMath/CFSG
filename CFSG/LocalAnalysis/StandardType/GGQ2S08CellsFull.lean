module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SmallCells
public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoordsExc
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

@[expose] def GGQ2S08LinTest {n : ℕ} {ι : Type} (S : ι → (Vn n ≃ₗ[ZMod 3] Vn n)) (x₀ : Vn n) :
    Prop :=
  ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n), TestHyp (Subgroup.closure (Set.range S)) x₀ A Mg →
    ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r → ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → t ∈ Mg

private theorem ggQ2s08_weyl_at_rank {Λ : Type} {M : CoxeterMatrix Λ} {r n : ℕ} (hn : n = r)
    (X : (k : ℕ) → CoxeterMatrix (Fin k)) (h : ∃ e : Fin n ≃ Λ, M = (X n).reindex e) :
    ∃ e : Fin r ≃ Λ, M = (X r).reindex e := by
  subst hn
  exact h

theorem ggQ2s08_cellBC_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {r : ℕ} (hr4 : 4 ≤ r) (hr8 : r ≤ 8)
    (htest : GGQ2S08LinTest (bcFullS r) (frameFullX r)) {t : LargeEvenLieTag}
    (ht : t = .B ∨ t = .C) : GGQ2S08Cell t r .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin r ≃ M.Λ, M.coxeter = (CoxeterMatrix.B r).reindex e := by
    refine ggQ2s08_weyl_at_rank hrank CoxeterMatrix.B ?_
    rcases ht with rfl | rfl
    · simpa only [GGQ2LabelWeyl, htag] using hWeyl
    · simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  have hx : M.xV ∉ M.coSpan := hShape.2.2.1
  have hcoords : ∃ κ : M.V ≃ₗ[ZMod 3] Vn (r + 1), κ M.xV = frameFullX r ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = bcFullS r k v := by
    rcases ggQ2_cartan_B e he M.isCartan with hC | hC
    · exact ggQ2_fullCoords_B r hr4 hr8 M hx e hC
    · exact ggQ2_fullCoords_C r hr4 hr8 M hx e hC
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e (bcFullS r) (frameFullX r)
    hcoords htest g φ hInd hRefl

theorem ggQ2s08_cellD_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {r : ℕ} (hr4 : 4 ≤ r) (hr8 : r ≤ 8)
    (htest : GGQ2S08LinTest (dFullS r) (frameFullX r)) {t : LargeEvenLieTag}
    (ht : t = .D ∨ t = .twD) : GGQ2S08Cell t r .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin r ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD r).reindex e := by
    refine ggQ2s08_weyl_at_rank hrank ggCoxeterMatrixD ?_
    rcases ht with rfl | rfl
    · simpa only [GGQ2LabelWeyl, htag] using hWeyl
    · simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e (dFullS r) (frameFullX r)
    (ggQ2_fullCoords_D r hr4 hr8 M hShape.2.2.1 e (ggQ2_cartan_D e he M.isCartan)) htest g φ
    hInd hRefl

theorem ggQ2s08_cellA4_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr)
    (htest : GGQ2S08LinTest (aFullS 5) (aFullX 5)) : GGQ2S08Cell .twA 4 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin 4 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 4).reindex e :=
    ggQ2s08_weyl_at_rank hrank CoxeterMatrix.A (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e (aFullS 5) (aFullX 5)
    (ggQ2_fullCoords_A5 M hShape.2.2.1 e (ggQ2_cartan_A e he M.isCartan)) htest g φ hInd hRefl

theorem ggQ2s08_cellF4_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr)
    (htest : GGQ2S08LinTest f4FullS f4FullX) : GGQ2S08Cell .F4 0 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin 4 ≃ M.Λ, M.coxeter = CoxeterMatrix.F₄.reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  have hx : M.xV ∉ M.coSpan := hShape.2.2.1
  have hcoords : ∃ κ : M.V ≃ₗ[ZMod 3] Vn 5, κ M.xV = f4FullX ∧
      ∀ k v, κ (ggLin (p := 3) M.model (M.simple (e k)) (κ.symm v)) = f4FullS k v := by
    rcases ggQ2_cartan_F₄ e he M.isCartan with hC | hC
    · exact ggQ2_fullCoords_F4 M hx e hC
    · exact ggQ2_fullCoords_F4t M hx e
        (fun i j => (hC i j).trans (Matrix.transpose_apply _ _ _).symm)
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e f4FullS f4FullX hcoords htest g φ
    hInd hRefl

theorem ggQ2s08_cellE7_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr)
    (htest : GGQ2S08LinTest e7FullS e7FullX) : GGQ2S08Cell .E7 0 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₇.reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e e7FullS e7FullX
    (ggQ2_fullCoords_E7 M hShape.2.2.1 e (ggQ2_cartan_E₇ e he M.isCartan)) htest g φ hInd hRefl

theorem ggQ2s08_cellE8_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr)
    (htest : GGQ2S08LinTest e8FullS e8FullX) : GGQ2S08Cell .E8 0 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  have hW : ∃ e : Fin 8 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₈.reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e e8FullS e8FullX
    (ggQ2_fullCoords_E8 M hShape.2.2.1 e (ggQ2_cartan_E₈ e he M.isCartan)) htest g φ hInd hRefl

end CFSG.StandardType

end
