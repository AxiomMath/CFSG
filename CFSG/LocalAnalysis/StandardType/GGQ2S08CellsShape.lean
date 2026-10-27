module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellsFull
public import CFSG.LocalAnalysis.StandardType.GGQ2S08ShapeCoords

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem TestLin.fixesLine_neg {n : ℕ} (x : Vn n) (g : Vn n ≃ₗ[ZMod 3] Vn n) :
    FixesLine (-x) g ↔ FixesLine x g := by
  unfold FixesLine
  rw [map_neg, neg_neg, neg_inj, neg_eq_iff_eq_neg]

theorem TestLin.TestHyp.of_neg {n : ℕ} {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x : Vn n}
    (hT : TestHyp W (-x) A M) : TestHyp W x A M where
  le := hT.le
  W_le := hT.W_le
  noTransv := hT.noTransv
  normW g hg hfix := hT.normW g hg ((fixesLine_neg x g).mpr hfix)
  stab_mem g hg hfix := hT.stab_mem g hg ((fixesLine_neg x g).mpr hfix)

theorem GGQ2S08LinTest.neg {n : ℕ} {ι : Type} {S : ι → (Vn n ≃ₗ[ZMod 3] Vn n)} {x₀ : Vn n}
    (h : GGQ2S08LinTest S x₀) : GGQ2S08LinTest S (-x₀) := by
  intro A Mg hT r hr hrR hrx t ht htR htx
  exact h A Mg hT.of_neg r hr hrR (fun h' => hrx ((fixesLine_neg x₀ r).mpr h')) t ht htR
    (fun h' => htx ((fixesLine_neg x₀ t).mpr h'))

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem ggQ2s08_cell_of_coords_pm (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ} {ι : Type}
    (e : ι ≃ M.Λ) (S : ι → (Vn n ≃ₗ[ZMod 3] Vn n)) (x₀ : Vn n)
    (hcoords : ∃ κ : M.V ≃ₗ[ZMod 3] Vn n, (κ M.xV = x₀ ∨ κ M.xV = -x₀) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v)
    (htest : GGQ2S08LinTest S x₀) (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ)
    (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  obtain ⟨κ, hκx | hκx, hκs⟩ := hcoords
  · exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e S x₀ ⟨κ, hκx, hκs⟩ htest g φ
      hInd hRefl
  · exact ggQ2s08_cell_of_coords hLB hP hΓi hTBN hS hI1 hCav M e S (-x₀) ⟨κ, hκx, hκs⟩
      htest.neg g φ hInd hRefl

theorem ggQ2s08_lab_twA (r : ℕ) {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (labL : LargeEvenLabel) (htag : labL.tag = .twA)
    (hrank : labL.rank = r) (hWeyl : GGQ2LabelWeyl labL M.coxeter) :
    ∃ e : Fin r ≃ M.Λ, ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j := by
  have hW : ∃ e : Fin labL.rank ≃ M.Λ, M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hWeyl
  rw [hrank] at hW
  obtain ⟨e, he⟩ := hW
  exact ⟨e, ggQ2_cartan_A e he M.isCartan⟩

theorem ggQ2s08_lab_twE6 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (labL : LargeEvenLabel) (htag : labL.tag = .twE6)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) :
    ∃ e : Fin 6 ≃ M.Λ, ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₆ i j := by
  have hW : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₆.reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hWeyl
  obtain ⟨e, he⟩ := hW
  exact ⟨e, ggQ2_cartan_E₆ e he M.isCartan⟩

theorem ggQ2s08_cell_of_label (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {t : LargeEvenLieTag} {r : ℕ}
    {s : GGQ2ShapeTag} {ℓ n : ℕ} (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ)
    (hlab : ∀ {G : Type} [Group G] {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x)
      (labL : LargeEvenLabel), labL.tag = t → labL.rank = r → GGQ2LabelWeyl labL M.coxeter →
        ∃ e : Fin ℓ ≃ M.Λ, ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n)) (x₀ : Vn n)
    (hco : ∀ {G : Type} [Group G] {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum 3 Bs L x),
      M.HasShape s → ∀ e : Fin ℓ ≃ M.Λ, (∀ i j, M.cartan (e i) (e j) = C₀ i j) →
        ∃ κ : M.V ≃ₗ[ZMod 3] Vn n, (κ M.xV = x₀ ∨ κ M.xV = -x₀) ∧
          ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v)
    (htest : GGQ2S08LinTest S x₀) : GGQ2S08Cell t r s := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
  obtain ⟨e, hC⟩ := hlab M labL htag hrank hWeyl
  exact ggQ2s08_cell_of_coords_pm hLB hP hΓi hTBN hS hI1 hCav M e S x₀ (hco M hShape e hC) htest
    g φ hInd hRefl

end CFSG.StandardType

end
