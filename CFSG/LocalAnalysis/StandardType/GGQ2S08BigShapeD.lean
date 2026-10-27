module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDTest
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_bigD_holds
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (M : GGQ2LDatum 3 Bs L x) (hD : M.ShapeD)
    (hRig : GGLabelRigidInput) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hmark : GGQ2TBMarked 3 L lab)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 := by
      apply M.model.injective
      simpa [GGQ2LDatum.xV] using h0
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := by
      simpa using Additive.ofMul.injective h1
    exact congrArg (fun b : ↥Bs => (b : G)) h2
  have hMW' : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa only [GGQ2LabelWeyl, htag] using hMW
  have hcardΛ : Fintype.card M.Λ = lab.rank := by
    obtain ⟨e, -⟩ := hMW'
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
  have hfin : Module.finrank (ZMod 3) M.V = lab.rank := by
    rw [← finrank_top (ZMod 3) M.V, ← hD.2.2, ← hcardΛ]
    exact finrank_span_eq_card hD.2.1
  haveI : Finite M.V := Finite.of_equiv _ M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  let κ : M.V ≃ₗ[ZMod 3] Vn lab.rank :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_fin_fun])
  exact ggQ2s08_cell_of_test_Q (hLB := hLB) (hP := hP) (hΓi := hΓi) (hTBN := hTBN)
    (hS := hS) (hI1 := hI1) (hCav := hCav) (M := M) (κ := κ) (hκx := rfl) (hW := rfl)
    (P := fun A => ∀ R : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank),
      R ≤ A → 8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2))
    (hPA := ggQ2s08_bigD_bound hTBW hCen hOut hS hnc M hD hlab hmark.2.2 hInn hMW h12 κ)
    (Q := fun _ _ => False)
    (htest := fun A Mg hT hPA' r hr hrr hrx t ht htr htx =>
      False.elim (ggQ2s08_bigD_test hKG M hD hx0 hlab hMW htag h3 h12 κ hT hPA'
        hr hrr hrx ht htr htx))
    (g := g) (φ := φ) (hInd := hInd) (hRefl := hRefl)
    (hQ := fun r _ _ _ hF => False.elim hF)

end CFSG.StandardType

end
