module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCTest
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_bigC_holds
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (M : GGQ2LDatum 3 Bs L x) (hC : M.ShapeC)
    (hRig : GGLabelRigidInput) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hmark : GGQ2TBMarked 3 L lab)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hcard : Fintype.card M.Λ = lab.rank := by
    obtain ⟨e, -⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa [GGQ2LabelWeyl, htag] using hMW
    simpa using (Fintype.card_congr e).symm
  have hdim : Module.finrank (ZMod 3) M.V = lab.rank + 1 := by
    rw [hC.2.2.2.1, hcard]
  let bV : Module.Basis (Fin (lab.rank + 1)) (ZMod 3) M.V :=
    Module.finBasisOfFinrankEq (ZMod 3) M.V hdim
  let κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1) := bV.equivFun
  refine ggQ2s08_cell_of_test_Q hLB hP hΓi hTBN hS hI1 hCav M κ rfl rfl
    (fun A => ∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
      R ≤ A → 8 * Nat.card R < 3 ^ ((lab.rank - 1) * (lab.rank - 2) / 2))
    (ggQ2s08_bigC_bound hTBW hCen hOut hS hnc M hC hlab hmark.2.2 hInn hMW h12 κ)
    (fun _ _ => False) ?_ g φ hInd hRefl (fun _ _ _ _ hF => hF.elim)
  intro A Mg hT hPA r hr hrr hrx t ht htr htx
  exact Or.inl (ggQ2s08_bigC_test hKG M hC hlab hMW htag h3 h12 κ hT hPA
    hr hrr hrx ht htr htx)

end CFSG.StandardType

end
