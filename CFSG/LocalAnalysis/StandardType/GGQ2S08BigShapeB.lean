module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBTest
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBBound
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_bigB_holds
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB)
    (hRig : GGLabelRigidInput) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hmark : GGQ2TBMarked 3 L lab)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (htag : lab.tag = .twA) (h3 : 3 ∣ lab.rank + 1)
    (h12 : 12 ≤ lab.rank + 1)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hune : (⟨x, M.hx⟩ : ↥Bs) ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  have hx0 : M.xV ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h0)
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hune h2
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hMW' : GGQ2LabelWeyl lab M.coxeter := hMW
  simp only [GGQ2LabelWeyl, htag] at hMW'
  obtain ⟨e, -⟩ := hMW'
  have hcardΛ : Fintype.card M.Λ = lab.rank := by
    calc Fintype.card M.Λ = Fintype.card (Fin lab.rank) := Fintype.card_congr e.symm
      _ = lab.rank := Fintype.card_fin _
  have hdim : Module.finrank (ZMod 3) M.V = lab.rank := by
    rw [ggQ2LD_dim_heart M (Or.inl hB), hcardΛ]
  let κ : M.V ≃ₗ[ZMod 3] Vn lab.rank :=
    LinearEquiv.ofFinrankEq M.V (Vn lab.rank) (by rw [hdim, Module.finrank_fin_fun])
  let P : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank) → Prop :=
    fun A => ∀ R : Subgroup (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank), R ≤ A →
      8 * Nat.card R < 3 ^ ((lab.rank - 1) * (lab.rank - 2) / 2)
  have hPA : P ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) :=
    ggQ2s08_bigB_bound hTBW hCen hOut hS hnc M hB hlab hmark.2.2 hInn hMW h12 κ
  let Q : (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank) →
      (Vn lab.rank ≃ₗ[ZMod 3] Vn lab.rank) → Prop := fun _ _ => False
  refine ggQ2s08_cell_of_test_Q hLB hP hΓi hTBN hS hI1 hCav M κ rfl rfl P hPA Q ?_
    g φ hInd hRefl ?_
  · intro A Mg hT hPA' r hr hrr hrx t ht htr htx
    exact (ggQ2s08_bigB_test hKG M hB hlab hMW htag h3 h12 κ hT hPA' hr hrr hrx
      ht htr htx).elim
  · intro r hr hrr hrx hF
    exact hF.elim

end CFSG.StandardType

end
