module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCoords
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBound
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigTest
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRoFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigRoExit
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_bigFull_holds
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (hRig : GGLabelRigidInput)
    (M : GGQ2LDatum 3 Bs L x) (hF : M.ShapeFull) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hmark : GGQ2TBMarked 3 L lab)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hx0 : M.xV ≠ 0 := by
    intro h0
    exact hF.2.2.1 (by rw [h0]; exact M.coSpan.zero_mem)
  have hF3 : lab.tag = .twA → ¬ 3 ∣ lab.rank + 1 := by
    intro htag h3
    rcases ggQ2s08_big_shape_label M hlab hMW hx0 (Or.inl hF) with h | h
    · exact h.2 ⟨htag, h3⟩
    · exact h.1 hF
  obtain ⟨κ, e, s, Mx, H, hMx, hs, hD⟩ := ggQ2s08_big_coords M hF hlab hMW
  have hℓ : 9 ≤ lab.rank := hlab.2.2
  have hΓ : GGQ2GammaX 3 B Bs x L D J := hΓi hS rfl hI1 hCav
  let W : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :=
    Subgroup.closure (Set.range s)
  have hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W :=
    ggQ2Cell_map_automizer_L M κ e s hs
  let P : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) → Prop := fun A =>
    (∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
        R ≤ A → 8 * Nat.card R < 3 ^ ((lab.rank + 1) * lab.rank / 2)) ∧
      (∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
        R ≤ A → (∀ a ∈ R, ∀ h ∈ H, a h ∈ H) →
        8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2))
  have hPA : P ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) := by
    obtain ⟨h1, h2⟩ := ggQ2s08_big_bound hTBW hCen hOut hS hnc M hF hlab hmark.2.2 hInn hMW κ
    exact ⟨h1, fun R hR hpres => h2 R H hR hD.hH hpres⟩
  let Q : (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) →
      (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)) → Prop := fun r t =>
    GGQ2S08CoreRO (N := lab.rank + 1)
      (Subgroup.closure
        (((Subgroup.closure (Set.range s)) :
          Set (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))) ∪ {r, t}))
      (Subgroup.closure (Set.range s)) r (κ M.xV)
  have htest : ∀ A Mg : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
      TestHyp W (κ M.xV) A Mg → P A →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (κ M.xV) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (κ M.xV) t → t ∈ Mg ∨ Q r t := by
    intro A Mg hT hPAT r hr hrr hrx t ht htr htx
    exact ggQ2s08_big_test hKG hℓ hD hT hPAT.1 hPAT.2 hr hrr hrx ht htr htx
  have hQ : ∀ r ∈ (ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
        (ggQ2CellLin M κ), IsRefl r → ¬ FixesLine (κ M.xV) r →
        Q r (ggQ2CellLin M κ φ) →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    intro r hr hrr hrx hQrt
    refine ggQ2s08_big_roExit hLB hP hS hΓ hCav M hlab hMW hF3 κ e s Mx H hMx hs hD ?_
      g φ hInd hr ?_
    · intro f hf htag hev h3
      exact ggQ2s08_roComponents_full hRig hS M hmark.2.2 ⟨htag, hmark.1⟩ hlab hMW h3 f hf
    · exact hQrt
  exact ggQ2s08_cell_of_test_Q hLB hP hΓi hTBN hS hI1 hCav M κ rfl hW P hPA Q htest
    g φ hInd hRefl hQ

end CFSG.StandardType

end
