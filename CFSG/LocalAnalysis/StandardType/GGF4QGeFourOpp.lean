module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine

public section

namespace CFSG.StandardType

open CFSG.Assembly

section OppEnd

variable {G : Type} [Group G] [Finite G]

@[expose] def GGF4QGeFourOppEnd (p : ℕ) (Bs : Subgroup G) (x : G) (W : Subgroup (MulAut ↥Bs))
    (z : G) (A : Subgroup G) : Prop :=
  GGFixLineComp Bs z A ∧ z ≠ 1 ∧ Bs ≤ Subgroup.normalizer (A : Set G) ∧
    ggAutomizer A Bs ≤ W ∧ GGWeylReflectionGroup p (ggAutomizer A Bs) ∧
    ∀ w ∈ W, ∀ b : ↥Bs, (b : G) = z → ((w b : ↥Bs) : G) ∉ Subgroup.zpowers x

end OppEnd

@[expose] def GGF4QGeFourOppSpInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → ¬ GGSecFiveTier1Region p B Bs x L D J →
      GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .PSp 3 f L →
        ∃ (z : G) (A : Subgroup G),
          GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
            GGCentralImage .PSp 3 f A

@[expose] def GGF4QGeFourOppOmegaInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → ¬ GGSecFiveTier1Region p B Bs x L D J →
      GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .POmegaMinus 4 f L →
        ∃ (z : G) (A : Subgroup G),
          GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
            GGCentralImage .PSU 6 f A

@[expose] def GGF4QGeFourOppPlusInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → ¬ GGSecFiveTier1Region p B Bs x L D J →
      GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f + 1 → GGCentralImage .POmegaMinus 4 f L →
        p = 5 ∧ f = 2 ∧ ∃ (z : G) (A : Subgroup G),
          GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
            GGCentralImage .PSL 6 2 A

section AltPlaneData

@[expose] def GGF4N2AltPlaneData {G : Type} [Group G] [Finite G]
    (B Bs : Subgroup G) (x : G) (L K : Subgroup G) : Prop :=
  ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (w : CoxeterMatrix.F₄.Group) (n : G),
    GGCoxeterPres 5 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' ∧
      n ∈ L ⊔ K ∧
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs,
        ((((e' (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
              ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) =
          n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs
        ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) : Set G) ∧
      ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
        D' = ggHyperplane Bs
            ((e' (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) :
              ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ⊓
          ggHyperplane Bs
            ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
              ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∧
        J' = LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) ∧
        D' = Subgroup.closure {x, d} ∧ LargeEvenStdSub 5 B x L D' J' ∧
        GGConfig 5 B Bs x L D' J' ∧ GGNbr 5 B x D' J' d A ∧
        A = ggLayerClosure 5 (Subgroup.centralizer ({d} : Set G)) J' ∧
        A.map (MulAut.conj n).toMonoidHom = A ∧ J' ≤ A ∧
        GGHasLabel ⟨.A, 3, 2⟩ (↥J' ⧸ Subgroup.center ↥J') ∧
        Subgroup.center ↥J' = ⊥ ∧
        GGInnerDiagOn Bs A ∧ GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A) ∧
        GGCentralImage .PSL 6 2 A ∧
        GGF4QGeFourOppEnd 5 Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) d A ∧
        ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs ∧
        A ≤ L ⊔ K ∧ L ⊔ K = L ⊔ A ∧
        ∀ (z : G) (Y : Subgroup G), GGNbr 5 B x D' J' z Y →
          GGInnerDiagOn Bs Y ∧
            LargeEvenMarking ↥Y
              (fun lab _ _ _ _ _ => LargeEvenHalfSplit 5 lab (Subgroup.center ↥Y = ⊥))

end AltPlaneData

end CFSG.StandardType

end
