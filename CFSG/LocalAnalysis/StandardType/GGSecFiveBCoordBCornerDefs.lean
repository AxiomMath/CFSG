module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def CornerRow {r : ℕ} (W : Submodule F (V r)) (u : V r) (c : Code r) : Prop :=
  (∃ i, Pi.single i 1 ∈ W ∧ (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧
      c = .zero (Finset.univ.erase i)) ∨
    (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
      (∀ i, u i ≠ 0 ↔ i = k ∨ i = l) ∧ c = .zero ((Finset.univ.erase k).erase l) ∧ 5 ≤ r) ∨
    (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧ (∀ i, u i ≠ 0) ∧
      (c = .extension u ∨ c = .extension (-u)) ∧ 5 ≤ r) ∨
    (∃ k, (∀ v, v ∈ W ↔ v k = 0) ∧ (∀ i, u i = 0 ↔ i = k) ∧
      (c = .extension u ∨ c = .extension (-u)) ∧ 6 ≤ r)

@[expose] def CornerRowRest {r : ℕ} (W : Submodule F (V r)) (u : V r) (c : Code r) : Prop :=
  (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
      (∀ i, u i ≠ 0 ↔ i = k ∨ i = l) ∧ c = .zero ((Finset.univ.erase k).erase l) ∧ 5 ≤ r) ∨
    (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧ (∀ i, u i ≠ 0) ∧
      (c = .extension u ∨ c = .extension (-u)) ∧ 5 ≤ r) ∨
    (∃ k, (∀ v, v ∈ W ↔ v k = 0) ∧ (∀ i, u i = 0 ↔ i = k) ∧
      (c = .extension u ∨ c = .extension (-u)) ∧ 6 ≤ r)

end GGQ2Frame.PlaneRaw

variable {G : Type} [Group G]

@[expose] def GGSecFiveBCoordBCornerRows (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (r : ℕ) : Prop :=
  ∃ (R : GGQ2Frame.Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L)
      (GGQ2Frame.planeEntry .symplectic r)) (z : ↥(Bs.subgroupOf L))
    (c : GGQ2Frame.PlaneRaw.Code r),
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G) ∧
      GGQ2Frame.PlaneRaw.admissible .symplectic c ∧ J = (R.component c).map L.subtype ∧
      GGQ2Frame.PlaneRaw.CornerRow (ggLinImage (p := 3) R.coord (B.subgroupOf L))
        (R.coord (Additive.ofMul z)) c

@[expose] def GGSecFiveBCoordBCornerRowsRest (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (r : ℕ) : Prop :=
  ∃ (R : GGQ2Frame.Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L)
      (GGQ2Frame.planeEntry .symplectic r)) (z : ↥(Bs.subgroupOf L))
    (c : GGQ2Frame.PlaneRaw.Code r),
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G) ∧
      GGQ2Frame.PlaneRaw.admissible .symplectic c ∧ J = (R.component c).map L.subtype ∧
      GGQ2Frame.PlaneRaw.CornerRowRest (ggLinImage (p := 3) R.coord (B.subgroupOf L))
        (R.coord (Additive.ofMul z)) c

section Inputs


@[expose] def GGSecFiveBCoordBProperRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (n : ℕ) (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e → 4 ≤ n →
      ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
          (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) p Bs L →
        B ≠ Bs →
        ((∃ i, i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1)) ∨
          ∃ i j, i ≠ j ∧ i ≠ i0 ∧ j ≠ i0 ∧
            ((∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)) ∨
              ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = (eta b j)⁻¹))) →
        GGSecFiveBCoordBCornerRowsRest B Bs x L D J (n - 1) →
        (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
          ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) →
        ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
