module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSuppliers

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

abbrev QTwoCell : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup G → Finset (Subgroup G) → Prop

@[expose] def QTwoCell.compl (cell : QTwoCell) : QTwoCell :=
  fun G _ _ L 𝒦 => ¬ cell G L 𝒦

@[expose] def qtwoOrthL : QTwoCell :=
  fun _ _ _ L _ => ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
    GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧ lab.n = 1 ∧ (lab.tag = .D ∨ lab.tag = .twD)

section Producer


@[expose] def GGSecFivePhanDQTwoAtCell (R : ℕ → Prop) (cell : QTwoCell) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        cell G L 𝒦 →
        GGSecFiveData p B x L D J ∨
          ∃ (U : Fin m → Subgroup G) (W : Fin m → Fin m → Subgroup G),
            QTwoWeakPhanSystemD (GaloisField 2 2) m (ggG0 p B x L D J) U W

theorem GGSecFivePhanDQTwoAt.of_cells {R : ℕ → Prop} {cell : QTwoCell}
    (h : GGSecFivePhanDQTwoAtCell R cell) (h' : GGSecFivePhanDQTwoAtCell R cell.compl) :
    GGSecFivePhanDQTwoAt R := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' hm hM hsix
  by_cases hc : cell G L 𝒦
  · exact h G p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' hm hM hsix hc
  · exact h' G p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' hm hM hsix hc

@[expose] def QTwoFrameAt {G : Type} [Group G] [Finite G] (Bs X : Subgroup G) {ι : Type}
    (M : CoxeterMatrix ι) (A : Subgroup (MulAut ↥Bs)) (e : M.Group ≃* ↥A) {m : ℕ}
    (e' : Fin m ≃ ι) : Prop :=
  ∃ w₀ : M.Group, ∀ i : Fin m, (i : ℕ) ≠ 0 →
    ((e (w₀ * M.simple (e' i) * w₀⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs

@[expose] def GGQTwoCellInputOn (R : ℕ → Prop) (cell : QTwoCell) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        cell G L 𝒦 → ∃ X : Subgroup G,
          QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e ∧
            QTwoFrameAt Bs X M (ggAutomizerJoin L Bs 𝒦) e e' ∧ X ≤ ggG0 p B x L D J

@[expose] def GGQTwoCellInput (cell : QTwoCell) : Prop :=
  GGQTwoCellInputOn (fun m => 7 ≤ m) cell

@[expose] def GGQTwoFarInputOn (R : ℕ → Prop) (cell : QTwoCell) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        cell G L 𝒦 → ∀ i k j l : Fin m, ggCoxeterMatrixD m i k = 3 →
          ggCoxeterMatrixD m j l = 3 → ggCoxeterMatrixD m i j = 2 → ggCoxeterMatrixD m i l = 2 →
          ggCoxeterMatrixD m k j = 2 → ggCoxeterMatrixD m k l = 2 →
            ∀ y ∈ qtwoW Bs (qtwoRefl e e') i k, ∀ z ∈ qtwoW Bs (qtwoRefl e e') j l,
              y * z = z * y

@[expose] def GGQTwoFrameInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
          GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) → lab.n = 1 →
          (lab.tag = .D ∨ lab.tag = .twD) →
            lab.rank + 1 = m ∧ QTwoFrameAt Bs L M (ggAutomizerJoin L Bs 𝒦) e e'

@[expose] def GGQTwoFrameInput : Prop :=
  GGQTwoFrameInputOn fun m => 7 ≤ m

end Producer

end CFSG.StandardType.QTwo

end
