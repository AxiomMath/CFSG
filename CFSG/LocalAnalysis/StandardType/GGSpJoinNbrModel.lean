module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofJoin
public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProof
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBLevi
import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic CFSG.Open

section Inputs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSpNbrAt (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (m f : ℕ) (y : G)
    (K : Subgroup G) (y' : G) (K' : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ GGTypeCNbr p B Bs x L D J (m + 1) f y K ∧ GGNbr p B x D J y' K' ∧
    ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs

end Inputs

@[expose] def GGSpNbrCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (y : G) (K : Subgroup G) (y' : G) (K' : Subgroup G),
    GGSpNbrAt p B Bs x L D J m f y K y' K' →
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) ≤ p

section Pieces

variable {G : Type} [Group G]

theorem largeEvenRawDatum_elim_const {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun (R : Type) [Group R] _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hq)

theorem largeEvenMarking_elim_const {X : Type*} [Group X] {Q : Prop}
    (h : LargeEvenMarking X (fun _ _ _ _ _ _ => Q)) : Q := by
  obtain ⟨-, lab, -, hraw⟩ := h
  exact largeEvenRawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, hθ⟩ := hq
      exact hθ) hraw)

theorem GGInnerDiagOn.le_normalizer {Bs X : Subgroup G} (h : GGInnerDiagOn Bs X) :
    Bs ≤ Subgroup.normalizer (X : Set G) :=
  largeEvenMarking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h)

variable [Finite G]

theorem pow_le_card_of_weylOfType_B {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {n : ℕ} (hn : 2 ≤ n) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B n) A) : p ^ n ≤ Nat.card Bs := by
  obtain ⟨e, -⟩ := hA
  obtain ⟨S₀, hS₀, hcard⟩ := exists_elemAbelian_two_coxeterB n hn
  let f : (CoxeterMatrix.B n).Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hS : IsElemAbelian 2 (S₀.map f) := hS₀.map f
  have hcard' : 2 ^ n ≤ Nat.card (S₀.map f) := by
    rw [Subgroup.card_map_of_injective hf]
    exact hcard
  exact pow_le_card_of_elemAbelian_two hp hp2 hBs hS hcard'

end Pieces

end CFSG.StandardType
