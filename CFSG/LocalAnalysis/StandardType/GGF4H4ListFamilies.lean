module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Pieces
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGF4TagClassical (t : LargeEvenLieTag) : Prop :=
  t = .B ∨ t = .C ∨ t = .D ∨ t = .twD

@[expose] def GGF4TagLinear (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA

@[expose] def GGF4TagExc (t : LargeEvenLieTag) : Prop :=
  t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twE6

@[expose] def GGF4TagSmall (t : LargeEvenLieTag) : Prop :=
  ¬ GGF4TagClassical t ∧ ¬ GGF4TagLinear t ∧ ¬ GGF4TagExc t

@[expose] def GGF4H4ListSp
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks,
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGF4TagClassical lab.tag →
        GGHasLabel lab (K ⧸ Subgroup.center K) → GGF4NbrList p K

@[expose] def GGF4H4ListLin
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks,
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGF4TagLinear lab.tag →
        GGHasLabel lab (K ⧸ Subgroup.center K) → GGF4NbrList p K

@[expose] def GGF4H4ListExc
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks,
      ∀ lab : LargeEvenLabel, GGF4TagExc lab.tag →
        GGHasLabel lab (K ⧸ Subgroup.center K) → False

@[expose] def GGF4H4ListSmall
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks,
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGF4TagSmall lab.tag →
        GGHasLabel lab (K ⧸ Subgroup.center K) → False

theorem ggF4H4List_of_families
    (h1 : GGF4H4ListSp) (h2 : GGF4H4ListLin) (h3 : GGF4H4ListExc) (h4 : GGF4H4ListSmall) :
    GGF4H4List := by
  intro G _ _ p B Bs x L D J ks hres hB K hK
  have hInn : GGInnerDiagAll p B Bs x L D J := hres.1.1.2.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  obtain ⟨lab, hΛ, hlab, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y K hnb)
  by_cases hc : GGF4TagClassical lab.tag
  · exact h1 G p B Bs x L D J ks hres hB K hK lab hΛ hc hlab
  by_cases hl : GGF4TagLinear lab.tag
  · exact h2 G p B Bs x L D J ks hres hB K hK lab hΛ hl hlab
  by_cases he : GGF4TagExc lab.tag
  · exact (h3 G p B Bs x L D J ks hres hB K hK lab he hlab).elim
  · exact (h4 G p B Bs x L D J ks hres hB K hK lab hΛ ⟨hc, hl, he⟩ hlab).elim

end CFSG.StandardType

end
