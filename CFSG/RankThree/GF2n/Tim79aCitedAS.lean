module

public import CFSG.Open.StatedDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Blueprint Matrix

@[expose] def AschbacherSeitzStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (m f : ℕ), 1 ≤ m → 2 ≤ f →
    Nonempty (A ≃* StatedSp m (GaloisField 2 f)) →
    standardComponentOddCore G = ⊥ → standardComponentIsStandard A →
    2 ≤ pRank 2 (Subgroup.centralizer (A : Set G)) →
    Subgroup.normalClosure (A : Set G) = A ∨
      (m = 1 ∧ f = 2 ∧
        (Nonempty (Subgroup.normalClosure (A : Set G) ≃* alternatingGroup (Fin 9)) ∨
          NativeSporadic.IsSporadic (Subgroup.normalClosure (A : Set G)) .M12 ∨
          NativeSporadic.IsSporadic (Subgroup.normalClosure (A : Set G)) .J2))

@[expose] def AschbacherHJRepresentationStatement : Prop :=
  ∀ (n : ℕ) (ρ : NativeSporadic.J2 →* GL (Fin n) (ZMod 2)), Function.Injective ρ → 12 ≤ n

end CFSG.RankThree.GF2n.Tim79a
