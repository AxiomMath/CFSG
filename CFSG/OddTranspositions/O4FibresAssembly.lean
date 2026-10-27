module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.SymmetricFiveTranspositions
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PSL2FieldAutFixed

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.GroupTheory
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] noncomputable def starImage (hC : HypothesisC D) (d : G)
    (hd : d ∈ DalphaStar D hC.alpha) :
    Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) :=
  QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
    ⟨d, Subgroup.subset_closure hd⟩

theorem DalphaStar_subset_X_of_singleton_fibres (hC : HypothesisC D)
    {X : Subgroup G}
    {e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5)}
    (hIm : e '' imageClass hC = transpositions)
    {Wset : Set X}
    (hWmem : ∀ w ∈ Wset, (w : G) ∈ DalphaStar D hC.alpha)
    (hWcover : ∀ τ ∈ transpositions, ∃ (w : X) (hw : w ∈ Wset),
      e (starImage hC (w : G) (hWmem w hw)) = τ)
    (hfib : ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
      (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
      e (starImage hC d hd) = e (starImage hC d' hd') → d = d') :
    DalphaStar D hC.alpha ⊆ (X : Set G) := by
  intro d hd
  have hdIm : e (starImage hC d hd) ∈ transpositions := by
    rw [← hIm]
    refine ⟨starImage hC d hd, ?_, rfl⟩
    exact ⟨⟨d, Subgroup.subset_closure hd⟩, (mem_DstarH_iff hC).mpr hd, rfl⟩
  obtain ⟨w, hw, hwimg⟩ := hWcover _ hdIm
  have hdweq : d = (w : G) :=
    hfib d hd (w : G) (hWmem w hw) hwimg.symm
  rw [hdweq]
  exact w.property

end CFSG.OddTranspositions
