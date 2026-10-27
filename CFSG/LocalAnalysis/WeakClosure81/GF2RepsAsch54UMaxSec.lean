module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMax
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ThmA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


theorem not_hasCompFactor_isCalL0_of_sectionalTwoRankLE
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) {Q : Type} [Group Q] [Finite Q]
    {L : Subgroup Q} [L.Normal] (hK : CFSG.Open.IsKGroup Q) (hLs : IsSimpleGroup ↥L)
    (hLnab : ∃ a b : ↥L, a * b ≠ b * a) (hC : centralizer (L : Set Q) = ⊥)
    (hE : CFSG.GH74.SectionalTwoRankLE ↥L 2) (X : Subgroup Q) : ¬ HasCompFactor X IsCalL0 := by
  have hKL : CFSG.Open.IsKGroup ↥L := hK.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer (hS _ hLs hLnab hcat))
  exact not_hasCompFactor_of_sectionalTwoRankLE isCalL0_nonabelian_not_sectionalTwoRankLE hq hE X

theorem asch80ThmA54Case_of_sectionalTwoRankLE (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → CFSG.GH74.SectionalTwoRankLE X 2)
    (hsh : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      P X → ¬ IsCalL0 X → Shape54Socle X) :
    Asch80ThmA54Case P := by
  intro Q _ _ L T M hK hLn hLs hLnab hC hPL hL0 _ _ _
  exact Or.inr ⟨not_hasCompFactor_isCalL0_of_sectionalTwoRankLE hS hK hLs hLnab hC (hP _ hPL) M,
    shape54_of_shape54Socle T hLs hLnab hC (hsh _ hLs hLnab hPL hL0)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
