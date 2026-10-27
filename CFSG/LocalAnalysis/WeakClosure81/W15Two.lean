module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenPrime
import CFSG.LocalAnalysis.WeakClosure81.W15POne
import CFSG.LocalAnalysis.WeakClosure81.W162TenTwoBMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Inputs15Two (G : Type) [Group G] [Finite G] : Prop where
  named : NamedInputs15 G
  dich : W15Eleven3Dich G
  s4 : W15Eleven3S4 G
  bar : W15Eleven4Bar G

section Certified


theorem fifteen_two {M V₀ V : Subgroup G} (hI : Inputs15Two G) (hS : Std15 G)
    (hyp : Hyp15 M V₀ V) (hm : 1 < mBar M V₀ V hyp.h6.elemAbelian) :
    (mSub V₀ : ℕ∞) < rMV M V := by
  by_contra hcon
  obtain ⟨U, S, h⟩ := exists_cex15 hyp hm (not_lt.1 hcon)
  have hW : W15Eight1 G := w15Eight1_of_namedInputs hI.named
  exact h.false_of_inputs hI.named hW (w15Ten2b_of_eight1 hI.named hW) hI.dich
    hI.s4 hI.bar hS

end Certified

end CFSG.LocalAnalysis.WeakClosure81
