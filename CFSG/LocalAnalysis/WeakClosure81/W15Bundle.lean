module

public import CFSG.LocalAnalysis.WeakClosure81.W15Seven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

structure NamedInputs15 (G : Type) [Group G] [Finite G] : Prop where
  thmB : Asc80ThmB
  mult : SchurMultiplierInput
  w122 : W3Lem122Two
  w86 : W3Lem86_1Two G
  w145 : W15Thm145 G

variable {G : Type} [Group G] [Finite G]

namespace NamedInputs15

variable {M V₀ V U S : Subgroup G}

theorem not_le_pCoreOf_centralizer (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) : ¬ V₀ ≤ pCoreOf 2 (centralizer (U : Set G)) :=
  h.not_le_pCoreOf_centralizer hI.thmB hI.mult hI.w122 hS

theorem wClos_eq (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) : E3.wClos V₀ 0 S = V₀ :=
  h.wClos_eq hI.w86 hI.thmB hI.mult hI.w122 hS

end NamedInputs15

end CFSG.LocalAnalysis.WeakClosure81
