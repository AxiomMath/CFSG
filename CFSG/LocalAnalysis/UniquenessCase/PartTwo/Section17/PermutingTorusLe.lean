module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx17_42.exists_permuting_elemAbelian_le_of_borel {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {f : ℕ} (hB : Inputs1719.BorelChevOver (BarInf L) f)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      IsElemAbelian r E ∧ Permutes E D.T ∧
        CFSG.Open.pRank r C ≤ CFSG.Open.pRank r E :=
  exists_permuting_elemAbelian_le_of_calC_of_borel (D := D) (L := L) (X := X) (C := C)
    (n := f) ctx.mem_calC ctx.X_eq hB ctx.cartan hr hr2

theorem Ctx17_42.exists_permuting_elemAbelian_le {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ∧
      IsElemAbelian r E ∧ Permutes E D.T ∧
        CFSG.Open.pRank r C ≤ CFSG.Open.pRank r E :=
  Ctx17_42.exists_permuting_elemAbelian_le_of_borel ctx
    (Inputs1719.BorelChevOver.of_chev hK3 ctx.chev) hr hr2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
