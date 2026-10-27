module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Rep

variable {τ : Tag} {L : Type} [Field L]

@[expose] def wordRep (τ : Tag) (L : Type) [Field L] (ω : List (Fin τ.rank)) : ModGL τ L :=
  (ω.map fun i => weylElt τ L i 1).prod

theorem wordRep_mem_monomial (ω : List (Fin τ.rank)) :
    wordRep τ L ω ∈ monomialSubgroup τ L :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

theorem wordRep_weylImage (ω : List (Fin τ.rank)) :
    weylQuotientHom τ L ⟨wordRep τ L ω, wordRep_mem_monomial ω⟩ = (coxeterSystem τ).wordProd ω :=
  weylQuotientHom_eq (mapsRootLines_list_prod ω)

theorem wordRep_fixed (σ : L ≃+* L) (ω : List (Fin τ.rank)) :
    Units.map (entrywiseHom σ.toRingHom) (wordRep τ L ω) = wordRep τ L ω := by
  unfold wordRep
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => entrywise_weylElt_one σ i)

theorem wordRep_conj_rootSL2 [CharP L 2] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (ω : List (Fin τ.rank)) (A : SL(2, L)) :
    wordRep τ L ω * rootSL2 τ L β A * (wordRep τ L ω)⁻¹ =
      rootSL2 τ L ((coxeterSystem τ).wordProd ω • β) A := by
  have hβ' : IsRoot τ ((coxeterSystem τ).wordProd ω • β) := IsRoot.smul hβ _
  have h : (MulAut.conj (wordRep τ L ω)).toMonoidHom.comp (rootSL2 τ L β) =
      rootSL2 τ L ((coxeterSystem τ).wordProd ω • β) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change wordRep τ L ω * rootSL2 τ L β (uSL c) * (wordRep τ L ω)⁻¹ =
          rootSL2 τ L ((coxeterSystem τ).wordProd ω • β) (uSL c)
        rw [rootSL2_uSL_of_charTwo hβ, rootSL2_uSL_of_charTwo hβ']
        exact list_prod_weylElt_conj_pinnedX_of_charTwo ω hβ c
      · change wordRep τ L ω * rootSL2 τ L β (vSL c) * (wordRep τ L ω)⁻¹ =
          rootSL2 τ L ((coxeterSystem τ).wordProd ω • β) (vSL c)
        rw [rootSL2_vSL_of_charTwo hβ, rootSL2_vSL_of_charTwo hβ', ← smul_neg]
        exact list_prod_weylElt_conj_pinnedX_of_charTwo ω (IsRoot.neg hβ) c
  exact DFunLike.congr_fun h A

end Rep

end CFSG.RankThree.PartOne.KLCE
