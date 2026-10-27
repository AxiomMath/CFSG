module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart29
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3Unconditional

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.B3Pinned

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.F4ExplicitPos.B3Unconditional

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_exceptionalEndo_weylElement
    (i : Fin F4.tag.rank) :
    f4_exceptionalEndo K (weylElement F4.tag K i) = weylElement F4.tag K (F4.perm i) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2
  have hdec : weylElement F4.tag K i =
      xElement i 1 * yElement i (-1) * xElement i 1 := by
    refine Subtype.ext ?_
    change weylElt F4.tag K i 1 =
      xUnit F4.tag K i 1 * yUnit F4.tag K i (-1) * xUnit F4.tag K i 1
    exact CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul i 1
  have hdec' : weylElement F4.tag K (F4.perm i) =
      xElement (F4.perm i) 1 * yElement (F4.perm i) (-1) * xElement (F4.perm i) 1 := by
    refine Subtype.ext ?_
    change weylElt F4.tag K (F4.perm i) 1 =
      xUnit F4.tag K (F4.perm i) 1 * yUnit F4.tag K (F4.perm i) (-1) *
        xUnit F4.tag K (F4.perm i) 1
    exact CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul (F4.perm i) 1
  rw [hdec, hdec', map_mul, map_mul, f4_exceptionalEndo_xElement,
    f4_exceptionalEndo_yElement, show ((1 : K) ^ F4.exponent i) = 1 from one_pow _,
    show ((-1 : K) ^ F4.exponent i) = -1 from by rw [hneg, one_pow]]

theorem f4_exceptionalEndo_wordWeylElement
    (w : List ℕ) :
    f4_exceptionalEndo K (wordWeylElement (t := F4) (K := K) w) =
      wordWeylElement (t := F4) (K := K)
        (w.map fun i => ((F4.perm (F4.tag.idx i) : Fin F4.tag.rank) : ℕ)) := by
  rw [wordWeylElement, wordWeylElement, map_list_prod, List.map_reverse, List.map_map,
    List.map_map]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, f4_exceptionalEndo_weylElement, Function.comp_apply, idx_perm]

theorem f4_exceptionalEndo_pinnedX
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : K) :
    f4_exceptionalEndo K ⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
      ⟨pinnedX F4.tag K (F4.dualRoot α) (c ^ F4.exponent (pinnedData F4.tag α).1),
        pinnedX_mem_adjointGroup _ _⟩ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set j := (pinnedData F4.tag α).1
  set w := (pinnedData F4.tag α).2.1
  have hdec : (⟨pinnedX F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag K) =
      wordWeylElement (t := F4) (K := K) w * xElement j c *
        (wordWeylElement (t := F4) (K := K) w)⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordWeylElement]
    rw [pinnedX_eq_of_two_eq_zero h2]
    rfl
  rw [hdec, map_mul, map_mul, map_inv, f4_exceptionalEndo_wordWeylElement,
    f4_exceptionalEndo_xElement]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordWeylElement]
  rw [show (xElement (F4.perm j) (c ^ F4.exponent j) : ModGL F4.tag K) =
      pinnedX F4.tag K (Pi.single (F4.perm j) 1) (c ^ F4.exponent j) from
        (pinnedX_single F4.tag K _ _).symm,
    prod_weylElt_conj_pinnedX_of_two_eq_zero h2 _ (isRoot_single _ _), ← dualRoot_single,
    dualRoot_foldl_reflect F4 w (isRoot_single _ _), foldl_reflect_pinnedData hα]

section B3

open CFSG.Open CFSG.LieType.Steinberg CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.LieEmbed

noncomputable def f4EndoF4
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(adjointGroup .F4 K) →* ↥(adjointGroup .F4 K) :=
  f4_exceptionalEndo K

@[simp] theorem f4EndoF4_apply
    (g : ↥(adjointGroup .F4 K)) :
    f4EndoF4 K g = f4_exceptionalEndo K g :=
  rfl

theorem c3RootSet_eq_c3LeviRoots :
    C3Range.c3RootSet = CFSG.SeitzReduction.F4Pilot.c3LeviRoots := by
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet]
  exact CFSG.SeitzReduction.F4Pilot.image_c3ToF4_roots

end B3
end CFSG.StandardType.F4ExplicitPos.B3Pinned
end

end
