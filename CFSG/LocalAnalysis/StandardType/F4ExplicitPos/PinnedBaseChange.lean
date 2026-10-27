module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

namespace CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

variable {τ : Tag} {R S : Type} [Field R] [Field S]

theorem bcGL_list_prod_weylElt
    (f : R →+* S) (l : List ℕ) :
    bcGL f ((l.map fun i => weylElt τ R (τ.idx i) 1).prod) =
      (l.map fun i => weylElt τ S (τ.idx i) 1).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [map_mul, ih, bcGL_weylElt]
    simp

theorem bcGL_pinnedWeyl
    (f : R →+* S) (α : Fin τ.rank → ℤ) :
    bcGL f (pinnedWeyl τ R α) = pinnedWeyl τ S α := by
  unfold pinnedWeyl
  rw [← List.map_reverse, ← List.map_reverse]
  exact bcGL_list_prod_weylElt f ((pinnedData τ α).2.1).reverse

theorem bcGL_pinnedX
    (f : R →+* S) (α : Fin τ.rank → ℤ) (c : R) :
    bcGL f (pinnedX τ R α c) = pinnedX τ S α (f c) := by
  unfold pinnedX
  rw [map_mul, map_mul, map_inv, bcGL_pinnedWeyl, bcGL_xUnit, map_zsmul]

variable {hA : TauCeti.IsFiniteType τ.cartan} {W : Type*} [Group W]

theorem bcGL_canonicalRep (f : R →+* S)
    (cs : CoxeterSystem (CFSG.LieType.RootSystem.coxeterMatrix hA) W) (w : W) :
    bcGL f (canonicalRep cs R w) = canonicalRep cs S w := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced w
  rw [hw, canonicalRep_wordProd (cs := cs) (R := R) hω,
    canonicalRep_wordProd (cs := cs) (R := S) hω]
  exact bcGL_prod_weylElt f ω

theorem map_bcGL_rootSubgroup_le
    (f : R →+* S) (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ R α).map (bcGL f) ≤ rootSubgroup τ S α := by
  rw [rootSubgroup, rootSubgroup, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨c, hc, rfl⟩
  obtain ⟨d, rfl⟩ := hc
  exact ⟨f d, (bcGL_pinnedX f α d).symm⟩

theorem map_bcGL_rootSubgroup_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f)
    (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ R α).map (bcGL f) = rootSubgroup τ S α := by
  refine le_antisymm (map_bcGL_rootSubgroup_le f α) ?_
  rw [rootSubgroup, rootSubgroup, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨c, rfl⟩
  obtain ⟨d, rfl⟩ := hf c
  exact ⟨pinnedX τ R α d, ⟨d, rfl⟩, bcGL_pinnedX f α d⟩

theorem map_bcGL_rootSpan_le
    (f : R →+* S) (T : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ R T).map (bcGL f) ≤ rootSpan τ S T := by
  rw [Subgroup.map_le_iff_le_comap, rootSpan]
  refine iSup_le fun α => iSup_le fun hα => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact (map_bcGL_rootSubgroup_le f α).trans
    ((le_iSup (fun (_ : α ∈ T) => rootSubgroup τ S α) hα).trans
      (le_iSup (fun α => ⨆ (_ : α ∈ T), rootSubgroup τ S α) α))

end CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

end

end
