module

public import CFSG.LieType.Chevalley.LatticeWeylGroup
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

theorem wordUnit_mem (τ : Tag) (l : List (Fin τ.rank)) :
    (l.map (reflectUnit τ)).prod ∈ latticeWeylGroup τ := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem wordUnit_apply (τ : Tag) (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    ((l.map (reflectUnit τ)).prod : Module.End ℤ (Fin τ.rank → ℤ)) v = (wordMat τ l) *ᵥ v := by
  induction l generalizing v with
  | nil => simp [wordMat_nil]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih,
      reflectUnit_apply, ← reflMat_mulVec, wordMat_cons, Matrix.mulVec_mulVec]

theorem mem_latticeWeylGroup_of_wordMat {τ : Tag} {g : (Module.End ℤ (Fin τ.rank → ℤ))ˣ}
    (l : List (Fin τ.rank))
    (h : ∀ v, (g : Module.End ℤ (Fin τ.rank → ℤ)) v = (wordMat τ l) *ᵥ v) :
    g ∈ latticeWeylGroup τ := by
  have hg : g = (l.map (reflectUnit τ)).prod :=
    Units.ext (LinearMap.ext fun v => by rw [h, wordUnit_apply])
  rw [hg]
  exact wordUnit_mem τ l

theorem neg_one_mem_latticeWeylGroup {τ : Tag} (l : List (Fin τ.rank)) (h : wordMat τ l = -1) :
    (-1 : (Module.End ℤ (Fin τ.rank → ℤ))ˣ) ∈ latticeWeylGroup τ :=
  mem_latticeWeylGroup_of_wordMat l fun v => by
    rw [h, Matrix.neg_mulVec, Matrix.one_mulVec, Units.val_neg, Units.val_one, LinearMap.neg_apply,
      Module.End.one_apply]

end CFSG.RankThree.Lattice
