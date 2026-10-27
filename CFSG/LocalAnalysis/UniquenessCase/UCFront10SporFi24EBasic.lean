module

public import CFSG.Sporadic.Fi24.Octads

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24
  CFSG.Sporadic.Fi24.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] rAction

section Gens


theorem comm_of_mem_closure {s : Set R} {h x : R} (hs : ∀ y ∈ s, h * y = y * h)
    (hx : x ∈ Subgroup.closure s) : h * x = x * h := by
  have hle : Subgroup.closure s ≤ Subgroup.centralizer {h} := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hs y hy).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

@[expose] noncomputable def fi24EB : Subgroup R := Subgroup.closure (Set.range bbar)

theorem comm_cls_of_smul {h : R} {k : Fin 306936} (hk : h • k = k) : h * cls k = cls k * h := by
  have e := cls_smul_R h k
  rw [hk] at e
  calc h * cls k = h * cls k * h⁻¹ * h := by group
    _ = cls k * h := by rw [← e]

theorem comm_fi24EB {h : R} (hb : ∀ i, h * bbar i = bbar i * h) {x : R} (hx : x ∈ fi24EB) :
    h * x = x * h :=
  comm_of_mem_closure (fun y hy => by obtain ⟨i, rfl⟩ := hy; exact hb i) hx


theorem fi24EB_comm {x : R} (hx : x ∈ fi24EB) (i : Fin 24) : x * bbar i = bbar i * x :=
  (comm_of_mem_closure (fun y hy => by obtain ⟨j, rfl⟩ := hy; exact bbar_comm i j) hx).symm

end Gens

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
