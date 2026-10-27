module

public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.Quasithin.A38c15 CFSG.Adapters.RankTwoModelTransports

variable {p : ℕ} [Fact p.Prime]

theorem gl2OddIndex_of_card (hR1 : GL2OddIndex) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p) (M : Subgroup (GL (Fin 2) F)) (hodd : Odd M.index)
    (hns : ¬ Group.IsSolvable ↥M) (g : GL (Fin 2) F)
    (hg : (g : Matrix (Fin 2) (Fin 2) F).det = 1) : g ∈ M := by
  let φ : F ≃+* ZMod p := fieldEquivZMod hF
  let e : GL (Fin 2) F ≃* GL (Fin 2) (ZMod p) := glCongr φ
  let f : GL (Fin 2) F →* GL (Fin 2) (ZMod p) := e
  have hf : Function.Injective f := e.injective
  have hidx : (M.map f).index = M.index := Subgroup.index_map_equiv M e
  have hns' : ¬ Group.IsSolvable ↥(M.map f) := fun hsol =>
    hns (Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective f hf).toMonoidHom) (M.equivMapOfInjective f hf).injective)
  have hdet : ((f g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    have h := det_map_ringEquiv φ (g : Matrix (Fin 2) (Fin 2) F)
    rw [hg, map_one] at h
    exact h
  exact (Subgroup.mem_map_iff_mem hf).mp (hR1 p hp2 (M.map f) (hidx ▸ hodd) hns' (f g) hdet)

omit [Fact p.Prime] in
theorem ne_three_of_not_isSolvable_gl2 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p) (M : Subgroup (GL (Fin 2) F)) (hns : ¬ Group.IsSolvable ↥M) :
    p ≠ 3 := by
  rintro rfl
  let e : GL (Fin 2) F ≃* GL (Fin 2) (ZMod 3) := glCongr (fieldEquivZMod hF)
  have : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := isSolvable_gl2_zmod_three
  have : Group.IsSolvable (GL (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact hns inferInstance

end CFSG.Quasithin.A38c17
