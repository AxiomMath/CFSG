module

public import CFSG.Quasithin.Background.G25Dual

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups

section Base

variable {F : Type} [Field F] {Γ : Type} [Group Γ]

structure L1Rep (ρ : Γ →* SL(3, F)) : Prop where
  stab : ∀ x, ρ x ∈ Pt (vE F 0)
  blk : ∀ M ∈ commutator SL(2, F), ∃ x, ρ x = CFSG.Quasithin.SL3Model.blk M
  torus : ∀ c : F, c ≠ 0 → ∃ x, ρ x • vE F 0 = c • vE F 0

@[expose] noncomputable def actV (ρ : Γ →* SL(3, F)) : Γ → (Fin 3 → F) →+ (Fin 3 → F) :=
  fun x => (Matrix.mulVecLin (ρ x : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom

@[expose] noncomputable def actVd (ρ : Γ →* SL(3, F)) : Γ → (Fin 3 → F) →+ (Fin 3 → F) :=
  fun x => (Matrix.mulVecLin (dualHom F 3 (ρ x) : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom

@[expose] def ablk (g : SL(3, F)) : Matrix (Fin 2) (Fin 2) F :=
  !![g.1 1 1, g.1 1 2; g.1 2 1, g.1 2 2]

@[expose] noncomputable def actUg (g : SL(3, F)) : (Fin 2 → F) →+ (Fin 2 → F) :=
  ((g.1 0 0) • Matrix.mulVecLin (ablk (dualHom F 3 g))).toAddMonoidHom

@[expose] noncomputable def actU (ρ : Γ →* SL(3, F)) : Γ → (Fin 2 → F) →+ (Fin 2 → F) :=
  fun x => actUg (ρ x)

@[expose] def tqv (v : Fin 2 → F) : SL(3, F) := tq (v 0) (v 1)

@[expose] def lineSub (F : Type) [Field F] : AddSubgroup (Fin 3 → F) :=
  (Submodule.span F {vE F 0}).toAddSubgroup

@[expose] def annSub (F : Type) [Field F] : AddSubgroup (Fin 3 → F) where
  carrier := {f | f 0 = 0}
  add_mem' := fun {a b} ha hb => by simp [Pi.add_apply, show a 0 = 0 from ha, show b 0 = 0 from hb]
  zero_mem' := rfl
  neg_mem' := fun {a} ha => by simp [show a 0 = 0 from ha]

end Base

end CFSG.Quasithin.RonanG25
