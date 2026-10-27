module

public import CFSG.Quasithin.Background.SmithD37Core

public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

section Row

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

@[expose] def rowSub (Mm : MatModel L₁ L₂ F d) (Y : Submodule F (Fin d → F)) : Subgroup U where
  carrier := {u | ∀ i, Multiplicative.toAdd (Mm.β u) i ∈ Y}
  one_mem' := by
    intro i
    simp only [map_one, toAdd_one]
    exact Y.zero_mem
  mul_mem' := by
    intro u v hu hv i
    simp only [map_mul, toAdd_mul]
    exact Y.add_mem (hu i) (hv i)
  inv_mem' := by
    intro u hu i
    simp only [map_inv, toAdd_inv]
    exact Y.neg_mem (hu i)

theorem rowSub_inv₁ (Mm : MatModel L₁ L₂ F d) (Y : Submodule F (Fin d → F)) (l : ↥L₁) {u : U}
    (hu : u ∈ rowSub Mm Y) : (l : MulAut U) u ∈ rowSub Mm Y := by
  intro i
  rw [Mm.act₁, toAdd_ofAdd]
  have : ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      Multiplicative.toAdd (Mm.β u) =
      fun i => ∑ j, ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix _ _ F) i j •
        Multiplicative.toAdd (Mm.β u) j := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [this]
  exact Y.sum_mem fun j _ => Y.smul_mem _ (hu j)

theorem rowSub_mono (Mm : MatModel L₁ L₂ F d) {Y Y' : Submodule F (Fin d → F)} (h : Y ≤ Y') :
    rowSub Mm Y ≤ rowSub Mm Y' :=
  fun _ hu i => h (hu i)

theorem rowSub_top (Mm : MatModel L₁ L₂ F d) : rowSub Mm ⊤ = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => Submodule.mem_top

theorem rowSub_bot (Mm : MatModel L₁ L₂ F d) : rowSub Mm ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot, ← Mm.β.map_eq_one_iff, ← ofAdd_toAdd (Mm.β u), ofAdd_eq_one]
  ext i j
  have := hu i
  rw [Submodule.mem_bot] at this
  simp [this]

@[expose] noncomputable def rank1 (Mm : MatModel L₁ L₂ F d) (x y : Fin d → F) : U :=
  Mm.β.symm (Multiplicative.ofAdd (Matrix.vecMulVec x y))

theorem β_rank1 (Mm : MatModel L₁ L₂ F d) (x y : Fin d → F) :
    Mm.β (rank1 Mm x y) = Multiplicative.ofAdd (Matrix.vecMulVec x y) :=
  Mm.β.apply_symm_apply _

theorem rank1_mem_rowSub (Mm : MatModel L₁ L₂ F d) {Y : Submodule F (Fin d → F)} (x : Fin d → F)
    {y : Fin d → F} (hy : y ∈ Y) : rank1 Mm x y ∈ rowSub Mm Y := by
  intro i
  rw [β_rank1, toAdd_ofAdd]
  have : Matrix.vecMulVec x y i = x i • y := by
    ext j
    simp [Matrix.vecMulVec_apply]
  rw [this]
  exact Y.smul_mem _ hy

end Row

section Nat

variable {F : Type} [Field F] {d : ℕ}

abbrev natMod (F : Type) [Field F] (d : ℕ) : Type := Multiplicative (Fin d → F)

@[expose] noncomputable def glAut : Matrix.GeneralLinearGroup (Fin d) F →* MulAut (natMod F d) where
  toFun g := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [Matrix.mulVec_mulVec]

theorem glAut_apply (g : Matrix.GeneralLinearGroup (Fin d) F) (x : natMod F d) :
    glAut g x = Multiplicative.ofAdd
      ((g : Matrix (Fin d) (Fin d) F) *ᵥ Multiplicative.toAdd x) := by
  simp [glAut]

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

@[expose] noncomputable def natAut (Mm : MatModel L₁ L₂ F d) : ↥L₁ →* MulAut (natMod F d) :=
  glAut.comp Mm.R₁

@[expose] noncomputable def natSub (Mm : MatModel L₁ L₂ F d) : Subgroup (MulAut (natMod F d)) :=
  (natAut Mm).range

theorem natAut_apply (Mm : MatModel L₁ L₂ F d) (l : ↥L₁) (x : natMod F d) :
    natAut Mm l x = Multiplicative.ofAdd
      (((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
        Multiplicative.toAdd x) :=
  glAut_apply _ _

end Nat

end CFSG.Quasithin.SmithD37
