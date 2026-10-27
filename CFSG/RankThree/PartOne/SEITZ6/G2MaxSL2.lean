module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.RankThree.PartOne.CTP CFSG.BenderSuzuki.MatrixGroups Matrix

variable {F : Type} [Field F]

@[expose] def uHom (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun a := u2 (Multiplicative.toAdd a)
  map_one' := u2_zero
  map_mul' _ _ := u2_add _ _

theorem uHom_injective : Function.Injective (uHom F) := fun _ _ h =>
  Multiplicative.toAdd.injective (u2_injective h)

@[expose] def Uup (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (uHom F).range

theorem u2_mem_Uup (a : F) : u2 a ∈ Uup F := ⟨Multiplicative.ofAdd a, rfl⟩

theorem mem_Uup_iff {g : SpecialLinearGroup (Fin 2) F} : g ∈ Uup F ↔ ∃ a : F, g = u2 a :=
  ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha.symm⟩, fun ⟨a, ha⟩ => ha ▸ u2_mem_Uup a⟩

theorem card_Uup [Finite F] : Nat.card (Uup F) = Nat.card F := by
  unfold Uup
  rw [← Nat.card_congr (MonoidHom.ofInjective (uHom_injective (F := F))).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem isSimpleGroup_SL2 [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := by
  have hs : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hbij : Function.Bijective (mkPSL F) :=
    ⟨mkPSL_injective, QuotientGroup.mk'_surjective _⟩
  exact (MulEquiv.ofBijective (mkPSL F) hbij).isSimpleGroup

theorem normalClosure_Uup [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    Subgroup.normalClosure ((Uup F : Subgroup _) : Set (SpecialLinearGroup (Fin 2) F)) = ⊤ := by
  have := isSimpleGroup_SL2 h4
  rcases (Subgroup.normalClosure_normal (s := ((Uup F : Subgroup _) :
      Set (SpecialLinearGroup (Fin 2) F)))).eq_bot_or_eq_top with h | h
  · exfalso
    have h1 : u2 (1 : F) ∈ Subgroup.normalClosure ((Uup F : Subgroup _) :
        Set (SpecialLinearGroup (Fin 2) F)) := Subgroup.subset_normalClosure (u2_mem_Uup 1)
    rw [h, Subgroup.mem_bot] at h1
    have := u2_injective (h1.trans u2_zero.symm)
    exact one_ne_zero this
  · exact h

end CFSG.RankThree.PartOne.SEITZ6
