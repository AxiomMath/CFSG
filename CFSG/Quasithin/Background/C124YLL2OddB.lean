module

public import CFSG.Quasithin.Background.C124YLL2Act
public import CFSG.Quasithin.Background.C124YLS2Fix

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

theorem card_toAdd {A : Type*} [AddCommGroup A] (S : Subgroup (Multiplicative A)) :
    Nat.card S.toAddSubgroup' = Nat.card S :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))

namespace S2

variable {F : Type*} [Field F]

@[expose] def lineAdd (F : Type*) [Field F] : AddSubgroup (Fin 2 → F) :=
  (Pi.evalAddMonoidHom (fun _ : Fin 2 => F) 1).ker

theorem mem_lineAdd {v : Fin 2 → F} : v ∈ lineAdd F ↔ v 1 = 0 := by
  simp [lineAdd, AddMonoidHom.mem_ker]

theorem card_lineAdd : Nat.card (lineAdd F) = Nat.card F := by
  refine Nat.card_congr ⟨fun v => (v : Fin 2 → F) 0, fun a => ⟨![a, 0], mem_lineAdd.2 (by simp)⟩,
    ?_, ?_⟩
  · intro v
    apply Subtype.ext
    have := mem_lineAdd.1 v.2
    ext i
    fin_cases i <;> simp [this]
  · intro a
    simp

theorem card_top_pi [Finite F] : Nat.card (⊤ : AddSubgroup (Fin 2 → F)) = Nat.card F ^ 2 := by
  rw [AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

end S2

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

theorem fix_of_mem_fixImg {B : Subgroup (MulAut W)} (hBX : B ≤ Xs) {x : ↥Xs}
    (hx : (x : MulAut W) ∈ B) {q : Multiplicative (Fin 2 → F)}
    (hq : q ∈ fixImg U Z C.c B) : C.gOf x (Multiplicative.toAdd q) = Multiplicative.toAdd q := by
  have := (mem_fixImg_iff_ind C.coord Xs C.hU C.hZ hBX q).1 hq x hx
  rw [gOf_apply, ofAdd_toAdd]
  exact congrArg Multiplicative.toAdd this

theorem card_fixImg_sq_le {B : Subgroup (MulAut W)} (hBX : B ≤ Xs) {x : ↥Xs}
    (hx : (x : MulAut W) ∈ B) {ω τω : F} (hne : τω ≠ ω)
    (hg : ∀ q, C.gOf x (ω • q) = τω • C.gOf x q) (L : AddSubgroup (Fin 2 → F))
    (hL : ∀ y ∈ L, ω • y ∈ L)
    (hS : ∀ q ∈ fixImg U Z C.c B, Multiplicative.toAdd q ∈ L) :
    Nat.card ↥(fixImg U Z C.c B) ^ 2 ≤ Nat.card L := by
  have hle : (fixImg U Z C.c B).toAddSubgroup' ≤ L ⊓ (C.gOf x - AddMonoidHom.id _).ker := by
    intro v hv
    refine ⟨hS _ hv, AddMonoidHom.mem_ker.2 ?_⟩
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
    exact C.fix_of_mem_fixImg hBX hx hv
  have h1 := S2.card_fix_sq_le hne (C.gOf x) hg L hL
  have h2 : Nat.card (fixImg U Z C.c B).toAddSubgroup' ≤
      Nat.card ↥(L ⊓ (C.gOf x - AddMonoidHom.id _).ker) := AddSubgroup.card_le_of_le hle
  have h3 := card_toAdd (fixImg U Z C.c B)
  have h4 : Nat.card ↥(fixImg U Z C.c B) ≤ Nat.card ↥(L ⊓ (C.gOf x - AddMonoidHom.id _).ker) := by
    rw [← h3]
    exact h2
  exact (Nat.pow_le_pow_left h4 2).trans h1

end L2Ctx

end CFSG.Quasithin.C124.YL
