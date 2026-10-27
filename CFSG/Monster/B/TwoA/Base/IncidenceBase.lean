
module

public import CFSG.Monster.B.TwoA.Base.Par45BBase
public import CFSG.Monster.B.TwoA.Base.ConjSub

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B

theorem Echain_le_succ : ∀ i : ℕ, 1 ≤ i → i < 5 → Echain i ≤ Echain (i + 1) := by
  intro i h1 h5
  interval_cases i
  · exact Subgroup.zpowers_le.2 xhat_mem_Vhat
  · exact Vhat_le_E3
  · exact E3_le_E4
  · exact E4_le_E5

theorem Echain_mono {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j) (h5 : j ≤ 5) : Echain i ≤ Echain j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (Echain_le_succ k (by omega) (by omega))

@[expose] def ParObj : Set (ℕ × Subgroup Dfull) :=
  {x | 1 ≤ x.1 ∧ x.1 ≤ 5 ∧ ∃ g ∈ Shat, x.2 = conjSub g (Echain x.1)}

abbrev ParGeom : Type := ↥ParObj

@[expose] def parType (x : ParGeom) : ℕ := x.1.1

@[expose] def parInc (x y : ParGeom) : Prop :=
  x = y ∨ (parType x ≠ parType y ∧ (x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2))

@[expose] def IsParFlag (F : Set ParGeom) : Prop := ∀ x ∈ F, ∀ y ∈ F, parInc x y

@[expose] def stdObj (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5) : ParGeom :=
  ⟨(i, Echain i), h1, h5, 1, Shat.one_mem, (conjSub_one _).symm⟩

theorem parType_bounds (x : ParGeom) : 1 ≤ parType x ∧ parType x ≤ 5 := ⟨x.2.1, x.2.2.1⟩

theorem parInc_refl (x : ParGeom) : parInc x x := .inl rfl

theorem parInc_symm {x y : ParGeom} (h : parInc x y) : parInc y x := by
  rcases h with rfl | ⟨hne, h | h⟩
  · exact .inl rfl
  · exact .inr ⟨hne.symm, .inr h⟩
  · exact .inr ⟨hne.symm, .inl h⟩

theorem parInc_iff_of_ne {x y : ParGeom} (h : parType x ≠ parType y) :
    parInc x y ↔ x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2 := by
  constructor
  · rintro (rfl | ⟨-, h'⟩)
    · exact .inl le_rfl
    · exact h'
  · exact fun h' => .inr ⟨h, h'⟩

theorem eq_of_parInc {x y : ParGeom} (h : parInc x y) (ht : parType x = parType y) : x = y := by
  rcases h with h | ⟨hne, -⟩
  · exact h
  · exact absurd ht hne

instance finite_subgroup_Dfull : Finite (Subgroup Dfull) :=
  Finite.of_injective (fun H : Subgroup Dfull => (H : Set Dfull)) SetLike.coe_injective

instance finite_ParGeom : Finite ParGeom := by
  refine Finite.of_injective (fun x : ParGeom => ((⟨x.1.1, by have := x.2.2.1; omega⟩ : Fin 6),
    x.1.2)) ?_
  intro x y h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

theorem conjSub_mem_ParObj {g : Dfull} (hg : g ∈ Shat) {x : ℕ × Subgroup Dfull}
    (hx : x ∈ ParObj) : (x.1, conjSub g x.2) ∈ ParObj := by
  obtain ⟨h1, h5, h, hh, hx2⟩ := hx
  exact ⟨h1, h5, g * h, Shat.mul_mem hg hh, by rw [hx2, conjSub_mul]⟩

@[expose, instance_reducible] def parAction : MulAction Shat ParGeom where
  smul g x := ⟨(x.1.1, conjSub (g : Dfull) x.1.2), conjSub_mem_ParObj g.2 x.2⟩
  one_smul _ := Subtype.ext (Prod.ext rfl (conjSub_one _))
  mul_smul _ _ _ := Subtype.ext (Prod.ext rfl (conjSub_mul _ _ _))

attribute [local instance] parAction

theorem coe_parAction (g : Shat) (x : ParGeom) :
    (g • x : ParGeom).1 = (x.1.1, conjSub (g : Dfull) x.1.2) := rfl

theorem parType_smul (g : Shat) (x : ParGeom) : parType (g • x) = parType x := rfl

theorem parInc_smul_iff (g : Shat) (x y : ParGeom) : parInc (g • x) (g • y) ↔ parInc x y := by
  have hinj : g • x = g • y ↔ x = y := (MulAction.injective g).eq_iff
  unfold parInc
  rw [hinj, parType_smul, parType_smul]
  change _ ∨ (_ ∧ (conjSub (g : Dfull) x.1.2 ≤ conjSub (g : Dfull) y.1.2 ∨
    conjSub (g : Dfull) y.1.2 ≤ conjSub (g : Dfull) x.1.2)) ↔ _
  rw [conjSub_le_conjSub_iff, conjSub_le_conjSub_iff]

@[expose] def stdParFlag : Set ParGeom := {x | x.1.2 = Echain x.1.1}

theorem stdObj_mem (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5) : stdObj i h1 h5 ∈ stdParFlag := rfl

theorem stdParFlag_isParFlag : IsParFlag stdParFlag ∧ parType '' stdParFlag = Set.Icc 1 5 := by
  refine ⟨fun x hx y hy => ?_, ?_⟩
  · rcases eq_or_ne (parType x) (parType y) with h | h
    · refine .inl (Subtype.ext (Prod.ext h ?_))
      rw [hx, hy]
      exact congrArg Echain h
    · refine .inr ⟨h, ?_⟩
      rw [hx, hy]
      rcases le_total x.1.1 y.1.1 with h' | h'
      · exact .inl (Echain_mono x.2.1 h' y.2.2.1)
      · exact .inr (Echain_mono y.2.1 h' x.2.2.1)
  · ext i
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x.2.1, x.2.2.1⟩
    · rintro ⟨h1, h5⟩
      exact ⟨stdObj i h1 h5, stdObj_mem i h1 h5, rfl⟩

end CFSG.Monster.B.TwoA
