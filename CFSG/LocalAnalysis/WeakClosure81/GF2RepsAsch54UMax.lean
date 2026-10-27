module

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Psi
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Blueprint (LieModel)

variable {Y : Type} [Group Y]

theorem lGen_le_of_forall_le {P : ∀ (X : Type) [Group X], Prop} {T M : Subgroup Y}
    (hM : ∀ X : Subgroup Y, T ≤ X → X < ⊤ → X ≤ M) : lGen P ⊤ T ≤ M :=
  iSup₂_le fun X hX => hM X hX.1 hX.2.1

theorem lGen_ne_top_of_forall_le {P : ∀ (X : Type) [Group X], Prop} {T M : Subgroup Y}
    (hMt : M < ⊤) (hM : ∀ X : Subgroup Y, T ≤ X → X < ⊤ → X ≤ M) : lGen P ⊤ T ≠ ⊤ := by
  intro h
  have hle := lGen_le_of_forall_le (P := P) hM
  rw [h] at hle
  exact hMt.ne (top_le_iff.mp hle)

theorem hasQuotShape_oInf_top [Finite Y] {L : Subgroup Y} [L.Normal] (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hC : centralizer (L : Set Y) = ⊥)
    {P : ∀ (X : Type) [Group X], Prop} (hP : P ↥L) :
    HasQuotShape L (OInf (⊤ : Subgroup Y) : Set Y) P := by
  refine ⟨↥L, inferInstance, MonoidHom.id _, Function.surjective_id, fun k => ?_, hP⟩
  rw [oInf_top_eq_bot (solvableRadical_eq_bot_of_simple_normal hLs hnab hC), MonoidHom.id_apply,
    SetLike.mem_coe, mem_bot, OneMemClass.coe_eq_one]

@[expose] def Shape54Socle (X : Type) [Group X] : Prop :=
  (IsL2 X 2 ∨ IsU3 X 2) ∨ (IsAlt X 6 ∨ IsL3 X 1) ∨
    (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ F6.IsL2 p e X) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p % 4 = 3 ∧ LieModel X .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel X .PSU 3 p 1))) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel X .PSp 2 p 1)

theorem shape54_of_shape54Socle [Finite Y] {L : Subgroup Y} [L.Normal] (T : Subgroup Y)
    (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : centralizer (L : Set Y) = ⊥) (h : Shape54Socle ↥L) : Shape54 ⊤ T L := by
  rcases h with h | h | ⟨p, e, hp, hp2, he, h⟩ | ⟨p, hp, hp2, ⟨h4, h⟩ | ⟨h4, h⟩⟩ |
      ⟨p, hp, hp2, h⟩
  · exact Or.inl (hasQuotShape_oInf_top hLs hnab hC h)
  · exact Or.inr (Or.inl (hasQuotShape_oInf_top hLs hnab hC h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp2, he,
      hasQuotShape_oInf_top hLs hnab hC (P := fun X _ => F6.IsL2 p e X) h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl ⟨h4,
      hasQuotShape_oInf_top hLs hnab hC (P := fun X _ => LieModel X .PSL 3 p 1) h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr ⟨h4,
      hasQuotShape_oInf_top hLs hnab hC (P := fun X _ => LieModel X .PSU 3 p 1) h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hp2,
      hasQuotShape_oInf_top hLs hnab hC (P := fun X _ => LieModel X .PSp 2 p 1) h⟩))))

end CFSG.LocalAnalysis.WeakClosure81

end
