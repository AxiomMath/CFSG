module

public import Certificates.Data.DcRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.LocDblDcos

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.Quasithin.H13.LocDbl.DcRank

variable {Γ : Type} [Group Γ]

theorem isElemAbelian_map_mulEquiv {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    {E : Subgroup A} (h : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map e.toMonoidHom) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x', hx', hx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg e.toMonoidHom
      (congrArg Subtype.val (h.1.is_comm.comm (⟨x', hx'⟩ : E) ⟨y', hy'⟩))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, h.2 x' hx', map_one]

@[expose] def ElemAbelianBound (A : Type*) [Group A] (m : ℕ) : Prop :=
  ∀ E : Subgroup A, IsElemAbelian 2 E → Nat.card E ≤ m

theorem ElemAbelianBound.of_mulEquiv {A A' : Type*} [Group A] [Group A'] [Finite A] {m : ℕ}
    (e : A ≃* A') (h : ElemAbelianBound A m) : ElemAbelianBound A' m := by
  intro E' hE'
  have := h (E'.map e.symm.toMonoidHom) (isElemAbelian_map_mulEquiv e.symm hE')
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

end CFSG.Quasithin.H13.LocDbl
