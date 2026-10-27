module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Vol2.Ch10SecBL32K
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.L3F

open CFSG.Quasithin.Vol2.Ch10.SecB.L32

@[expose] def rowOf (i : Fin 4) : Fin 3 → ZMod 2 := ![1, ((i.val % 2 : ℕ) : ZMod 2),
  ((i.val / 2 : ℕ) : ZMod 2)]

@[expose] def idxOf (r : Fin 3 → ZMod 2) : Fin 4 :=
  ⟨(r 1).val + 2 * (r 2).val, by
    have h1 := ZMod.val_lt (r 1)
    have h2 := ZMod.val_lt (r 2)
    omega⟩

@[expose] def actIdx (γ : L3.Γ) (i : Fin 4) : Fin 4 :=
  idxOf (Matrix.vecMul (rowOf i) ((γ⁻¹ : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)))

set_option maxRecDepth 100000 in
theorem actIdx_mul : ∀ γ δ : L3.Γ, IsPa γ → IsPa δ → ∀ i : Fin 4,
    actIdx (γ * δ) i = actIdx γ (actIdx δ i) := by
  unfold actIdx idxOf rowOf IsPa ent; decide +kernel

theorem actIdx_one : ∀ i : Fin 4, actIdx 1 i = i := by
  unfold actIdx idxOf rowOf; decide +kernel

@[expose] def permOf (γ : ↥Pa) : Equiv.Perm (Fin 4) where
  toFun := actIdx γ
  invFun := actIdx (γ : L3.Γ)⁻¹
  left_inv := fun i => by
    rw [← actIdx_mul _ _ (isPa_inv _ γ.2) γ.2, inv_mul_cancel, actIdx_one]
  right_inv := fun i => by
    rw [← actIdx_mul _ _ γ.2 (isPa_inv _ γ.2), mul_inv_cancel, actIdx_one]

@[expose] def permHom : ↥Pa →* Equiv.Perm (Fin 4) where
  toFun := permOf
  map_one' := Equiv.ext actIdx_one
  map_mul' := fun γ δ => Equiv.ext fun i => actIdx_mul γ δ γ.2 δ.2 i

theorem ka_le_pa : Ka ≤ Pa := fun _ h => h.1

set_option maxRecDepth 100000 in
theorem ka_even : ∀ γ : L3.Γ, IsKa γ → ∀ (h : IsPa γ),
    permOf ⟨γ, h⟩ ∈ alternatingGroup (Fin 4) := by
  intro γ hγ h
  rw [Equiv.Perm.mem_alternatingGroup]
  revert γ
  unfold permOf actIdx idxOf rowOf IsKa IsPa ent
  decide +kernel

set_option maxRecDepth 100000 in
theorem ka_inj : ∀ γ δ : L3.Γ, IsKa γ → IsKa δ → (∀ i, actIdx γ i = actIdx δ i) → γ = δ := by
  unfold actIdx idxOf rowOf IsKa IsPa ent; decide +kernel

@[expose] noncomputable def kaHom : ↥Ka →* ↥(alternatingGroup (Fin 4)) :=
  (permHom.comp (Subgroup.inclusion ka_le_pa)).codRestrict _ fun γ =>
    ka_even γ γ.2 (ka_le_pa γ.2)

theorem kaHom_injective : Function.Injective kaHom := by
  intro γ δ h
  have h1 : ∀ i, actIdx γ i = actIdx δ i := fun i =>
    congrArg (fun σ : ↥(alternatingGroup (Fin 4)) => (σ : Equiv.Perm (Fin 4)) i) h
  exact Subtype.ext (ka_inj γ δ γ.2 δ.2 h1)

theorem card_Ka : Nat.card ↥Ka = 12 := by
  rw [Nat.card_eq_fintype_card, ← SecB.L32.card_Ka]
  exact Fintype.card_subtype (· ∈ Ka)

@[expose] noncomputable def kaEquiv : ↥Ka ≃* ↥(alternatingGroup (Fin 4)) :=
  MulEquiv.ofBijective kaHom ⟨kaHom_injective, by
    have hcard : Nat.card ↥(alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card]; decide
    exact (Function.Injective.bijective_of_nat_card_le kaHom_injective
      (by rw [card_Ka, hcard])).2⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.L3F
