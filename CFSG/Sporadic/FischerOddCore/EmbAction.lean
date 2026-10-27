module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Sporadic.FischerOddCore

variable {α β : Type*}

@[expose] def embStab (ι : β → α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, g x ∈ Set.range ι ↔ x ∈ Set.range ι}
  mul_mem' {g h} hg hh x := by
    rw [Equiv.Perm.mul_apply]
    exact (hg (h x)).trans (hh x)
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg x := by
    have := hg (g⁻¹ x)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    exact this.symm

theorem mem_embStab {ι : β → α} {g : Equiv.Perm α} :
    g ∈ embStab ι ↔ ∀ x, g x ∈ Set.range ι ↔ x ∈ Set.range ι :=
  Iff.rfl

@[expose] noncomputable def embPosPerm (ι : β → α) (hι : Function.Injective ι)
    (g : embStab ι) : Equiv.Perm β :=
  ((Equiv.ofInjective ι hι).trans
    (Equiv.Perm.subtypePerm (g : Equiv.Perm α) (mem_embStab.1 g.2))).trans
      (Equiv.ofInjective ι hι).symm

theorem embPosPerm_apply (ι : β → α) (hι : Function.Injective ι) (g : embStab ι) (b : β) :
    ι (embPosPerm ι hι g b) = (g : Equiv.Perm α) (ι b) := by
  simp only [embPosPerm, Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm hι]
  rfl

theorem embPos_ext (ι : β → α) (hι : Function.Injective ι) {σ τ : Equiv.Perm β}
    (h : ∀ b, ι (σ b) = ι (τ b)) : σ = τ :=
  Equiv.ext fun b => hι (h b)

@[expose] noncomputable def embPos (ι : β → α) (hι : Function.Injective ι) :
    embStab ι →* Equiv.Perm β where
  toFun := embPosPerm ι hι
  map_one' := embPos_ext ι hι fun b => by
    rw [embPosPerm_apply ι hι, Subgroup.coe_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  map_mul' g h := embPos_ext ι hι fun b => by
    rw [embPosPerm_apply ι hι, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      embPosPerm_apply ι hι, embPosPerm_apply ι hι]

theorem embPos_apply (ι : β → α) (hι : Function.Injective ι) (g : embStab ι) (b : β) :
    ι (embPos ι hι g b) = (g : Equiv.Perm α) (ι b) :=
  embPosPerm_apply ι hι g b

theorem mem_embStab_of_apply {ι : β → α} {g : Equiv.Perm α} (σ : Equiv.Perm β)
    (h : ∀ b, g (ι b) = ι (σ b)) : g ∈ embStab ι := by
  intro x
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨σ⁻¹ b, ?_⟩
    apply g.injective
    rw [h, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨σ b, (h b).symm⟩

theorem embPos_eq_of_apply (ι : β → α) (hι : Function.Injective ι) (g : embStab ι)
    (σ : Equiv.Perm β) (h : ∀ b, (g : Equiv.Perm α) (ι b) = ι (σ b)) : embPos ι hι g = σ :=
  embPos_ext ι hι fun b => by rw [embPos_apply ι hι, h]

theorem embPos_eq_one_iff (ι : β → α) (hι : Function.Injective ι) (g : embStab ι) :
    embPos ι hι g = 1 ↔ ∀ b, (g : Equiv.Perm α) (ι b) = ι b := by
  constructor
  · intro h b
    rw [← embPos_apply ι hι g b, h, Equiv.Perm.one_apply]
  · intro h
    exact embPos_eq_of_apply ι hι g 1 fun b => by rw [h, Equiv.Perm.one_apply]

end CFSG.Sporadic.FischerOddCore
