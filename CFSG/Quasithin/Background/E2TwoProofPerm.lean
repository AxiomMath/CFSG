module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.Quasithin

namespace E2P

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

@[expose] def boolStab (b : Fin n → Bool) : Subgroup (Perm (Fin n)) where
  carrier := {σ | ∀ x, b (σ x) = b x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x => (hσ (τ x)).trans (hτ x)
  inv_mem' := fun {σ} hσ x => by
    have h := hσ (σ⁻¹ x)
    rw [Perm.coe_inv, Equiv.apply_symm_apply] at h
    exact h.symm

theorem mem_boolStab {b : Fin n → Bool} {σ : Perm (Fin n)} :
    σ ∈ boolStab b ↔ ∀ x, b (σ x) = b x := Iff.rfl

@[expose] def boolStab2 (b : Fin n → Bool) : Subgroup (Perm (Fin n)) where
  carrier := {σ | (∀ x, b (σ x) = b x) ∨ (∀ x, b (σ x) = !b x)}
  one_mem' := Or.inl fun _ => rfl
  mul_mem' := by
    rintro σ τ (hσ | hσ) (hτ | hτ)
    · exact Or.inl fun x => (hσ (τ x)).trans (hτ x)
    · exact Or.inr fun x => (hσ (τ x)).trans (hτ x)
    · exact Or.inr fun x => (hσ (τ x)).trans (by rw [hτ x])
    · exact Or.inl fun x => (hσ (τ x)).trans (by rw [hτ x, Bool.not_not])
  inv_mem' := by
    rintro σ (hσ | hσ)
    · refine Or.inl fun x => ?_
      have h := hσ (σ⁻¹ x)
      rw [Perm.coe_inv, Equiv.apply_symm_apply] at h
      exact h.symm
    · refine Or.inr fun x => ?_
      have h := hσ (σ⁻¹ x)
      rw [Perm.coe_inv, Equiv.apply_symm_apply] at h
      rw [Perm.coe_inv, h, Bool.not_not]

theorem lat_cases {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hc : c.check RN.enc = true)
    (Y : Subgroup ↥A) (hY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y) :
    ∃ (j : ℕ) (hj : j < (c.tGens :: c.lat).length),
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ≤ A ∧
      Y = (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}).subgroupOf A ∧
      Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}) = c.sizes.getD j 0 := by
  subst hM
  exact c.overgroup_cases_idx (rawIsEnc n) hc Y hY

theorem lat_card (c : LatCert (Perm (Fin n))) (hc : c.check RN.enc = true) (j : ℕ)
    (hj : j < (c.tGens :: c.lat).length) :
    Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}) = c.sizes.getD j 0 :=
  c.card_member_idx (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc) j hj

theorem card_subgroupOf_of_le {G : Type} [Group G] {H A : Subgroup G} (h : H ≤ A) :
    Nat.card (H.subgroupOf A) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

end E2P

end CFSG.Quasithin
