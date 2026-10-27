module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.OrbitRestrictionKernel
open MulAction

@[expose] def Complement {E : Type*} (B : Subgroup (Equiv.Perm E)) (x : E) : SubMulAction B E :=
  { carrier := (orbit B x)ᶜ
    smul_mem' := by
      intro b y hy hby
      exact hy (by simpa only [inv_smul_smul] using mem_orbit_of_mem_orbit b⁻¹ hby) }

theorem card_complement {E : Type*} [Finite E]
    (B : Subgroup (Equiv.Perm E)) (x : E) :
    Nat.card (Complement B x) = Nat.card E - Nat.card (orbit B x) := by
  change Nat.card ((orbit B x)ᶜ : Set E) = _
  rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq]

theorem injective_on_kernel {E : Type*} [Finite E]
    (B : Subgroup (Equiv.Perm E)) (x : E) :
    Function.Injective ((toPermHom B (Complement B x)).comp
      (toPermHom B (orbit B x)).ker.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro k hk
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ orbit B x
  · exact congrArg (fun f : Equiv.Perm (orbit B x) => (f ⟨y,hy⟩).val) k.property
  · exact congrArg (fun f : Equiv.Perm (Complement B x) => (f ⟨y,hy⟩).val) hk

private theorem card_kernel_dvd {E : Type*} [Finite E]
    (B : Subgroup (Equiv.Perm E)) (x : E) :
    Nat.card (toPermHom B (orbit B x)).ker ∣
      (Nat.card E - Nat.card (orbit B x)).factorial := by
  have hd := Subgroup.card_dvd_of_injective
    ((toPermHom B (Complement B x)).comp (toPermHom B (orbit B x)).ker.subtype)
    (injective_on_kernel B x)
  rwa [Nat.card_perm,card_complement] at hd

theorem card_kernel_le {E : Type*} [Finite E]
    (B : Subgroup (Equiv.Perm E)) (x : E)
    (hE : Nat.card E ≤ 14) (hx : 9 ≤ Nat.card (orbit B x)) :
    Nat.card (toPermHom B (orbit B x)).ker ≤ 120 := by
  have hd := (card_kernel_dvd B x).trans
    (Nat.factorial_dvd_factorial (by omega : Nat.card E - Nat.card (orbit B x) ≤ 5))
  have hb := Nat.le_of_dvd (Nat.factorial_pos 5) hd
  norm_num only [Nat.factorial] at hb
  exact hb

end FiveTransitive.OrbitRestrictionKernel

end CFSG
