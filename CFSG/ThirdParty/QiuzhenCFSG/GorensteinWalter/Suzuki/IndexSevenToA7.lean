module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# From an index-seven subgroup to `A₇`

The final, mechanical step of Suzuki's recognition theorem: if a finite
simple group of order `2520` has a subgroup of index seven, then the coset
action embeds it faithfully into `S₇`, the image has index two (hence is
`A₇` by the index-two subgroup theorem), and equal orders give the
isomorphism.

This uses `hmin` (simplicity forces the normal core of `H` to be trivial,
so the coset action is faithful) and the first-case count `|G| = 2520`
(to identify the image as `A₇`).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A finite simple group of order `2520` with a subgroup of index seven is
isomorphic to `A₇`. -/
public theorem mulEquiv_alternatingGroup_seven_of_index_seven
    {G : Type u} [Group G] [Finite G]
    (hGcard : Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7)
    (hsimple : IsSimpleGroup G)
    (H : Subgroup G) (hHindex : H.index = 7) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  classical
  have hHne : H ≠ ⊤ := by
    intro htop
    have hindex : H.index = 1 := by rw [htop]; simp
    omega
  have hcore : H.normalCore = ⊥ := by
    have hle : H.normalCore ≤ H := H.normalCore_le
    rcases H.normalCore_normal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · exfalso
      apply hHne
      exact le_antisymm le_top (htop.symm ▸ hle)
  have hCosetCard : Nat.card (G ⧸ H) = 7 := by
    rw [← H.index_eq_card, hHindex]
  let act : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  have hactInj : Function.Injective act := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← H.normalCore_eq_ker]
    exact hcore
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hCosetFcard : Fintype.card (G ⧸ H) = 7 := by
    simpa [Nat.card_eq_fintype_card] using hCosetCard
  let eCoset : (G ⧸ H) ≃ Fin 7 := Fintype.equivFinOfCardEq hCosetFcard
  let actFin : G →* Equiv.Perm (Fin 7) :=
    (Equiv.permCongrHom eCoset).toMonoidHom.comp act
  have hactFinInj : Function.Injective actFin := by
    intro x y hxy
    apply hactInj
    apply (Equiv.permCongrHom eCoset).injective
    simpa [actFin] using hxy
  let A : Subgroup (Equiv.Perm (Fin 7)) := actFin.range
  let eRange : G ≃* A :=
    MulEquiv.ofBijective actFin.rangeRestrict
      ⟨fun x y hxy ↦ hactFinInj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin⟩
  have hAcard : Nat.card A = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hperm7card : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hAindex : A.index = 2 := by
    have hmul := A.index_mul_card
    rw [hAcard, hperm7card] at hmul
    omega
  have hAalt : A = alternatingGroup (Fin 7) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hAindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hAalt)⟩

end CFSG.GorensteinWalter
