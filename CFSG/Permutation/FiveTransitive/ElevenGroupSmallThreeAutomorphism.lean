module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Permutation.FiveTransitive.FreeActionTransporterCount
import CFSG.Permutation.FiveTransitive.Degree39ElevenAut

public section

namespace CFSG

namespace FiveTransitive.ElevenGroupSmallThreeAutomorphism
open MulAction

theorem nine_not_dvd_card
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 11 Q)
    (hcard : Nat.card Q ≤ 121) : ¬ 9 ∣ Nat.card (MulAut Q) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_cases hQone : Nat.card Q = 1
  · let _ : Subsingleton Q := Finite.card_le_one_iff_subsingleton.mp (by omega)
    let _ : Subsingleton (MulAut Q) := ⟨fun a b => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    have hc : Nat.card (MulAut Q) = 1 := Nat.card_unique
    rw [hc]
    norm_num
  let S : Sylow 3 (MulAut Q) := Sylow.nonempty.some
  let C : SubMulAction S Q :=
    { carrier := {q | q ≠ 1}
      smul_mem' := by
        intro a q hq hh
        apply hq
        exact a.val.injective (hh.trans (map_one a.val).symm) }
  have hfree (a : S) (q : C) (ha : a • q = q) : a = 1 := by
    let A := Subgroup.zpowers a
    have hA : IsPGroup 3 A := S.isPGroup'.to_subgroup A
    have hfix : ∀ b : A, b • q.val = q.val := by
      intro b
      have hstab : a ∈ stabilizer S q.val := congrArg Subtype.val ha
      exact (Subgroup.zpowers_le.mpr hstab) b.property
    have hall := FiveTransitive.Degree39ElevenAut.action_trivial_of_fixed hA hQ hcard q.val q.property hfix
      (⟨a,Subgroup.mem_zpowers a⟩ : A)
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact hall x
  have hdiv : Nat.card S ∣ Nat.card C := by
    have he := FreeActionTransporterCount.card_orbit_preimage hfree
      (fun _ : orbitRel.Quotient S C => True)
    simpa using (show Nat.card S ∣ Nat.card {x : C // True} from ⟨_,he⟩)
  have hCcard : Nat.card C = Nat.card Q - 1 := by
    change Nat.card {q : Q // q ≠ 1} = _
    change Nat.card ↥(({1} : Set Q)ᶜ) = _
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
  rw [hCcard] at hdiv
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he2 : e ≤ 2 := by
    rw [he] at hcard
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 11) (by omega : 3 ≤ e)
    norm_num at hh
    omega
  intro hnine
  have hd9 : 9 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hnine
  have hh := hd9.trans hdiv
  rw [he] at hh hQone
  interval_cases e <;> norm_num at *

end FiveTransitive.ElevenGroupSmallThreeAutomorphism

end CFSG
