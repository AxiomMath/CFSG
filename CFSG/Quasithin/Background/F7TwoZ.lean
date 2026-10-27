module

public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isPGroup_conjSubgroup_iff {B : Subgroup G} (g : G) :
    IsPGroup 2 ↥(conjSubgroup B g) ↔ IsPGroup 2 ↥B :=
  F7.isPGroup_conjSub_iff g⁻¹

theorem inv_mem_nonTwoConj {A H : Subgroup G} {h : G} (hh : h ∈ nonTwoConj A H) :
    h⁻¹ ∈ nonTwoConj A H := by
  refine ⟨H.inv_mem hh.1, fun hp => hh.2 ?_⟩
  have e : conjSubgroup (A ⊔ conjSubgroup A h⁻¹) h = A ⊔ conjSubgroup A h := by
    have : conjSubgroup (A ⊔ conjSubgroup A h⁻¹) h =
        conjSubgroup A h ⊔ conjSubgroup (conjSubgroup A h⁻¹) h :=
      Subgroup.map_sup _ _ _
    rw [this, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, sup_comm]
  rw [← e]
  exact (isPGroup_conjSubgroup_iff h).mpr hp

theorem conjSubgroup_le_normalizer_iff {A W : Subgroup G} (ξ z : G) :
    conjSubgroup A ξ ≤ Subgroup.normalizer (conjSub z W : Set G) ↔
      A ≤ Subgroup.normalizer (conjSub (ξ * z) W : Set G) := by
  show conjSub ξ⁻¹ A ≤ _ ↔ _
  rw [conjSub_le_iff, inv_inv, ← conjSub_normalizer, ← conjSub_mul]

theorem exists_nonTwoConj_not_normalizing {A H P X W : Subgroup G} (hAP : A ≤ P) (hPH : P ≤ H)
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hHXP : H ≤ X ⊔ P) (hX : X ≤ Subgroup.closure (nonTwoConj A H))
    (hex : ∃ g ∈ H, ¬ A ≤ Subgroup.normalizer (conjSub g W : Set G)) :
    ∃ h ∈ nonTwoConj A H, ∃ g ∈ H,
      conjSubgroup A h ≤ Subgroup.normalizer (conjSub g W : Set G) ∧
        ¬ A ≤ Subgroup.normalizer (conjSub g W : Set G) := by
  by_contra hcon
  push Not at hcon
  have key1 : ∀ ξ ∈ nonTwoConj A H, ∀ z ∈ H,
      A ≤ Subgroup.normalizer (conjSub (ξ * z) W : Set G) →
        A ≤ Subgroup.normalizer (conjSub z W : Set G) := fun ξ hξ z hz hq =>
    hcon ξ hξ z hz ((conjSubgroup_le_normalizer_iff ξ z).mpr hq)
  have key2 : ∀ ξ ∈ nonTwoConj A H, ∀ z ∈ H,
      A ≤ Subgroup.normalizer (conjSub z W : Set G) →
        A ≤ Subgroup.normalizer (conjSub (ξ * z) W : Set G) := fun ξ hξ z hz hq => by
    have := key1 ξ⁻¹ (inv_mem_nonTwoConj hξ) (ξ * z) (H.mul_mem hξ.1 hz)
    rw [inv_mul_cancel_left] at this
    exact this hq
  let D : Subgroup G :=
    { carrier := {ξ | ξ ∈ H ∧ ∀ z ∈ H, (A ≤ Subgroup.normalizer (conjSub z W : Set G) ↔
        A ≤ Subgroup.normalizer (conjSub (ξ * z) W : Set G))}
      one_mem' := ⟨H.one_mem, fun z _ => by rw [one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun z hz => by
        rw [mul_assoc]
        exact (hb.2 z hz).trans (ha.2 (b * z) (H.mul_mem hb.1 hz))⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun z hz => by
        have := ha.2 (a⁻¹ * z) (H.mul_mem (H.inv_mem ha.1) hz)
        rw [mul_inv_cancel_left] at this
        exact this.symm⟩ }
  have hΞD : nonTwoConj A H ⊆ D := fun ξ hξ =>
    ⟨hξ.1, fun z hz => ⟨key2 ξ hξ z hz, key1 ξ hξ z hz⟩⟩
  have hXD : X ≤ D := hX.trans ((Subgroup.closure_le D).mpr hΞD)
  obtain ⟨g, hgH, hg⟩ := hex
  have hgXP : g ∈ (X : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left X P hPX]
    exact hHXP hgH
  obtain ⟨x, hx, p, hp, rfl⟩ := hgXP
  refine hg ?_
  have hQp : A ≤ Subgroup.normalizer (conjSub p W : Set G) := by
    intro a ha
    rw [conjSub_normalizer, mem_conjSub]
    refine hPW ?_
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) (hAP ha)) hp
    simpa [mul_assoc] using this
  exact ((hXD hx).2 p (hPH hp)).mp hQp

theorem relIndex_inf_eq_two {A R N : Subgroup G} (hRN : R ≤ N) (hRA : R ≤ A)
    (hidx : R.relIndex A = 2) (hnot : ¬ A ≤ N) : (A ⊓ N).relIndex A = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex R (A ⊓ N) A (le_inf hRA hRN) inf_le_left
  rw [hidx] at h1
  have hd : (A ⊓ N).relIndex A ∣ 2 := ⟨R.relIndex (A ⊓ N), by rw [← h1, mul_comm]⟩
  have h1' : (A ⊓ N).relIndex A ≠ 1 := fun e =>
    hnot ((Subgroup.relIndex_eq_one.mp e).trans inf_le_right)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with e | e
  · exact absurd e h1'
  · exact e

end CFSG.Quasithin.F7Two
