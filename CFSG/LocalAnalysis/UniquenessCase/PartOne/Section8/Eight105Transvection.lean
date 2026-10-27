module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.PartTwo.Sec15.SimsBaumannTransvection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pow_twelve_mem_centralizer {V : Subgroup G} (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hV2 : ∀ v ∈ V, v * v = 1) {s t : G} (hs : s ∈ normalizer (V : Set G))
    (ht : t ∈ normalizer (V : Set G)) (hs2 : s * s = 1) (ht2 : t * t = 1)
    (hsV : Nat.card V ≤ 2 * Nat.card (V ⊓ centralizer ({s} : Set G) : Subgroup G))
    (htV : Nat.card V ≤ 2 * Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    (s * t) ^ 12 ∈ centralizer (V : Set G) := by
  have hVel : CFSG.Open.IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun v w => Subtype.ext (hVab v v.2 w w.2)⟩⟩, fun v hv => ?_⟩
    rw [pow_two]
    exact hV2 v hv
  have hsV' : (V ⊓ centralizer ({s} : Set G)).relIndex V ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (V ⊓ centralizer ({s} : Set G)) V
    rw [inf_of_le_left (inf_le_left : V ⊓ centralizer ({s} : Set G) ≤ V)] at h
    exact Nat.le_of_mul_le_mul_right (by rw [h]; exact hsV) Nat.card_pos
  have htV' : (V ⊓ centralizer ({t} : Set G)).relIndex V ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (V ⊓ centralizer ({t} : Set G)) V
    rw [inf_of_le_left (inf_le_left : V ⊓ centralizer ({t} : Set G) ≤ V)] at h
    exact Nat.le_of_mul_le_mul_right (by rw [h]; exact htV) Nat.card_pos
  exact CFSG.RankThree.PartTwo.Sec15.SimsBaumann.pow_twelve_mem_centralizer hVel hs ht hsV' htV'

private lemma is_elem_abelian {V A : Subgroup G}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1) :
    CFSG.Open.IsElemAbelian 2 ((A ⊓ centralizer (V : Set G)) ⊔ V) := by
  have hAel : CFSG.Open.IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hAab a a.2 b b.2)⟩⟩, fun a ha => ?_⟩
    rw [pow_two]
    exact hA2 a ha
  have hVel : CFSG.Open.IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun v w => Subtype.ext (hVab v v.2 w w.2)⟩⟩, fun v hv => ?_⟩
    rw [pow_two]
    exact hV2 v hv
  have hA'el : CFSG.Open.IsElemAbelian 2 (A ⊓ centralizer (V : Set G)) :=
    hAel.mono inf_le_left
  refine CFSG.Open.IsElemAbelian.sup_of_commute hA'el hVel ?_
  intro a ha v hv
  exact (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm

theorem card_mul_card_le_of_max {R V A : Subgroup G} (hVR : V ≤ R) (hAR : A ≤ R)
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hmax : ∀ E : Subgroup G, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E ≤ Nat.card A) :
    Nat.card V * Nat.card (A ⊓ centralizer (V : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) := by
  set A' : Subgroup G := A ⊓ centralizer (V : Set G) with hA'
  have hEel : CFSG.Open.IsElemAbelian 2 (A' ⊔ V) := is_elem_abelian hVab hV2 hAab hA2
  have hER : A' ⊔ V ≤ R := by
    rw [hA']
    exact sup_le (inf_le_left.trans hAR) hVR
  have hEcard : Nat.card (A' ⊔ V : Subgroup G) ≤ Nat.card A :=
    hmax (A' ⊔ V) hER
      (fun x hx y hy => hEel.comm hx hy)
      (fun x hx => hEel.mul_self_eq_one hx)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A' V
    (fun a ha v hv => (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm)).1
  have hle : A' ⊓ V ≤ V ⊓ centralizer (A : Set G) := by
    rintro x ⟨hxA', hxV⟩
    exact ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun a ha => hAab a ha x hxA'.1⟩
  calc Nat.card V * Nat.card A' = Nat.card A' * Nat.card V := Nat.mul_comm _ _
    _ = Nat.card (A' ⊔ V : Subgroup G) * Nat.card (A' ⊓ V : Subgroup G) := hprod.symm
    _ ≤ Nat.card A * Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) :=
      Nat.mul_le_mul hEcard (Subgroup.card_le_of_le hle)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
