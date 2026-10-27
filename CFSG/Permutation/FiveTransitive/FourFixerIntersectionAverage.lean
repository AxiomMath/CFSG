module

public import CFSG.Permutation.FiveTransitive.TransitiveIntersectionAverage

public section

namespace CFSG

namespace FiveTransitive.FourFixerIntersectionAverage

open Equiv MulAction

theorem exists_fixing_intersection_le
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (hn : 5 ≤ Fintype.card X)
    (D : Set X) [DecidablePred (· ∈ D)] (hD : D.ncard = 4) (A B : Finset X)
    (hDA : ∀ x ∈ D, x ∈ A) :
    ∃ q : fixingSubgroup P D,
      (B.filter (fun x => x ∈ D)).card ≤ (A ∩ B.image (q.val : Perm X)).card ∧
      (Fintype.card X - 4) *
          ((A ∩ B.image (q.val : Perm X)).card - (B.filter (fun x => x ∈ D)).card) ≤
        (B.filter (fun x => x ∉ D)).card * (A.filter (fun x => x ∉ D)).card := by
  classical
  let K := fixingSubgroup P D
  let Y := SubMulAction.ofFixingSubgroup P D
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : IsMultiplyPretransitive P X 5 := h5
  have hK1 : IsMultiplyPretransitive K Y 1 :=
    SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (m := 1) (n := 5) P D (by omega)
  let _ : IsPretransitive K Y := is_one_pretransitive_iff.mp hK1
  have hY : Fintype.card Y = Fintype.card X - 4 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ↥(Dᶜ : Set X) = _
    rw [Nat.card_coe_set_eq, Set.ncard_compl, hD, Nat.card_eq_fintype_card]
  have hne : Nonempty Y := Fintype.card_pos_iff.mp (by omega)
  let y₀ : Y := Classical.choice hne
  let C : Finset Y := B.subtype (fun a => a ∈ Dᶜ)
  let E : Finset Y := A.subtype (fun a => a ∈ Dᶜ)
  obtain ⟨q, hq⟩ := TransitiveIntersectionAverage.exists_card_filter_smul_le (G := K) y₀ C E
  let u : Perm X := q.val
  have hufix (x : X) (hx : x ∈ D) : u x = x :=
    (mem_fixingSubgroup_iff P).mp q.property x hx
  let F : Finset X := B.filter (fun a => u a ∈ A)
  have hcount : (C.filter fun a => q • a ∈ E).card = (F.filter (fun a => a ∉ D)).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      obtain ⟨haC, haE⟩ := Finset.mem_filter.mp ha
      have hb := (Finset.mem_subtype (p := fun a : X => a ∈ Dᶜ)).mp haC
      have hu := (Finset.mem_subtype (p := fun a : X => a ∈ Dᶜ)).mp haE
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hb, hu⟩, a.property⟩
    · intro a ha b hb heq
      exact Subtype.ext heq
    · intro a ha
      obtain ⟨haF, haD⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hu⟩ := Finset.mem_filter.mp haF
      refine ⟨⟨a, haD⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_subtype (p := fun a : X => a ∈ Dᶜ)).mpr hb,
        (Finset.mem_subtype (p := fun a : X => a ∈ Dᶜ)).mpr hu⟩
  have hinside : F.filter (fun a => a ∈ D) = B.filter (fun a => a ∈ D) := by
    ext a
    simp only [F, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hb, _⟩, haD⟩
      exact ⟨hb, haD⟩
    · rintro ⟨hb, haD⟩
      exact ⟨⟨hb, by rw [hufix a haD]; exact hDA a haD⟩, haD⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun a => a ∈ D)
  rw [hinside] at hsplit
  have hF : F.card = (A ∩ B.image u).card := by
    rw [← Finset.card_image_of_injective F u.injective]
    congr 1
    ext a
    simp only [Finset.mem_image, Finset.mem_inter, F, Finset.mem_filter]
    constructor
    · rintro ⟨b, ⟨hb, hub⟩, rfl⟩
      exact ⟨hub, b, hb, rfl⟩
    · rintro ⟨ha, b, hb, rfl⟩
      exact ⟨b, ⟨hb, ha⟩, rfl⟩
  have hC : C.card = (B.filter (fun a => a ∉ D)).card := Finset.card_subtype _ _
  have hE : E.card = (A.filter (fun a => a ∉ D)).card := Finset.card_subtype _ _
  rw [hY, hC, hE, hcount] at hq
  refine ⟨q, ?_, ?_⟩
  · change (B.filter (fun a => a ∈ D)).card ≤ (A ∩ B.image u).card
    omega
  · have heq : (F.filter (fun a => a ∉ D)).card =
        (A ∩ B.image u).card - (B.filter (fun a => a ∈ D)).card := by omega
    rwa [heq] at hq

end FiveTransitive.FourFixerIntersectionAverage

end CFSG
