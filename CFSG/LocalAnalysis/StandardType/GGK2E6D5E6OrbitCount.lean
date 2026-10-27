module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem linear_orbit_card_add_one_le
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {Q H : Subgroup (V ≃ₗ[ZMod 3] V)} (hQH : Q ≤ H)
    {y : V} (hQy : ∀ g ∈ Q, g y = y)
    {t : V ≃ₗ[ZMod 3] V} (ht : t ∈ H) (hty : t y ≠ y) :
    Nat.card (MulAction.orbit Q (t y)) + 1 ≤ Nat.card (MulAction.orbit H y) := by
  classical
  let O := MulAction.orbit Q (t y)
  let Y := MulAction.orbit H y
  have hnot : y ∉ O := by
    intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    apply hty
    apply g.val.injective
    exact hg.trans (hQy g.val g.property).symm
  have hsub : O ⊆ Y := by
    intro z hz
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hz
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨g.val * t, H.mul_mem (hQH g.property) ht⟩, ?_⟩
    exact hg
  let f : Option O → Y := fun s =>
    match s with
    | none => ⟨y, MulAction.mem_orbit_self y⟩
    | some z => ⟨z.val, hsub z.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        exfalso
        apply hnot
        have heq : y = b.val := congrArg Subtype.val hab
        exact heq.symm ▸ b.property
    | some a =>
      cases b with
      | none =>
        exfalso
        apply hnot
        have heq : a.val = y := congrArg Subtype.val hab
        exact heq ▸ a.property
      | some b =>
        congr 1
        exact Subtype.ext (congrArg (fun z : Y => (z : V)) hab)
  have hcard : Nat.card (Option O) = Nat.card O + 1 := by
    letI : Fintype O := Fintype.ofFinite O
    simp [Nat.card_eq_fintype_card]
  rw [← hcard]
  exact Nat.card_le_card_of_injective f hf

theorem linear_nonzero_orbit_card_lt
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) {x : V} (hx : x ≠ 0) :
    Nat.card (MulAction.orbit H x) < Nat.card V := by
  classical
  let f : MulAction.orbit H x → {v : V // v ≠ 0} := fun z =>
    ⟨z.val, by
      intro hz
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp z.property
      have hg0 : g.val x = 0 := hg.trans hz
      apply hx
      have heq := congrArg g.val.symm hg0
      simpa using heq⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {v : V // v ≠ 0} => (z : V)) hab)
  exact (Nat.card_le_card_of_injective f hf).trans_lt
    (Finite.card_subtype_lt (x := (0 : V)) (by simp))

theorem d5_e6_join_false_of_actual_counts
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {Q H : Subgroup (V ≃ₗ[ZMod 3] V)} (hQH : Q ≤ H)
    (hQcard : Nat.card Q = 51840) (hV : Nat.card V = 3 ^ 6)
    {x y : V} (hx : x ≠ 0) (hQy : ∀ g ∈ Q, g y = y)
    (hst : Nat.card (MulAction.stabilizer H x) ≤ 3840)
    {t : V ≃ₗ[ZMod 3] V} (ht : t ∈ H) (hty : t y ≠ y)
    (ho : 72 ≤ Nat.card (MulAction.orbit Q (t y))) : False := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (congrFun h))
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (MulAction.orbit H x) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer H x) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit H y) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer H y) := Fintype.ofFinite _
  have hxcount : Nat.card (MulAction.orbit H x) *
      Nat.card (MulAction.stabilizer H x) = Nat.card H := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group H x
  have hycount : Nat.card (MulAction.orbit H y) *
      Nat.card (MulAction.stabilizer H y) = Nat.card H := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group H y
  have hxo : Nat.card (MulAction.orbit H x) ≤ 728 := by
    have hl := linear_nonzero_orbit_card_lt H hx
    rw [hV] at hl
    change Nat.card (MulAction.orbit H x) < 729 at hl
    omega
  have hyo : 73 ≤ Nat.card (MulAction.orbit H y) := by
    have hl := linear_orbit_card_add_one_le hQH hQy ht hty
    omega
  have hQst : 51840 ≤ Nat.card (MulAction.stabilizer H y) := by
    let f : Q → MulAction.stabilizer H y := fun g =>
      ⟨⟨g.val, hQH g.property⟩,
        MulAction.mem_stabilizer_iff.mpr (hQy g.val g.property)⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : MulAction.stabilizer H y => z.val.val) hab)
    rw [← hQcard]
    exact Nat.card_le_card_of_injective f hf
  have hu : Nat.card H ≤ 728 * 3840 := by
    rw [← hxcount]
    exact Nat.mul_le_mul hxo hst
  have hl : 73 * 51840 ≤ Nat.card H := by
    rw [← hycount]
    exact Nat.mul_le_mul hyo hQst
  norm_num at hu hl
  omega

end CFSG.StandardType

end
