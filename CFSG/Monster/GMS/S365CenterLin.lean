module

public import CFSG.Monster.GMS.S365Root

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀)

namespace S365

theorem eq_one_of_forall_act (A : Co1) (h : ∀ v, co1Act A v = v) : A = 1 := by
  refine Units.ext (Subtype.ext ?_)
  rw [Matrix.ext_iff_mulVec]
  intro v
  simp only [Units.val_one, Submonoid.coe_one, Matrix.one_mulVec]
  exact h v

theorem mem_of_forall_perp
    {S : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {x : Fin 24 → ZMod 2}
    (h : ∀ a, (∀ s ∈ S, bil₀ a s = 0) → bil₀ x a = 0) : x ∈ S := by
  by_contra hx
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  obtain ⟨a, ha⟩ := Leech.exists_bil₀_eq_of_additive (f := fun v => f v)
    (fun u v => map_add f u v)
  have hperp : ∀ s ∈ S, bil₀ a s = 0 := by
    intro s hs
    have hmem : f s ∈ S.map f := ⟨s, hs, rfl⟩
    rw [hf, Submodule.mem_bot] at hmem
    rw [← ha]
    exact hmem
  apply hfx
  rw [ha, CFSG.Sporadic.Co1.Module.bil₀_comm]
  exact h a hperp

theorem co1Fix_ncard_le
    {s : Co1} (hs : orderOf s = 2) : (co1Fix s).ncard ≤ 2 ^ 16 := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := co1_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, -⟩ := hrep
  rcases hcls s hs with h | h | h
  · have e : (co1Fix sA).ncard = 2 ^ 16 := hfA
    rw [(co1Inv_isConj_invariants h).1, e]
  · have e : (co1Fix sB).ncard = 2 ^ 12 := hfB
    rw [(co1Inv_isConj_invariants h).1, e]
    norm_num
  · have e : (co1Fix sC).ncard = 2 ^ 12 := hfC
    rw [(co1Inv_isConj_invariants h).1, e]
    norm_num

theorem eq_one_of_fix_perp_three
    (A : Co1) (e : Fin 3 → Fin 24 → ZMod 2)
    (hfix : ∀ i, co1Act A (e i) = e i)
    (hW : ∀ v, (∀ i, bil₀ v (e i) = 0) → co1Act A v = v) : A = 1 := by
  classical
  set U : Submodule (ZMod 2) (Fin 24 → ZMod 2) := Submodule.span (ZMod 2) (Set.range e) with hU
  let T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := co1Act A - LinearMap.id
  have hT : ∀ v, T v = co1Act A v + v := fun v => by
    simp only [T, LinearMap.sub_apply, LinearMap.id_apply]
    exact Leech.sub_eq_add _ _
  have hUfix : ∀ c ∈ U, co1Act A c = c := by
    intro c hc
    have hle : U ≤ LinearMap.ker T := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hT, hfix i]
      exact CharTwo.add_self_eq_zero _
    have h0 := hle hc
    rw [LinearMap.mem_ker, hT] at h0
    exact (eq_neg_of_add_eq_zero_left h0).trans (Leech.neg_eq_self c)
  have hmem : ∀ v, co1Act A v + v ∈ U := by
    intro v
    refine mem_of_forall_perp fun a ha => ?_
    have ha' : ∀ i, bil₀ a (e i) = 0 := fun i => ha _ (Submodule.subset_span ⟨i, rfl⟩)
    have hAa := hW a ha'
    rw [Leech.bil₀_add_left]
    have h1 : bil₀ (co1Act A v) a = bil₀ v a := by
      have := Leech.bil₀_co1Act A v a
      rwa [hAa] at this
    rw [h1]
    exact CharTwo.add_self_eq_zero _
  have hsq : ∀ v, co1Act A (co1Act A v) = v := by
    intro v
    have h1 := hUfix _ (hmem v)
    rw [map_add] at h1
    exact add_right_cancel (h1.trans (add_comm _ _))
  have hAA : A * A = 1 := eq_one_of_forall_act (A * A) fun v => by
    rw [map_mul, Module.End.mul_apply]
    exact hsq v
  by_contra hA1
  have hord : orderOf A = 2 := by
    refine orderOf_eq_prime ?_ hA1
    rw [pow_two]
    exact hAA
  have hle := co1Fix_ncard_le hord
  let f : (Fin 24 → ZMod 2) →+ (Fin 24 → ZMod 2) := T.toAddMonoidHom
  have hcard := AddSubgroup.card_ker_mul_card_range f
  have hker : ((AddMonoidHom.ker f : AddSubgroup (Fin 24 → ZMod 2)) : Set (Fin 24 → ZMod 2)) =
      co1Fix A := by
    ext v
    show T v = 0 ↔ co1Act A v = v
    rw [hT]
    constructor
    · intro h0
      exact (eq_neg_of_add_eq_zero_left h0).trans (Leech.neg_eq_self v)
    · intro h0
      rw [h0]
      exact CharTwo.add_self_eq_zero _
  have hrange : Nat.card ↥(AddMonoidHom.range f) ≤ 8 := by
    have hsub : ((AddMonoidHom.range f : AddSubgroup (Fin 24 → ZMod 2)) :
        Set (Fin 24 → ZMod 2)) ⊆
        (fun c : Fin 3 → ZMod 2 => ∑ i, c i • e i) '' Set.univ := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hmem v)
      exact ⟨c, Set.mem_univ _, by
        show ∑ i, c i • e i = T v
        rw [hc, hT]⟩
    have h1 : Nat.card ↥(AddMonoidHom.range f) =
        ((AddMonoidHom.range f : AddSubgroup (Fin 24 → ZMod 2)) :
          Set (Fin 24 → ZMod 2)).ncard := Nat.card_coe_set_eq _
    rw [h1]
    calc _ ≤ ((fun c : Fin 3 → ZMod 2 => ∑ i, c i • e i) '' Set.univ).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Set.univ : Set (Fin 3 → ZMod 2)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 8 := by
        rw [Set.ncard_univ]
        simp [Nat.card_eq_fintype_card, ZMod.card]
  have hker' : Nat.card ↥(AddMonoidHom.ker f) = (co1Fix A).ncard := by
    rw [← hker]
    exact Nat.card_coe_set_eq _
  have hV : Nat.card (Fin 24 → ZMod 2) = 2 ^ 24 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hker', hV] at hcard
  have := Nat.mul_le_mul hle hrange
  omega

end S365

end CFSG.Monster.GMS
