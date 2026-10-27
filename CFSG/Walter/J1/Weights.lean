module

public import CFSG.Walter.J1.CosetClassify
public import CFSG.Walter.J1.Seven

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem weights (Q : Sylow 2 G) {H : Subgroup G}
    (hH : H = Subgroup.normalizer ((Q : Subgroup G) : Set G)) {u : G} (hu : orderOf u = 2)
    (huH : u ∉ H) {n : ℕ} (hn : cosetInvolutions H (rightCoset H u) = n) :
    (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 7) ∧
    invOrd H u 2 = (if n = 2 then 1 else 0) + (if n = 6 then 1 else 0) ∧
    invOrd H u 6 = (if n = 6 then 2 else 0) ∧
    invOrd H u 3 = (if n = 3 then 2 else 0) + (if n = 6 then 2 else 0) ∧
    invOrd H u 7 = (if n = 7 then 6 else 0) ∧
    (n = 1 → (kap H u = 0 ∨ kap H u = 2) ∧ (kap H u = 2 ↔ ∃ g ∈ H, g ≠ 1 ∧ g * u = u * g)) ∧
    (n = 3 ∨ n = 6 → kap H u = 0) := by
  have hn' : n = 1 + invOrd H u 2 + invOrd H u 3 + invOrd H u 6 + invOrd H u 7 := by
    rw [← hn, cosetInvolutions_eq (mem_involutions.mpr hu) huH]
    subst hH
    exact h.ncard_inv_eq Q u
  rcases h.classify Q hH hu huH with ⟨h2, h3, h6, h7, hk, hk2⟩ | ⟨h2, h3, h6, h7, hk⟩ |
      ⟨h2, h3, h6, h7, hk⟩ | ⟨h2, h3, h6, h7, hk⟩ | ⟨h2, h3, h6, h7⟩ <;>
    rw [h2, h3, h6, h7] at hn' <;> norm_num at hn' <;> subst hn'
  · exact ⟨by norm_num, by simp [h2], by simp [h6], by simp [h3], by simp [h7],
      fun _ => ⟨hk, hk2⟩, fun h0 => by omega⟩
  · exact ⟨by norm_num, by simp [h2], by simp [h6], by simp [h3], by simp [h7],
      fun h0 => by omega, fun h0 => by omega⟩
  · exact ⟨by norm_num, by simp [h2], by simp [h6], by simp [h3], by simp [h7],
      fun h0 => by omega, fun _ => hk⟩
  · exact ⟨by norm_num, by simp [h2], by simp [h6], by simp [h3], by simp [h7],
      fun h0 => by omega, fun _ => hk⟩
  · exact ⟨by norm_num, by simp [h2], by simp [h6], by simp [h3], by simp [h7],
      fun h0 => by omega, fun h0 => by omega⟩

include h in
theorem ncard_involutions_mul : {u : G | orderOf u = 2}.ncard * 120 = Nat.card G := by
  have horbit : MulAction.orbit (ConjAct G) h.t = {u : G | orderOf u = 2} := by
    ext u
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩
      rw [ConjAct.smul_def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
    · intro hu
      obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_of_orderOf_eq_two h.orderOf_t hu)
      exact ⟨ConjAct.toConjAct c, by rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hc]⟩
  have := (MulAction.stabilizer (ConjAct G) h.t).card_mul_index
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    h.card_centralizer, horbit] at this
  rw [mul_comm, this]
  exact Nat.card_congr ConjAct.toConjAct.toEquiv.symm

theorem ncard_involutions_mod_five {P : Subgroup G} (hP : Nat.card P = 5) :
    {u : G | orderOf u = 2}.ncard % 5 =
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (P : Set G)}.ncard % 5 := by
  set S := {u : G | orderOf u = 2}
  have hS : ∀ k ∈ P, ∀ u ∈ S, k * u * k⁻¹ ∈ S := fun k _ u hu => by
    change orderOf (k * u * k⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu
  let := conjActionElems P S hS
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have : Finite S := Set.toFinite _ |>.to_subtype
  have hmod := hP5.card_modEq_card_fixedPoints S
  have hfix : Nat.card (MulAction.fixedPoints P S) =
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (P : Set G)}.ncard := by
    have hset : {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (P : Set G)} =
        (fun u : S => (u : G)) '' (MulAction.fixedPoints P S) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hu, huC⟩
        refine ⟨⟨u, hu⟩, ?_, rfl⟩
        rintro ⟨k, hk⟩
        apply Subtype.ext
        change k * u * k⁻¹ = u
        rw [Subgroup.mem_centralizer_iff.mp huC k hk, mul_inv_cancel_right]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have := congrArg Subtype.val (hv ⟨k, hk⟩)
        change k * v * k⁻¹ = v at this
        calc k * (v : G) = k * v * k⁻¹ * k := by group
          _ = v * k := by rw [this]
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq]
  rw [hfix, Nat.card_coe_set_eq] at hmod
  exact hmod

end JankoHyp

end CFSG.Walter.J1
