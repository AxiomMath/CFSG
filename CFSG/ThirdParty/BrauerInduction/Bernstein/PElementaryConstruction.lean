module

public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalFunction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-coset evaluation in Bernstein's proof

This file contains the part of Bernstein's local argument that evaluates the
induced local function at an element of the form `a * s`, where `a` is
`p`-regular and `s` is `p`-singular and commutes with `a`.

The evaluation is expressed as a fixed-point count on a finite coset space.
The resulting fixed-point formula is later combined with a congruence modulo
`p` to prove that the value is represented by an integer not divisible by `p`.
-/

namespace CFSG.BrauerInduction.Bernstein

section FixedCosetEvaluation

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

open BrauerInduction.PElementary

open Classical Subgroup in
/--
Evaluation of `f p a` at `a * s`, where `s` is `p`-singular and
commutes with `a`. The induction sum reduces to a count of elements of
`C_G(a)` that conjugate `s` into the Sylow `p`-subgroup `P_Z(a)`.
-/
lemma f_apply_mul_pSingular_eq_sum
    [CharZero k] [Fintype G]
    {a : G} (ha : IsPRegular p a) (s : G) (hs_sing : IsPSingular p s) (h_comm : Commute a s) :
    f (k := k) (p := p) a (a * s) =
    (Nat.card (E_subgroup p a) : k)⁻¹ *
      ((Finset.univ.filter
          (fun x => x ∈ centralizer ({a} : Set G) ∧ x * s * x⁻¹ ∈ P_of_Z p a)).card : k)  *
      (orderOf a : k) := by
  unfold f
  rw [ClassFun.ind_apply_eq_inv_mul_sum_mul_inv]
  simp only [Nat.card_eq_fintype_card]
  dsimp [phi]
  have hfa := isOfFinOrder_of_finite a
  have hfs := isOfFinOrder_of_finite s
  have h_sum :
      (∑ x : G, if h : x * (a * s) * x⁻¹ ∈ E_subgroup p a
                then if Group.pRegular p (x * (a * s) * x⁻¹) = a
                then (orderOf a : k) else 0 else 0) =
      ∑ x ∈ Finset.univ.filter
        (fun x => x ∈ centralizer ({a} : Set G) ∧ x * s * x⁻¹ ∈ P_of_Z p a), (orderOf a : k) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    have h_reg :
        Group.pRegular p (x * (a * s) * x⁻¹) = x * a * x⁻¹ := by
      rw [Group.pRegular_conj]
      have h_au : Group.pRegular p (a * s) = a := by
        rw [Group.pRegular_mul_eq_left_of_right_pSingular_commute p hfs hfa hs_sing h_comm.symm]
        exact Group.pRegular_eq_self_of_isPRegular p hfa ha
      rw [h_au]
    by_cases hxC : x ∈ centralizer ({a} : Set G)
    · have hax : x * a * x⁻¹ = a := by
        rw [mem_centralizer_iff] at hxC
        have h_comm_xa : x * a = a * x := by exact Eq.symm (SemiconjBy.eq (hxC a rfl))
        calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [h_comm_xa]
          _ = a := by group
      have h_reg_eq_a : Group.pRegular p (x * (a * s) * x⁻¹) = a := by rw [h_reg, hax]
      have h_xaux : x * (a * s) * x⁻¹ = a * (x * s * x⁻¹) := by
        calc x * (a * s) * x⁻¹ = (x * a * x⁻¹) * (x * s * x⁻¹) := by group
          _ = a * (x * s * x⁻¹) := by rw [hax]
      have h_E_iff : x * (a * s) * x⁻¹ ∈ E_subgroup p a ↔ x * s * x⁻¹ ∈ P_of_Z p a := by
        rw [h_xaux]
        constructor
        · intro h_in_E
          have ha_inv_in : a⁻¹ ∈ E_subgroup p a :=
              (E_subgroup p a).inv_mem (mem_sup_left (mem_zpowers a))
          have h_mul := (E_subgroup p a).mul_mem ha_inv_in h_in_E
          have h_cancel : a⁻¹ * (a * (x * s * x⁻¹)) = x * s * x⁻¹ := by group
          rw [h_cancel] at h_mul
          let h_elem := associatedSubgroup ha
          have h_sing : IsPSingular p (x * s * x⁻¹) := (IsPSingular.isConj p hs_sing) (by simp)
          let z : E_subgroup p a := ⟨x * s * x⁻¹, h_mul⟩
          have hz_sing : IsPSingular p z := by
              simpa [z] using
                (IsPSingular.subtype_iff
                  (p := p)
                  (H := E_subgroup p a)
                  (x := z)).1 h_sing
          have hz_mem_P : z ∈ h_elem.P := by exact (mem_P_iff_pSingular h_elem).mpr hz_sing
          exact mem_carrier.mp hz_mem_P
        · intro h_in_P
          have h_P_in_E : x * s * x⁻¹ ∈ E_subgroup p a := mem_sup_right h_in_P
          have h_a_in_E : a ∈ E_subgroup p a := mem_sup_left (mem_zpowers a)
          exact (E_subgroup p a).mul_mem h_a_in_E h_P_in_E
      by_cases hP : x * s * x⁻¹ ∈ P_of_Z p a
      · have hE : x * (a * s) * x⁻¹ ∈ E_subgroup p a := h_E_iff.mpr hP
        rw [dif_pos hE, if_pos h_reg_eq_a]
        simp [hxC, hP]
      · have hnE : x * (a * s) * x⁻¹ ∉ E_subgroup p a := fun h => hP (h_E_iff.mp h)
        rw [dif_neg hnE]
        simp [hP]
    · have h_reg_ne_a : Group.pRegular p (x * (a * s) * x⁻¹) ≠ a := by
        intro h_eq
        rw [h_reg] at h_eq
        apply hxC
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have h_xa : x * y = y * x := by
          calc x * y = x * y * x⁻¹ * x := by group
            _ = y * x := by rw [h_eq]
        exact Eq.symm h_xa
      by_cases hE : x * (a * s) * x⁻¹ ∈ E_subgroup p a
      · rw [dif_pos hE, if_neg h_reg_ne_a]
        simp [hxC]
      · rw [dif_neg hE]
        simp [hxC]
  rw [h_sum, Finset.sum_const, nsmul_eq_mul, mul_assoc]

open Classical Subgroup in
/--
For a `p`-regular element `a` and a commuting `p`-singular element `s`, the
value of `f p a` at `a * s` is the number of fixed cosets of `P_Z(a)` in the
centralizer of `a`.

This is the fixed-point count appearing in Bernstein's Step 8.
-/
lemma f_apply_mul_pSingular_eq_card_fixedCosets
    [CharZero k] [Finite G]
    {a : G} (ha : IsPRegular p a) (s : G) (hs_sing : IsPSingular p s) (h_comm : Commute a s) :
    f (k := k) p a (a * s) =
    (Nat.card { c : ↥(centralizer ({a} : Set G)) ⧸ (P_in_Z p a : Subgroup _) //
      (⟨s, fun y hy => by rcases hy with rfl; exact h_comm.eq⟩ :
        ↥(centralizer ({a} : Set G))) • c = c } : k) := by
  letI: Fintype G := Fintype.ofFinite G
  rw [f_apply_mul_pSingular_eq_sum p ha s hs_sing h_comm]
  let Z_group := centralizer ({a} : Set G)
  let P_Z : Subgroup Z_group := P_in_Z p a
  let s_Z : Z_group := ⟨s, fun y hy => by rcases hy with rfl; exact h_comm.eq⟩
  have h_set_card :
      (Finset.univ.filter (fun x : G => x ∈ Z_group ∧ x * s * x⁻¹ ∈ P_of_Z p a)).card =
      Nat.card { x : G // x ∈ Z_group ∧ x * s * x⁻¹ ∈ P_of_Z p a } := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  let e_inv :
    { x : G // x ∈ Z_group ∧ x * s * x⁻¹ ∈ P_of_Z p a } ≃
    { x : G // x ∈ Z_group ∧ x⁻¹ * s * x ∈ P_of_Z p a } :=
  { toFun := fun x => ⟨x.val⁻¹, by
      have hx := x.property
      refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
      have : (x.val⁻¹)⁻¹ * s * x.val⁻¹ = x.val * s * x.val⁻¹ := by rw [inv_inv]
      rw [this]
      exact hx.2⟩
    invFun := fun x => ⟨x.val⁻¹, by
      have hx := x.property
      refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
      have : x.val⁻¹ * s * (x.val⁻¹)⁻¹ = x.val⁻¹ * s * x.val := by rw [inv_inv]
      rw [this]
      exact hx.2⟩
    left_inv := fun x => Subtype.ext (inv_inv x.val)
    right_inv := fun x => Subtype.ext (inv_inv x.val) }
  have h_bij :
    Nat.card { x : G // x ∈ Z_group ∧ x * s * x⁻¹ ∈ P_of_Z p a } =
    Nat.card { x : G // x ∈ Z_group ∧ x⁻¹ * s * x ∈ P_of_Z p a } := Nat.card_congr e_inv
  let e_lift :
    { x : G // x ∈ Z_group ∧ x⁻¹ * s * x ∈ P_of_Z p a } ≃
    { x : Z_group // x⁻¹ * s_Z * x ∈ P_Z } :=
  { toFun := fun x =>
      let z_x : Z_group := ⟨x.val, x.property.1⟩
      ⟨z_x, by
        have h_mem := x.property.2
        unfold P_of_Z at h_mem
        rw [Subgroup.mem_map] at h_mem
        rcases h_mem with ⟨w, hw_mem, hw_eq⟩
        have h_eq : z_x⁻¹ * s_Z * z_x = w := by
          ext
          exact hw_eq.symm
        rw [h_eq]
        exact hw_mem⟩
    invFun := fun z =>
      ⟨z.val.val, z.val.property, by
        have h_mem := z.property
        unfold P_of_Z
        rw [Subgroup.mem_map]
        use z.val⁻¹ * s_Z * z.val
        exact ⟨h_mem, rfl⟩⟩
    left_inv := fun x => by ext; rfl
    right_inv := fun z => by ext; rfl }
  have h_card_lift :
      Nat.card { x : G // x ∈ Z_group ∧ x⁻¹ * s * x ∈ P_of_Z p a } =
      Nat.card { x : Z_group // x⁻¹ * s_Z * x ∈ P_Z } :=
    Nat.card_congr e_lift
  have h_equiv := conjMemEquiv_fixedPointsProd P_Z s_Z
  have h_card_prod :
      Nat.card { x : Z_group // x⁻¹ * s_Z * x ∈ P_Z } =
      Nat.card ({ c : Z_group ⧸ P_Z // s_Z • c = c } × P_Z) := Nat.card_congr h_equiv
  have h_card_final :
      ((Finset.univ.filter (fun x : G => x ∈ Z_group ∧ x * s * x⁻¹ ∈ P_of_Z p a)).card : k) =
      (Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) * (Nat.card P_Z : k) := by
    rw [h_set_card, h_bij, h_card_lift, h_card_prod, Nat.card_prod, Nat.cast_mul]
  rw [h_card_final]
  have hE_card :
      Nat.card (E_subgroup p a) =
        orderOf a * Nat.card (P_of_Z p a) := by
    exact E_card (p := p) (G := G) ha
  have hP_card : Nat.card (P_of_Z p a) = Nat.card P_Z := card_P_of_Z_eq_card_P_in_Z a
  have h_kE : (Nat.card (E_subgroup p a) : k) = (orderOf a : k) * (Nat.card P_Z : k) := by
    rw [hE_card, hP_card, Nat.cast_mul]
  have h_ord_ne_zero : (orderOf a : k) ≠ 0 := Nat.cast_ne_zero.mpr (orderOf_pos a).ne'
  have h_P_ne_zero : (Nat.card P_Z : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [h_kE]
  calc ((orderOf a : k) * (Nat.card P_Z : k))⁻¹ *
      ((Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) * (Nat.card P_Z : k)) * (orderOf a : k)
  _ = (orderOf a : k)⁻¹ * (Nat.card P_Z : k)⁻¹ *
      ((Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) *
      (Nat.card P_Z : k)) * (orderOf a : k) := by rw [mul_inv]
  _ = (Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) * ((Nat.card P_Z : k)⁻¹ *
        (Nat.card P_Z : k)) * ((orderOf a : k)⁻¹ * (orderOf a : k)) := by ring
  _ = (Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) * 1 * 1 :=
        by rw [inv_mul_cancel₀ h_P_ne_zero, inv_mul_cancel₀ h_ord_ne_zero]
  _ = (Nat.card { c : Z_group ⧸ P_Z // s_Z • c = c } : k) := by ring

end FixedCosetEvaluation


end CFSG.BrauerInduction.Bernstein
