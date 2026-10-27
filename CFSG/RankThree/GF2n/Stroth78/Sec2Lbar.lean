module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Centralizer
public import CFSG.RankThree.GF2n.Stroth78.ConjAction
public import CFSG.GroupTheory.Extraspecial2PG

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

abbrev L0 (S : Setting z E F) (a : G) : Subgroup G := QaOf a ⊓ H z

theorem La_eq_sup_L0 (S : Setting z E F) (a : G) : La S a = Q z ⊔ L0 S a := rfl

theorem L0_le_H (S : Setting z E F) (a : G) : L0 S a ≤ H z := inf_le_right

theorem map_L0_eq_Lbar (S : Setting z E F) (a : G) :
    Subgroup.map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
        ((L0 S a).subgroupOf (H z)) = Lbar S a := by
  have hQmap : Subgroup.map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
      ((Q z).subgroupOf (H z)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Lbar, La_eq_sup_L0, Subgroup.subgroupOf_sup (Q_le_H S) (L0_le_H S a),
    Subgroup.map_sup, hQmap, bot_sup_eq]

theorem card_Lbar_mul (S : Setting z E F) (a : G) :
    Nat.card (Lbar S a) * Nat.card (QaOf a ⊓ Q z : Subgroup G) =
      Nat.card (L0 S a) := by
  let f : L0 S a →* Hbar z :=
    (QuotientGroup.mk' ((Q z).subgroupOf (H z))).comp
      (Subgroup.inclusion (L0_le_H S a))
  have hrange : f.range = Lbar S a := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, map_L0_eq_Lbar]
  have hker : f.ker = (Q z).subgroupOf (L0 S a) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (QuotientGroup.mk (Subgroup.inclusion (L0_le_H S a) x) : Hbar z) = 1 ↔
      x ∈ (Q z).subgroupOf (L0 S a)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hinf : Q z ⊓ L0 S a = QaOf a ⊓ Q z := by
    rw [L0, ← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left (Q_le_H S)), inf_comm]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Q z ⊓ L0 S a ≤ L0 S a)).toEquiv,
    hinf, mul_comm] at h
  exact h

theorem sq_mem_zpowers_of_mem_Q (S : Setting z E F) {x : G} (hx : x ∈ Q z) :
    x ^ 2 ∈ Subgroup.zpowers z := by
  obtain ⟨e, he, f, hf, rfl⟩ := exists_e_f S hx
  have he2 : e * e = 1 := by
    simpa [pow_two] using S.hyp.elemAbelian.2 e he
  have hef : e * f = f * e := (S.hyp.commute e he f hf).eq
  have hsq : (e * f) ^ 2 = f ^ 2 := by
    rw [pow_two, pow_two]
    calc
      (e * f) * (e * f) = e * (f * e) * f := by group
      _ = e * (e * f) * f := by rw [hef]
      _ = (e * e) * (f * f) := by group
      _ = f * f := by rw [he2, one_mul]
  have hf2 : f * f ∈ centerIn F := by
    rw [centerIn_eq_map_center]
    exact CFSG.IsExtraspecial2.mul_self_mem_center_map S.hyp.extraspecial hf
  have hfz : f * f ∈ Subgroup.zpowers z := by
    rw [← F_centerIn_eq S]
    exact hf2
  rw [hsq, pow_two]
  exact hfz

theorem commutator_mem_zpowers_of_mem_Q (S : Setting z E F) {x y : G}
    (hx : x ∈ Q z) (hy : y ∈ Q z) : ⁅x, y⁆ ∈ Subgroup.zpowers z := by
  have h := Subgroup.commutator_mem_commutator hx hy
  rwa [Q_deriv_eq S] at h

theorem eq_one_or_z_of_mem_zpowers (S : Setting z E F) {x : G}
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [← hk, zpow_mul]
    simp [hz2]
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp [hz2]

noncomputable abbrev mkQbar (S : Setting z E F) : ↥(Q z) →* QbarOf S :=
  QuotientGroup.mk' ((ZQ z).subgroupOf (Q z))

noncomputable def QaInterImage (S : Setting z E F) (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (QbarOf S)) :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.map (mkQbar S) (A.subgroupOf (Q z))).toAddSubgroup

theorem mem_QaInterImage_iff (S : Setting z E F) {A : Subgroup G}
    {v : Additive (QbarOf S)} :
    v ∈ QaInterImage S A ↔
      ∃ y : ↥(Q z), (y : G) ∈ A ∧ mkQbar S y = Additive.toMul v := by
  simp only [QaInterImage, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup,
    Subgroup.mem_map, Subgroup.mem_subgroupOf, Additive.toMul]

theorem QaInterImage_le_orthogonal (S : Setting z E F) {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    QaInterImage S A ≤
      LinearMap.BilinForm.orthogonal (qS S).polarBilin (QaInterImage S A) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨x, hxA, hxv⟩ := (mem_QaInterImage_iff S).mp hv
  obtain ⟨y, hyA, hyu⟩ := (mem_QaInterImage_iff S).mp hu
  have hv' : v = Additive.ofMul (mkQbar S x) := (congrArg Additive.ofMul hxv).symm
  have hu' : u = Additive.ofMul (mkQbar S y) := (congrArg Additive.ofMul hyu).symm
  rw [hv', hu', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  exact (polar_q_eq_zero_iff S y x).mpr (hcomm x hxA y hyA).symm

theorem finrank_QbarOf_eq_two_mul (S : Setting z E F) {w : ℕ}
    (hw : Nat.card F = 2 ^ (2 * w + 1)) :
    finrank (ZMod 2) (Additive (QbarOf S)) = 2 * w := by
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hcardQbar : Nat.card (QbarOf S) = 2 ^ (2 * w) := by
    have hcardQZ : Nat.card (ZQ z) * Nat.card (QbarOf S) = Nat.card (Q z) := by
      have h := Subgroup.card_mul_index ((ZQ z).subgroupOf (Q z))
      rw [Subgroup.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (show ZQ z ≤ Q z from inf_le_left)).toEquiv] at h
      exact h
    have hmain : Nat.card (ZQ z) * Nat.card (QbarOf S) =
        Nat.card (ZQ z) * 2 ^ (2 * w) := by
      calc
        Nat.card (ZQ z) * Nat.card (QbarOf S) = Nat.card (Q z) := hcardQZ
        _ = Nat.card E * Nat.card F := Q_card S
        _ = Nat.card E * 2 ^ (2 * w + 1) := by rw [hw]
        _ = (Nat.card E * 2) * 2 ^ (2 * w) := by
          rw [pow_succ]
          ring
        _ = Nat.card (ZQ z) * 2 ^ (2 * w) := by rw [ZQ_card S]
    exact Nat.mul_left_cancel (Nat.card_pos (α := ZQ z)) hmain
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QbarOf S))
  rw [Nat.card_zmod,
    Nat.card_congr (Additive.toMul : Additive (QbarOf S) ≃ QbarOf S), hcardQbar] at h
  exact Nat.pow_right_injective le_rfl h.symm

theorem finrank_QaInterImage_le (S : Setting z E F) {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {w : ℕ}
    (hw : Nat.card F = 2 ^ (2 * w + 1)) :
    finrank (ZMod 2) (QaInterImage S A) ≤ w := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : Finite (Additive (QbarOf S)) := inferInstance
  haveI : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have horth := QaInterImage_le_orthogonal S hcomm
  have h1 : finrank (ZMod 2)
      ↥(LinearMap.BilinForm.orthogonal (qS S).polarBilin (QaInterImage S A)) =
      finrank (ZMod 2) (Additive (QbarOf S)) - finrank (ZMod 2) (QaInterImage S A) :=
    LinearMap.BilinForm.finrank_orthogonal (q_nondegenerate S) (QaInterImage S A)
  have h2 := Submodule.finrank_mono horth
  have hV := finrank_QbarOf_eq_two_mul S hw
  omega

end CFSG.RankThree.GF2n.Stroth78
