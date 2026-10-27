module

public import CFSG.Monster.B.Generic.CentralExtension
public import CFSG.Monster.B.E6.StandardSimple
public import CFSG.LieType.Chevalley.C2E6FieldExtensionStar

public noncomputable section

namespace CFSG.Monster.B.E6

open CFSG.Monster.B.Generic CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped commutatorElement

theorem stdGroup_isSimpleGroup :
    IsSimpleGroup stdGroup :=
  standard_twisted_e6_group_simple.2.2

theorem stdGroup_not_comm :
    ¬ IsMulCommutative stdGroup := by
  obtain ⟨x, y, hxy⟩ := standard_twisted_e6_group_simple.2.1
  exact fun h => hxy (h.is_comm.comm x y)

theorem commutator_stdGroup :
    commutator stdGroup = ⊤ :=
  @commutator_eq_top_of_isSimpleGroup _ _ stdGroup_isSimpleGroup stdGroup_not_comm

theorem center_stdGroup :
    Subgroup.center stdGroup = ⊥ :=
  @center_eq_bot_of_isSimpleGroup _ _ stdGroup_isSimpleGroup stdGroup_not_comm

abbrev Ginl :

    Subgroup GStar := (SemidirectProduct.inl : stdGroup →* GStar).range

theorem betaGroup_comm
    (a b : betaGroup) : a * b = b * a := by
  rcases mem_betaGroup_iff.1 a.2 with ha | ha <;> rcases mem_betaGroup_iff.1 b.2 with hb | hb <;>
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, ha, hb, one_mul, mul_one]

theorem commutator_GStar :
    commutator GStar = Ginl := by
  apply le_antisymm
  · show commutator GStar ≤ (SemidirectProduct.inl : stdGroup →* GStar).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, _root_.commutator_def,
      Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact betaGroup_comm _ _
  · rw [Ginl, MonoidHom.range_eq_map, ← commutator_stdGroup, _root_.commutator_def,
      Subgroup.map_commutator, _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem center_GStar :
    Subgroup.center GStar = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have key : ∀ m : stdGroup, (z.right : MulAut stdGroup) m = z.left⁻¹ * m * z.left := by
    intro m
    have h := congrArg SemidirectProduct.left
      ((Subgroup.mem_center_iff.1 hz) (SemidirectProduct.inl m))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at h
    rw [show z.left⁻¹ * m * z.left = z.left⁻¹ * (m * z.left) by group, h]
    simp only [inv_mul_cancel_left]
    rfl
  rcases mem_betaGroup_iff.1 z.right.2 with hr | hr
  · have hc : z.left ∈ Subgroup.center stdGroup := by
      rw [Subgroup.mem_center_iff]
      intro m
      have h := key m
      rw [hr, MulAut.one_apply] at h
      calc m * z.left = z.left * (z.left⁻¹ * m * z.left) := by group
        _ = z.left * m := by rw [← h]
    rw [center_stdGroup, Subgroup.mem_bot] at hc
    exact SemidirectProduct.ext hc (Subtype.ext hr)
  · exfalso
    apply betaG_ne_conj z.left⁻¹
    ext m
    rw [← hr, key m, MulAut.conj_apply, inv_inv]

theorem index_Ginl :
    Ginl.index = 2 := by
  show (SemidirectProduct.inl : stdGroup →* GStar).range.index = 2
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 SemidirectProduct.rightHom_surjective, Subgroup.card_top,
    card_betaGroup]

@[expose] def stdGroupEquivGinl :
    stdGroup ≃* Ginl :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

theorem Ginl_isSimpleGroup :
    IsSimpleGroup Ginl :=
  @MulEquiv.isSimpleGroup _ _ _ _ stdGroup_isSimpleGroup stdGroupEquivGinl.symm

theorem Ginl_not_comm :
    ¬ IsMulCommutative Ginl := fun h => stdGroup_not_comm
  ⟨⟨fun a b => stdGroupEquivGinl.injective (by rw [map_mul, map_mul, h.is_comm.comm])⟩⟩

section Cover

variable {E : Type*} [Group E] (Z : Subgroup E) [Z.Normal]

theorem map_commutator_quotient
    (θ : E ⧸ Z ≃* GStar) :
    (commutator (E ⧸ Z)).map θ.toMonoidHom = Ginl := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.2 θ.surjective, ← _root_.commutator_def,
    commutator_GStar]

theorem commutator_quotient_eq
    (θ : E ⧸ Z ≃* GStar) :
    commutator (E ⧸ Z) = Ginl.comap θ.toMonoidHom := by
  rw [← map_commutator_quotient Z θ, Subgroup.comap_map_eq_self_of_injective θ.injective]

@[expose] def commutatorQuotientEquiv
    (θ : E ⧸ Z ≃* GStar) : commutator (E ⧸ Z) ≃* stdGroup :=
  ((θ.subgroupMap (commutator (E ⧸ Z))).trans
    (MulEquiv.subgroupCongr (map_commutator_quotient Z θ))).trans stdGroupEquivGinl.symm

theorem derived_cover_of_iso
    (hZc : Z ≤ Subgroup.center E) (hZ2 : Nat.card Z = 2)
    (hZd : Z ≤ commutator E) (θ : E ⧸ Z ≃* GStar) :
    Group.IsPerfect (commutator E) ∧ (commutator E).index = 2 ∧ Subgroup.center E = Z ∧
      (Subgroup.center (commutator E)).map (commutator E).subtype = Z ∧
      Nonempty (commutator E ⧸ Z.subgroupOf (commutator E) ≃* stdGroup) ∧
      (¬ ∃ L : Subgroup E, L ≤ commutator E ∧ Z ⊓ L = ⊥ ∧ Z ⊔ L = commutator E) ∧
      Nat.card (commutator E) = 153064959367549707878400 ∧
      commutator E = Ginl.comap (θ.toMonoidHom.comp (QuotientGroup.mk' Z)) := by
  have hsimple : IsSimpleGroup (commutator (E ⧸ Z)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ Ginl_isSimpleGroup
      ((θ.subgroupMap (commutator (E ⧸ Z))).trans
        (MulEquiv.subgroupCongr (map_commutator_quotient Z θ)))
  have hnonab : ¬ IsMulCommutative (commutator (E ⧸ Z)) := fun h => stdGroup_not_comm
    ⟨⟨fun a b => (commutatorQuotientEquiv Z θ).symm.injective (by
      rw [map_mul, map_mul, h.is_comm.comm])⟩⟩
  have hindex : (commutator (E ⧸ Z)).index = 2 := by
    rw [commutator_quotient_eq Z θ, Subgroup.index_comap_of_surjective _ θ.surjective,
      index_Ginl]
  have hcenter : Subgroup.center (E ⧸ Z) = ⊥ := by
    have h := Subgroup.map_center_eq θ
    rw [center_GStar] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h
  obtain ⟨hperf, hidx, hZE, hZE', ⟨e, he⟩, hsplit⟩ :=
    central_double_extension_derived_perfect Z hZc hZ2 hZd hsimple hnonab hindex hcenter
  have hcard : Nat.card (commutator E) = 153064959367549707878400 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf (commutator E))
    have h2 : Nat.card (Z.subgroupOf (commutator E)) = 2 := by
      rw [← hZ2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZd).toEquiv
    rw [h1, h2, Nat.card_congr (e.trans (commutatorQuotientEquiv Z θ)).toEquiv, card_stdGroup]
  have hpre : commutator E = Ginl.comap (θ.toMonoidHom.comp (QuotientGroup.mk' Z)) := by
    rw [← Subgroup.comap_comap, ← commutator_quotient_eq Z θ]
    have hmap : (commutator E).map (QuotientGroup.mk' Z) = commutator (E ⧸ Z) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective Z),
        ← _root_.commutator_def]
    rw [← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hZd]
  exact ⟨hperf, hidx, hZE, hZE', ⟨e.trans (commutatorQuotientEquiv Z θ)⟩, hsplit, hcard, hpre⟩

end Cover

end CFSG.Monster.B.E6
