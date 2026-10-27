module

public import CFSG.Monster.B.E6.FieldInvF4Coset
public import CFSG.Monster.B.E6.StdF4Degree
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem exists_groupJ_mulEquiv_F4 :
    ∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      ∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g := by
  obtain ⟨-, e, he⟩ := (even_E6_twisted_E6_canonical_graph_fixed_subgroup 1 le_rfl (ZMod 2) K
    (by simp) CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2
  let e₁ : groupJ ≃* (twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))).map
      (baseChangeGL (algebraMap (ZMod 2) K)) := MulEquiv.subgroupCongr groupJ_eq_canonical
  exact ⟨e₁.trans e, fun g x hx => he g (e₁ x) hx⟩

theorem card_groupJ :
    Nat.card groupJ = 3311126603366400 := by
  obtain ⟨Ψ, -⟩ := exists_groupJ_mulEquiv_F4
  rw [Nat.card_congr Ψ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    Nat.card_zmod]
  norm_num [CFSG.Open.ordF4]

theorem coe_mul_tJ
    (x : groupJ) : ((x * tJ : groupJ) : ModGL Tag.E6 K) = x * rootInvM :=
  Subgroup.coe_mul _ x tJ

theorem coe_tJ_mul
    (x : groupJ) : ((tJ * x : groupJ) : ModGL Tag.E6 K) = rootInvM * x :=
  Subgroup.coe_mul _ tJ x

theorem card_centralizer_tJ :
    Nat.card (Subgroup.centralizer ({tJ} : Set groupJ)) = 47563407360 := by
  rw [← card_centJ]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · rw [← coe_mul_tJ, ← coe_tJ_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2]
  · refine Subtype.ext ?_
    rw [coe_mul_tJ, coe_tJ_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2

theorem card_centralizer_betaStarElt :
    Nat.card (Subgroup.centralizer {betaStarElt}) = 6622253206732800 := by
  rw [centralizer_betaStarElt, card_starSub, card_groupJ_subgroupOf, card_groupJ]

theorem not_conj_betaStarElt_tStar
    (h : GStar) : h * betaStarElt * h⁻¹ ≠ tStar := by
  intro e
  have := card_centralizer_conj h betaStarElt
  rw [e, card_centralizer_tStar, card_centralizer_betaStarElt] at this
  norm_num at this

theorem xor_conj_of_sq_eq_one
    {a : stdGroup}
    (ha : (SemidirectProduct.inl a * betaStarElt : GStar) ^ 2 = 1) :
    Xor (∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
        (SemidirectProduct.inl g)⁻¹ = betaStarElt)
      (∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
        (SemidirectProduct.inl g)⁻¹ = tStar) := by
  set x : GStar := SemidirectProduct.inl a * betaStarElt
  rcases exists_conj_of_sq_eq_one ha with h | h
  · refine Or.inl ⟨h, ?_⟩
    rintro ⟨g', hg'⟩
    obtain ⟨g, hg⟩ := h
    refine not_conj_betaStarElt_tStar
      (SemidirectProduct.inl g' * (SemidirectProduct.inl g)⁻¹) ?_
    calc SemidirectProduct.inl g' * (SemidirectProduct.inl g)⁻¹ * betaStarElt *
          (SemidirectProduct.inl g' * (SemidirectProduct.inl g)⁻¹)⁻¹ =
        SemidirectProduct.inl g' * (SemidirectProduct.inl g)⁻¹ *
          (SemidirectProduct.inl g * x * (SemidirectProduct.inl g)⁻¹) *
            (SemidirectProduct.inl g' * (SemidirectProduct.inl g)⁻¹)⁻¹ := by rw [hg]
      _ = SemidirectProduct.inl g' * x * (SemidirectProduct.inl g')⁻¹ := by group
      _ = tStar := hg'
  · refine Or.inr ⟨h, ?_⟩
    rintro ⟨g', hg'⟩
    obtain ⟨g, hg⟩ := h
    refine not_conj_betaStarElt_tStar
      (SemidirectProduct.inl g * (SemidirectProduct.inl g')⁻¹) ?_
    calc SemidirectProduct.inl g * (SemidirectProduct.inl g')⁻¹ * betaStarElt *
          (SemidirectProduct.inl g * (SemidirectProduct.inl g')⁻¹)⁻¹ =
        SemidirectProduct.inl g * (SemidirectProduct.inl g')⁻¹ *
          (SemidirectProduct.inl g' * x * (SemidirectProduct.inl g')⁻¹) *
            (SemidirectProduct.inl g * (SemidirectProduct.inl g')⁻¹)⁻¹ := by rw [hg']
      _ = SemidirectProduct.inl g * x * (SemidirectProduct.inl g)⁻¹ := by group
      _ = tStar := hg

theorem orderOf_betaStarElt :
    orderOf betaStarElt = 2 := by
  refine orderOf_eq_prime ?_ fun h => betaG_ne_one (congrArg Subtype.val
    (congrArg SemidirectProduct.right h))
  rw [pow_two, ← map_mul, betaElt'_mul_self, map_one]

theorem orderOf_tStar :
    orderOf tStar = 2 := by
  refine orderOf_eq_prime ?_ fun h => betaG_ne_one (congrArg Subtype.val
    (congrArg SemidirectProduct.right h))
  rw [tStar, rootStar, sq_inl_mul_betaStarElt,
    show betaG rootInv = rootInv from apply_rootInv_of_mem_betaGroup betaElt', rootInv_mul_self,
    map_one]

theorem standard_field_involution_F4_and_root_centralizer_orders :
    (∀ g : stdGroup, (g : ModGL Tag.E6 K) ∈ groupJ ↔
      Commute (SemidirectProduct.inl g : GStar) betaStarElt) ∧
    (groupJ : Subgroup (ModGL TwistTag.E6.tag K)) =
      (twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))).map
        (baseChangeGL (algebraMap (ZMod 2) K)) ∧
    (∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      ∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g) ∧
    Nat.card groupJ = 3311126603366400 ∧
    Nat.card (Subgroup.centralizer ({tJ} : Set groupJ)) = 47563407360 ∧
    (∀ γ : GStar, γ ∈ Subgroup.centralizer {betaStarElt} ↔
      (γ.left : ModGL Tag.E6 K) ∈ groupJ) ∧
    (∃ e : (groupJ.subgroupOf stdGroup) × betaGroup ≃* Subgroup.centralizer {betaStarElt},
      ∀ x, (e x : GStar) =
        SemidirectProduct.inl (x.1 : stdGroup) * SemidirectProduct.inr x.2) ∧
    Nat.card (Subgroup.centralizer {betaStarElt}) = 6622253206732800 ∧
    (∀ γ : GStar, γ ∈ Subgroup.centralizer {rootStar * betaStarElt} ↔
      (γ.left : ModGL Tag.E6 K) ∈ groupJ ⊓ Subgroup.centralizer {rootInvM}) ∧
    (∃ e : ((groupJ ⊓ Subgroup.centralizer {rootInvM}).subgroupOf stdGroup) × betaGroup ≃*
        Subgroup.centralizer {rootStar * betaStarElt},
      ∀ x, (e x : GStar) =
        SemidirectProduct.inl (x.1 : stdGroup) * SemidirectProduct.inr x.2) ∧
    Nat.card (Subgroup.centralizer {rootStar * betaStarElt}) = 95126814720 ∧
    orderOf betaStarElt = 2 ∧ orderOf (rootStar * betaStarElt) = 2 ∧
    ∀ a : stdGroup, (SemidirectProduct.inl a * betaStarElt : GStar) ^ 2 = 1 →
      Xor (∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
          (SemidirectProduct.inl g)⁻¹ = betaStarElt)
        (∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
          (SemidirectProduct.inl g)⁻¹ = rootStar * betaStarElt) :=
  ⟨mem_groupJ_iff_commute, groupJ_eq_canonical, exists_groupJ_mulEquiv_F4, card_groupJ,
    card_centralizer_tJ,
    fun γ => by
      rw [centralizer_betaStarElt, mem_starSub, Subgroup.mem_subgroupOf],
    ⟨(prodStar groupJ_fixed).trans (MulEquiv.subgroupCongr centralizer_betaStarElt.symm),
      fun x => coe_prodStar groupJ_fixed x⟩,
    card_centralizer_betaStarElt,
    fun γ => by
      rw [centralizer_tStar, mem_starSub, Subgroup.mem_subgroupOf],
    ⟨(prodStar centJ_fixed).trans (MulEquiv.subgroupCongr centralizer_tStar.symm),
      fun x => coe_prodStar centJ_fixed x⟩,
    card_centralizer_tStar, orderOf_betaStarElt, orderOf_tStar,
    fun _ ha => xor_conj_of_sq_eq_one ha⟩

end CFSG.Monster.B.E6.FieldInvF4
