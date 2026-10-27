module

public import CFSG.Monster.B.E6.FieldInvF4Cent
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem betaGroup_mul_comm
    (b c : betaGroup) : b * c = c * b := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp b.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp c.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn]
  exact (Commute.zpow_zpow_self betaG m n).eq

abbrev betaElt' :
    betaGroup := ⟨betaG, Subgroup.mem_zpowers _⟩

theorem betaElt'_mul_self :
    betaElt' * betaElt' = 1 :=
  Subtype.ext betaG_mul_self

section Star

variable {H : Subgroup stdGroup}

theorem apply_of_mem_betaGroup
    (hH : ∀ h ∈ H, betaG h = h) (b : betaGroup) {h : stdGroup}
    (hh : h ∈ H) : (b : MulAut stdGroup) h = h := by
  rcases mem_betaGroup_iff.mp b.2 with e | e <;> rw [e]
  · rfl
  · exact hH h hh

@[expose] def starSub
    (hH : ∀ h ∈ H, betaG h = h) : Subgroup GStar where
  carrier := {γ | γ.left ∈ H}
  mul_mem' {γ γ'} hγ hγ' := by
    change γ.left * (γ.right : MulAut stdGroup) γ'.left ∈ H
    rw [apply_of_mem_betaGroup hH γ.right hγ']
    exact H.mul_mem hγ hγ'
  one_mem' := H.one_mem
  inv_mem' {γ} hγ := by
    change ((γ.right⁻¹ : betaGroup) : MulAut stdGroup) γ.left⁻¹ ∈ H
    rw [apply_of_mem_betaGroup hH _ (H.inv_mem hγ)]
    exact H.inv_mem hγ

theorem mem_starSub
    (hH : ∀ h ∈ H, betaG h = h) {γ : GStar} :
    γ ∈ starSub hH ↔ γ.left ∈ H :=
  Iff.rfl

@[expose] def prodStar
    (hH : ∀ h ∈ H, betaG h = h) : H × betaGroup ≃* starSub hH where
  toFun x := ⟨⟨(x.1 : stdGroup), x.2⟩, x.1.2⟩
  invFun γ := (⟨(γ : GStar).left, γ.2⟩, (γ : GStar).right)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    refine Subtype.ext (SemidirectProduct.ext ?_ rfl)
    change ((x.1 : stdGroup) * (y.1 : stdGroup)) =
      (x.1 : stdGroup) * ((x.2 : betaGroup) : MulAut stdGroup) (y.1 : stdGroup)
    rw [apply_of_mem_betaGroup hH x.2 y.1.2]

theorem coe_prodStar
    (hH : ∀ h ∈ H, betaG h = h) (x : H × betaGroup) :
    (prodStar hH x : GStar) = SemidirectProduct.inl (x.1 : stdGroup) * SemidirectProduct.inr x.2 :=
  SemidirectProduct.ext (by simp [prodStar]) (by simp [prodStar])

theorem card_starSub
    (hH : ∀ h ∈ H, betaG h = h) :
    Nat.card (starSub hH) = 2 * Nat.card H := by
  rw [← Nat.card_congr (prodStar hH).toEquiv, Nat.card_prod, card_betaGroup, mul_comm]

end Star

theorem groupJ_fixed :
    ∀ h ∈ groupJ.subgroupOf stdGroup, betaG h = h := fun h hh =>
  (mem_groupJ_iff_betaG h).mp hh

theorem mem_centralizer_betaStarElt_iff
    (γ : GStar) :
    γ ∈ Subgroup.centralizer {betaStarElt} ↔ betaG γ.left = γ.left := by
  rw [Subgroup.mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inr,
    SemidirectProduct.right_inr, Subgroup.subtype_apply, map_one, one_mul, mul_one]
  constructor
  · exact fun h => h.1.symm
  · exact fun h => ⟨h.symm, betaGroup_mul_comm _ _⟩

theorem centralizer_betaStarElt :
    Subgroup.centralizer {betaStarElt} = starSub groupJ_fixed := by
  ext γ
  rw [mem_centralizer_betaStarElt_iff, mem_starSub, Subgroup.mem_subgroupOf, mem_groupJ_iff_betaG]

abbrev tStar :
    GStar := rootStar * betaStarElt

theorem diagE6GL_mul_self :
    diagE6GL * diagE6GL = 1 :=
  diagramMap_E6_mul_self

theorem diagE6GL_conj_eq_betaGL
    {g : ModGL Tag.E6 K} (hg : g ∈ stdGroup) :
    diagE6GL * g * diagE6GL⁻¹ = betaGL g :=
  diagramMap_conj_eq_entrywise (fun c => bar_bar c) (graphFixedRootGroup_le _ _ _ hg)

theorem rootInvM_mul_betaGL_eq_iff
    {g : ModGL Tag.E6 K} (hg : g ∈ stdGroup) :
    rootInvM * betaGL g = g * rootInvM ↔ g ∈ centJ := by
  constructor
  · intro h
    obtain ⟨-, -, -, hset⟩ :=
      even_E6_highest_root_graph_fixed_centralizer_intersection K (ringChar.eq K 2) one_ne_zero
    have hζ : rootInvM * (diagE6GL * g * diagE6GL⁻¹) * rootInvM⁻¹ = g := by
      rw [diagE6GL_conj_eq_betaGL hg, h, mul_inv_cancel_right]
    have hmem : g ∈ {g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) |
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
            (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ = g} :=
      ⟨(graphFixedRootGroup_le _ _ _ hg).1, hζ⟩
    rw [hset] at hmem
    have hβ : betaGL g = g := by
      rw [← diagE6GL_conj_eq_betaGL hg]
      exact hmem.1.2
    refine ⟨⟨hg, hβ⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← h, hβ]
  · rintro ⟨hJ, hc⟩
    rw [hJ.2]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm

theorem centJ_fixed :
    ∀ h ∈ centJ.subgroupOf stdGroup, betaG h = h := fun h hh =>
  groupJ_fixed h (centJ_le_groupJ hh)

theorem coe_rootInv_mul_betaG
    (g : stdGroup) :
    ((rootInv * betaG g : stdGroup) : ModGL Tag.E6 K) = rootInvM * betaGL (g : ModGL Tag.E6 K) := by
  rw [Subgroup.coe_mul, coe_rootInv, coe_betaG_apply]

theorem coe_mul_rootInv
    (g : stdGroup) :
    ((g * rootInv : stdGroup) : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) * rootInvM := by
  rw [Subgroup.coe_mul, coe_rootInv]

theorem mem_centralizer_tStar_iff
    (γ : GStar) :
    γ ∈ Subgroup.centralizer {tStar} ↔ rootInv * betaG γ.left = γ.left * rootInv := by
  rw [Subgroup.mem_centralizer_singleton_iff, SemidirectProduct.ext_iff]
  simp only [tStar, rootStar, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, Subgroup.subtype_apply, map_one, one_mul, mul_one]
  rw [apply_rootInv_of_mem_betaGroup]
  constructor
  · exact fun h => h.1.symm
  · exact fun h => ⟨h.symm, betaGroup_mul_comm _ _⟩

theorem centralizer_tStar :
    Subgroup.centralizer {tStar} = starSub centJ_fixed := by
  ext γ
  rw [mem_centralizer_tStar_iff, mem_starSub, Subgroup.mem_subgroupOf,
    ← rootInvM_mul_betaGL_eq_iff γ.left.2, ← coe_rootInv_mul_betaG, ← coe_mul_rootInv]
  exact Subtype.ext_iff

theorem card_groupJ_subgroupOf :
    Nat.card (groupJ.subgroupOf stdGroup) = Nat.card groupJ :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe groupJ_le_stdGroup).toEquiv

theorem card_centJ_subgroupOf :
    Nat.card (centJ.subgroupOf stdGroup) = Nat.card centJ :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centJ_le_groupJ.trans groupJ_le_stdGroup)).toEquiv

theorem card_centralizer_tStar :
    Nat.card (Subgroup.centralizer {tStar}) = 95126814720 := by
  rw [centralizer_tStar, card_starSub, card_centJ_subgroupOf, card_centJ]

theorem card_centralizer_conj {M : Type*} [Group M] (h x : M) :
    Nat.card (Subgroup.centralizer ({h * x * h⁻¹} : Set M)) =
      Nat.card (Subgroup.centralizer ({x} : Set M)) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨h⁻¹ * z * h, ?_⟩
      invFun := fun y => ⟨h * y * h⁻¹, ?_⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have hz := Subgroup.mem_centralizer_singleton_iff.mp z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * z * h * x = h⁻¹ * (z * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * z) * h := by rw [hz]
      _ = x * (h⁻¹ * z * h) := by group
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * y * h⁻¹ * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
      _ = h * (x * y) * h⁻¹ := by rw [hy]
      _ = h * x * h⁻¹ * (h * y * h⁻¹) := by group

end CFSG.Monster.B.E6.FieldInvF4
