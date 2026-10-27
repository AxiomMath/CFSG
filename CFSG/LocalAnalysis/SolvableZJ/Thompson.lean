module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Foundations.MaxOrderThompsonImage
public import CFSG.LocalAnalysis.SignalizerFunctor.AxiomaticZJCharacteristic

public section

namespace CFSG

open SignalizerFunctor

section Thompson

variable (S : Type*) [Group S] [Finite S]

@[expose, reducible]
def maximalOrderAbelianSubgroups : Set (Subgroup S) :=
  {B | IsMaxCardAbelian B}

theorem maximalOrderAbelianSubgroups_nonempty :
    (maximalOrderAbelianSubgroups S).Nonempty :=
  Helpers.maximum_order_abelian_family_nonempty

@[reducible]
noncomputable def maximalAbelianOrder : ℕ :=
  maxAbelianOrder S

@[expose, reducible]
noncomputable def thompsonOrder : Subgroup S :=
  maxCardThompson S

@[expose, reducible]
noncomputable def centerThompsonOrder : Subgroup S :=
  maxCardZJ S

end Thompson

@[expose, reducible]
noncomputable def embeddedThompsonCenter {G : Type*} [Group G] (U : Subgroup G) : Subgroup G :=
  Helpers.embeddedOrderThompsonCenter U

theorem thompsonOrder_isomorphism {S T : Type*} [Group S] [Finite S]
    [Group T] [Finite T] (φ : S ≃* T) :
    maximalAbelianOrder S = maximalAbelianOrder T ∧
    (Subgroup.map φ.toMonoidHom '' maximalOrderAbelianSubgroups S) =
      maximalOrderAbelianSubgroups T ∧
    (thompsonOrder S).map φ.toMonoidHom = thompsonOrder T ∧
    (centerThompsonOrder S).map φ.toMonoidHom = centerThompsonOrder T ∧
    (thompsonOrder S).Characteristic ∧ (centerThompsonOrder S).Characteristic := by
  have hfamily : (Subgroup.map φ.toMonoidHom '' maximalOrderAbelianSubgroups S) =
      maximalOrderAbelianSubgroups T := by
    ext C
    refine ⟨fun ⟨B, hB, hBC⟩ => hBC ▸ Helpers.maximum_order_abelian_family_map φ B hB,
      fun hC => ⟨C.map φ.symm.toMonoidHom,
        Helpers.maximum_order_abelian_family_map φ.symm C hC, ?_⟩⟩
    have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id T := by ext; simp
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  exact ⟨maxAbelianOrder_eq_of_mulEquiv φ, hfamily,
    Helpers.order_thompson_subgroup_map φ, Helpers.order_thompson_center_map φ,
    Subgroup.characteristic_iff_map_eq.mpr fun ψ => Helpers.order_thompson_subgroup_map ψ,
    Subgroup.characteristic_iff_map_eq.mpr fun ψ => Helpers.order_thompson_center_map ψ⟩

theorem centerThompsonOrder_contains_center (S : Type*) [Group S] [Finite S] :
    Subgroup.center S ≤ centerThompsonOrder S ∧
      ∀ p : ℕ, p.Prime → IsPGroup p S → Nontrivial S → centerThompsonOrder S ≠ ⊥ :=
  ⟨Helpers.center_le_order_thompson_center, fun p hp hS _ =>
    Helpers.order_thompson_center_pgroup_nontrivial p hp hS⟩

theorem embeddedThompsonCenter_le {G : Type*} [Group G] (U : Subgroup G) :
    embeddedThompsonCenter U ≤ U :=
  Subgroup.map_subtype_le _

theorem map_embeddedThompsonCenter {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (U : Subgroup G) (f : G →* H) (hker : f.ker ⊓ U = ⊥) :
    (embeddedThompsonCenter U).map f = embeddedThompsonCenter (U.map f) :=
  map_maxCardZJ_map_subtype_of_injective f U <| (injective_iff_map_eq_one _).mpr fun x hx =>
    Subtype.ext (by simpa [hker] using (show (x : G) ∈ f.ker ⊓ U from ⟨hx, x.2⟩))

section Action

variable {G P : Type*} [Group G] [Group P]

@[expose]
def actionPrimeCore (p : ℕ) (ρ : G →* MulAut P) : Subgroup G :=
  (pCore p (G ⧸ ρ.ker)).comap (QuotientGroup.mk' ρ.ker)

@[expose]
def zjActionCommutator (ρ : G →* MulAut P) (u : P) (x : G) : P :=
  u⁻¹ * ρ x⁻¹ u

@[expose]
def IsPStableAction (p : ℕ) (ρ : G →* MulAut P) : Prop :=
  ∀ x : G, (∀ u : P, zjActionCommutator ρ (zjActionCommutator ρ u x) x = 1) →
    x ∈ actionPrimeCore p ρ

end Action

@[expose]
def StableNormalPSubgroupActions (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (U : Subgroup G) (hU : U.Normal), IsPGroup p U →
    letI : U.Normal := hU
    IsPStableAction p (MulAut.conjNormal : G →* MulAut U)

@[expose]
def subgroupProduct {G : Type*} [Group G] (U V : Subgroup G) : Set G :=
  {g | ∃ u ∈ U, ∃ v ∈ V, u * v = g}

section Glauberman

variable {G : Type*} [Group G]

private theorem actionPrimeCore_eq_quotientActionPrimeCore [Finite G] {P : Type*} [Group P]
    {p : ℕ} (hp : p.Prime) (ρ : G →* MulAut P) :
    actionPrimeCore p ρ = Helpers.quotientActionPrimeCore p ρ.ker := by
  rw [actionPrimeCore, pCore_eq_helpersPrimeSetCore hp, Helpers.quotientActionPrimeCore]

private theorem conjNormal_ker_eq_centralizer (U : Subgroup G) [U.Normal] :
    (MulAut.conjNormal : G →* MulAut U).ker = Subgroup.centralizer (U : Set G) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have he : x * u * x⁻¹ = u := congrArg Subtype.val (MulEquiv.congr_fun h ⟨u, hu⟩)
    calc u * x = x * u * x⁻¹ * x := by rw [he]
      _ = x * u := by group
  · intro h
    ext u
    change x * u.val * x⁻¹ = u.val
    rw [← h u.val u.property]
    group

private theorem actionPrimeCore_conjNormal [Finite G] {p : ℕ} (hp : p.Prime) (U : Subgroup G)
    [U.Normal] :
    actionPrimeCore p (MulAut.conjNormal : G →* MulAut U) =
      Helpers.conjugationActionPrimeCore p U := by
  simp only [actionPrimeCore_eq_quotientActionPrimeCore hp, Helpers.conjugationActionPrimeCore,
    conjNormal_ker_eq_centralizer]

private theorem zjActionCommutator_conjNormal (U : Subgroup G) [U.Normal] (u : U) (x : G) :
    (zjActionCommutator (MulAut.conjNormal : G →* MulAut U) u x).val =
      Helpers.conjugationDifference x⁻¹ u.val := by
  simp only [zjActionCommutator, Helpers.conjugationDifference, inv_inv, Subgroup.coe_mul,
    Subgroup.coe_inv, MulAut.conjNormal_apply]
  group

private theorem stableNormalPSubgroupActions_iff [Finite G] {p : ℕ} (hp : p.Prime) :
    StableNormalPSubgroupActions p G ↔ Helpers.normalPSubgroupActionsStable p G := by
  constructor
  · intro h U hU hUp x hx
    have hi := h U hU hUp x⁻¹ fun u => Subtype.ext <| by
      simpa only [zjActionCommutator_conjNormal, inv_inv, Subgroup.coe_one] using hx u
    rw [actionPrimeCore_conjNormal hp] at hi
    exact (Subgroup.inv_mem_iff _).mp hi
  · intro h U hU hUp x hx
    have hi := h U hU hUp x⁻¹ fun u => by
      simpa only [zjActionCommutator_conjNormal, Subgroup.coe_one] using
        congrArg Subtype.val (hx u)
    rw [actionPrimeCore_conjNormal hp]
    exact (Subgroup.inv_mem_iff _).mp hi

private theorem isCharacteristicP_iff [Finite G] {p : ℕ} (hp : p.Prime) :
    IsCharacteristicP p G ↔
      Subgroup.centralizer (Helpers.primeSetCore (GroupType := G) {p} : Set G) ≤
        Helpers.primeSetCore {p} := by
  rw [IsCharacteristicP, pCore_eq_helpersPrimeSetCore hp]

theorem embeddedThompsonCenter_characteristic (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (G : Type*) [Group G] [Finite G]
    (hchar : IsCharacteristicP p G)
    (S : Sylow p G) (hstable : StableNormalPSubgroupActions p G) :
    (embeddedThompsonCenter (S : Subgroup G)).Characteristic :=
  Helpers.axiomatic_zj_characteristic (GroupType := G) p Fact.out hpodd
    ((stableNormalPSubgroupActions_iff Fact.out).mp hstable)
    ((isCharacteristicP_iff Fact.out).mp hchar) S

end Glauberman

end CFSG
