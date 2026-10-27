module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {L Q : Subgroup G} {H : Type} [Group H]

theorem exists_modOrthL2_conjRep (hQ : IsElemAbelian 2 Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (α : ↥L →* H) (hα : Function.Surjective α)
    (hker : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ Q) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) H W) (cls : ↥Q →* Multiplicative W),
      Function.Bijective cls ∧
        ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
          ρ (α ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v) := by
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let c : ↥L →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hLQ)
  have hc : ∀ (ℓ : ↥L) (u : ↥Q), ((c ℓ u : ↥Q) : G) = ℓ * u * (ℓ : G)⁻¹ := fun _ _ => rfl
  have hkerc : α.ker ≤ c.ker := by
    intro ℓ hℓ
    have hℓQ : (ℓ : G) ∈ Q := hker ℓ hℓ
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun u => Subtype.ext ?_
    change ((c ℓ u : ↥Q) : G) = u
    rw [hc, hcommQ _ hℓQ _ u.2, mul_inv_cancel_right]
  let c' : H →* MulAut ↥Q := α.liftOfSurjective hα ⟨c, hkerc⟩
  have hc' : ∀ ℓ : ↥L, c' (α ℓ) = c ℓ := fun ℓ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ ℓ
  letI : CommGroup ↥Q :=
    { (inferInstance : Group ↥Q) with
      mul_comm := fun a b => Subtype.ext (hcommQ _ a.2 _ b.2) }
  have h2 : ∀ x : Additive ↥Q, 2 • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hQ.2 _ (Additive.toMul x).2)
  letI : Module (ZMod 2) (Additive ↥Q) := AddCommGroup.zmodModule h2
  let lin : MulAut ↥Q →* Module.End (ZMod 2) (Additive ↥Q) :=
    { toFun := fun φ => (MulEquiv.toAdditive φ).toAddMonoidHom.toZModLinearMap 2
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let cls : ↥Q →* Multiplicative (Additive ↥Q) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul u)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Additive ↥Q, inferInstance, inferInstance, lin.comp c', cls,
    ⟨fun a b hab => Additive.ofMul.injective (Multiplicative.ofAdd.injective hab),
      fun y => ⟨Additive.toMul (Multiplicative.toAdd y), rfl⟩⟩, ?_⟩
  intro ℓ u v huv
  change Additive.ofMul (c' (α ℓ) u) = Additive.ofMul v
  rw [hc']
  exact congrArg Additive.ofMul (Subtype.ext (by rw [hc]; exact huv.symm))

section Module

variable {α : ↥L →* H} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {cls : ↥Q →* Multiplicative W}

theorem modOrthL2_isIrreducible [Nontrivial W] (hcls : Function.Surjective cls)
    (hact : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      ρ (α ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ Q → L ≤ Subgroup.normalizer (N : Set G) → N = ⊥ ∨ N = Q) :
    ρ.IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  let N : Subgroup G := ((AddSubgroup.toSubgroup U.toAddSubgroup).comap cls).map Q.subtype
  have hmem : ∀ u : ↥Q, (u : G) ∈ N ↔ Multiplicative.toAdd (cls u) ∈ U := fun u =>
    (Subgroup.mem_map_iff_mem Q.subtype_injective).trans Iff.rfl
  have hconj : ∀ ℓ ∈ L, ∀ x ∈ N, ℓ * x * ℓ⁻¹ ∈ N := by
    intro ℓ hℓ x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    let v : ↥Q := ⟨ℓ * u * ℓ⁻¹, (Subgroup.mem_normalizer_iff.mp (hLQ hℓ) u).mp u.2⟩
    have hv : Multiplicative.toAdd (cls v) ∈ U := by
      rw [← hact ⟨ℓ, hℓ⟩ u v rfl]
      exact hU _ _ hu
    exact (hmem v).mpr hv
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj ℓ hℓ x, fun hx => ?_⟩
    have h1 := hconj ℓ⁻¹ (L.inv_mem hℓ) _ hx
    have h2 : ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  rcases hirr N (Subgroup.map_subtype_le _) hLN with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨u, hu⟩ := hcls (Multiplicative.ofAdd w)
    have huN : (u : G) ∈ N := (hmem u).mpr (by rw [hu]; exact hw)
    rw [h, Subgroup.mem_bot] at huN
    have hu1 : u = 1 := Subtype.ext huN
    rw [hu1, map_one] at hu
    rw [Submodule.mem_bot]
    exact (congrArg Multiplicative.toAdd hu).symm
  · right
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, hu⟩ := hcls (Multiplicative.ofAdd w)
    have huN : (u : G) ∈ N := by
      rw [h]
      exact u.2
    have hw := (hmem u).mp huN
    rwa [hu] at hw

theorem modOrthL2_exists_ne_one (hcls : Function.Injective cls)
    (hact : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      ρ (α ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (Q : Set G)) : ∃ g, ρ g ≠ 1 := by
  obtain ⟨ℓ, hℓ, hℓQ⟩ := SetLike.not_le_iff_exists.mp hnt
  rw [Subgroup.mem_centralizer_iff] at hℓQ
  push Not at hℓQ
  obtain ⟨q, hq, hne⟩ := hℓQ
  refine ⟨α ⟨ℓ, hℓ⟩, fun h1 => hne ?_⟩
  let v : ↥Q := ⟨ℓ * q * ℓ⁻¹, (Subgroup.mem_normalizer_iff.mp (hLQ hℓ) q).mp hq⟩
  have h2 := hact ⟨ℓ, hℓ⟩ ⟨q, hq⟩ v rfl
  rw [h1, Module.End.one_apply] at h2
  have h3 : q = ℓ * q * ℓ⁻¹ := congrArg Subtype.val (hcls (Multiplicative.toAdd.injective h2))
  calc q * ℓ = ℓ * q * ℓ⁻¹ * ℓ := by rw [← h3]
    _ = ℓ * q := inv_mul_cancel_right _ _

theorem modOrthL2_toAdd_cls_commutator
    (hact : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      ρ (α ℓ) (Multiplicative.toAdd (cls u)) = Multiplicative.toAdd (cls v))
    {ℓ u : G} (hℓ : ℓ ∈ L) (hu : u ∈ Q) (h : ⁅ℓ, u⁆ ∈ Q) :
    Multiplicative.toAdd (cls ⟨⁅ℓ, u⁆, h⟩) =
      ρ (α ⟨ℓ, hℓ⟩) (Multiplicative.toAdd (cls ⟨u, hu⟩)) - Multiplicative.toAdd (cls ⟨u, hu⟩) := by
  let v : ↥Q := ⟨⁅ℓ, u⁆ * u, Q.mul_mem h hu⟩
  have hv : (v : G) = ℓ * u * ℓ⁻¹ := by
    change ⁅ℓ, u⁆ * u = ℓ * u * ℓ⁻¹
    rw [commutatorElement_def, inv_mul_cancel_right]
  have he : (⟨⁅ℓ, u⁆, h⟩ : ↥Q) = v * (⟨u, hu⟩ : ↥Q)⁻¹ := Subtype.ext (by
    change ⁅ℓ, u⁆ = ⁅ℓ, u⁆ * u * u⁻¹
    rw [mul_inv_cancel_right])
  rw [he, map_mul, map_inv, toAdd_mul, toAdd_inv, ← hact ⟨ℓ, hℓ⟩ ⟨u, hu⟩ v hv, sub_eq_add_neg]

end Module

end CFSG.Quasithin.F112R.St84

end
