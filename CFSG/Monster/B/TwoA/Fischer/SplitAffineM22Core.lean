module

public import CFSG.Monster.B.TwoA.Fischer.SplitAffine
public import CFSG.RankThree.FFModules.RepMulAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Rep

variable {M W : Type*} [Group M] [AddCommGroup W] [Module (ZMod 2) W]

abbrev repMulAut (ρ : Representation (ZMod 2) M W) : M →* MulAut (Multiplicative W) :=
  CFSG.RankThree.FFModules.repMulAut ρ

theorem repMulAut_apply (ρ : Representation (ZMod 2) M W) (g : M) (w : Multiplicative W) :
    repMulAut ρ g w = Multiplicative.ofAdd (ρ g (Multiplicative.toAdd w)) := rfl

end Rep

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem clique_split_affine_core {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {M W : Type*} [Group M]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) M W)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃* M)
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W)
    (hφ : ∀ (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
      (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = ρ (θ f) (φ (Additive.ofMul r)))
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) :
    (∃ e : ↥(setStab act lab Y C ⊓ actStab act x) ≃* M,
      ∀ k, e k = θ (Subgroup.inclusion inf_le_left k)) ∧
    ∃ (Ψ : ↥(setStab act lab Y C) ≃* Multiplicative W ⋊[repMulAut ρ] M)
      (c : ↥(hexadFiber lab Y C ∅) ≃ W),
      (∀ (r : Subgroup.closure (lab '' C)) (k : S)
        (hk : k ∈ setStab act lab Y C ⊓ actStab act x) (h : (r : S) * k ∈ setStab act lab Y C),
        Ψ ⟨(r : S) * k, h⟩ = ⟨Multiplicative.ofAdd (φ (Additive.ofMul r)),
          θ (QuotientGroup.mk (⟨k, hk.1⟩ : setStab act lab Y C))⟩) ∧
      (∀ (r : Subgroup.closure (lab '' C)) (h : act (r : S) x ∈ hexadFiber lab Y C ∅),
        c ⟨act (r : S) x, h⟩ = φ (Additive.ofMul r)) ∧
      ∀ (f : setStab act lab Y C) (y : ↥(hexadFiber lab Y C ∅))
        (h : act (f : S) y ∈ hexadFiber lab Y C ∅),
        c ⟨act (f : S) y, h⟩ = Multiplicative.toAdd (Ψ f).left + ρ (Ψ f).right (c y) := by
  have hcl : ptStab act lab Y C = Subgroup.closure (lab '' C) :=
    hS.ptStab_eq_closure_of_isSliceMaxClique hC
  have hmem : ∀ {s : S}, s ∈ ptStab act lab Y C → s ∈ Subgroup.closure (lab '' C) :=
    fun h => hcl ▸ h
  have hmem' : ∀ {s : S}, s ∈ Subgroup.closure (lab '' C) → s ∈ ptStab act lab Y C :=
    fun h => hcl ▸ h
  obtain ⟨-, -, hreg⟩ := hS.clique_split_regular hC
  obtain ⟨hcompl, hbij, haff⟩ := hreg x hx
  obtain ⟨eK, heK⟩ : ∃ eK : ↥(setStab act lab Y C ⊓ actStab act x) ≃*
      setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C),
      ∀ k, eK k = QuotientGroup.mk (Subgroup.inclusion inf_le_left k) :=
    ⟨MulEquiv.ofBijective _ hbij, fun _ => rfl⟩
  refine ⟨⟨eK.trans θ, fun k => by rw [MulEquiv.trans_apply, heK]⟩, ?_⟩
  have hmemR : ∀ n : ↥((ptStab act lab Y C).subgroupOf (setStab act lab Y C)),
      ((n : setStab act lab Y C) : S) ∈ Subgroup.closure (lab '' C) :=
    fun n => hmem ((Subgroup.mem_subgroupOf).1 n.2)
  obtain ⟨fn, hfn⟩ : ∃ fn : ↥((ptStab act lab Y C).subgroupOf (setStab act lab Y C)) ≃*
      Multiplicative W, ∀ n : ↥((ptStab act lab Y C).subgroupOf (setStab act lab Y C)),
      fn n = Multiplicative.ofAdd (φ (Additive.ofMul ⟨_, hmemR n⟩)) :=
    ⟨((Subgroup.subgroupOfEquivOfLe (ptStab_le_setStab C)).trans
      (MulEquiv.subgroupCongr hcl)).trans (MulEquiv.toAdditiveLeft.symm φ.toAddEquiv),
      fun _ => rfl⟩
  obtain ⟨fg, hfg⟩ : ∃ fg : ↥((setStab act lab Y C ⊓ actStab act x).subgroupOf
      (setStab act lab Y C)) ≃* M, ∀ k : ↥((setStab act lab Y C ⊓ actStab act x).subgroupOf
      (setStab act lab Y C)), fg k = θ (QuotientGroup.mk (k : setStab act lab Y C)) :=
    ⟨((Subgroup.subgroupOfEquivOfLe inf_le_left).trans eK).trans θ, fun k => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, heK]
      rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(setStab act lab Y C) ≃* Multiplicative W ⋊[repMulAut ρ] M,
      ∀ (n : ↥((ptStab act lab Y C).subgroupOf (setStab act lab Y C)))
        (k : ↥((setStab act lab Y C ⊓ actStab act x).subgroupOf (setStab act lab Y C))),
        Ψ ((n : setStab act lab Y C) * k) = ⟨fn n, fg k⟩ := by
    refine ⟨(SemidirectProduct.mulEquivSubgroup hcompl).symm.trans
      (SemidirectProduct.congr fn fg fun g => MulEquiv.ext fun n => ?_), fun n k => ?_⟩
    · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hfn, hfn, repMulAut_apply, hfg,
        toAdd_ofAdd]
      exact congrArg Multiplicative.ofAdd (hφ (g : setStab act lab Y C)
        ⟨((n : setStab act lab Y C) : S), hmemR n⟩ _)
    · rw [MulEquiv.trans_apply]
      have e : (SemidirectProduct.mulEquivSubgroup hcompl).symm
          ((n : setStab act lab Y C) * k) = ⟨n, k⟩ := by
        rw [MulEquiv.symm_apply_eq, SemidirectProduct.mulEquivSubgroup_apply]
      rw [e]
      rfl
  obtain ⟨c, hc⟩ : ∃ c : ↥(hexadFiber lab Y C ∅) ≃ W,
      ∀ (r : Subgroup.closure (lab '' C)) (h : act (r : S) x ∈ hexadFiber lab Y C ∅),
        c ⟨act (r : S) x, h⟩ = φ (Additive.ofMul r) := by
    let o : Subgroup.closure (lab '' C) → ↥(hexadFiber lab Y C ∅) := fun r =>
      ⟨act (r : S) x, hS.act_mem_hexadFiber (hmem' r.2) hx⟩
    have ho : Function.Bijective o := by
      refine ⟨fun r s h => ?_, fun y => ?_⟩
      · have h1 : act ((s : S)⁻¹ * r) x = x := by
          rw [map_mul, Equiv.Perm.mul_apply]
          have h2 : act (r : S) x = act (s : S) x := congrArg Subtype.val h
          rw [h2, act_inv_act]
        have h3 := hS.eq_one_of_act_eq hC hx
          ((ptStab act lab Y C).mul_mem ((ptStab act lab Y C).inv_mem (hmem' s.2)) (hmem' r.2)) h1
        rw [inv_mul_eq_one] at h3
        exact (Subtype.ext h3).symm
      · obtain ⟨r, ⟨hr, hry⟩, -⟩ := hS.existsUnique_act_eq hC hx y.2
        exact ⟨⟨r, hmem hr⟩, Subtype.ext hry⟩
    refine ⟨(Equiv.ofBijective o ho).symm.trans (Additive.ofMul.trans φ.toEquiv), fun r h => ?_⟩
    have e : (⟨act (r : S) x, h⟩ : ↥(hexadFiber lab Y C ∅)) = Equiv.ofBijective o ho r := rfl
    rw [e, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  refine ⟨Ψ, c, fun r k hk h => ?_, hc, fun f y h => ?_⟩
  · have hrF : (r : S) ∈ setStab act lab Y C := ptStab_le_setStab C (hmem' r.2)
    have e : (⟨(r : S) * k, h⟩ : setStab act lab Y C) =
        ((⟨⟨r, hrF⟩, (Subgroup.mem_subgroupOf).2 (hmem' r.2)⟩ :
          ↥((ptStab act lab Y C).subgroupOf (setStab act lab Y C))) : setStab act lab Y C) *
        ((⟨⟨k, hk.1⟩, (Subgroup.mem_subgroupOf).2 hk⟩ :
          ↥((setStab act lab Y C ⊓ actStab act x).subgroupOf (setStab act lab Y C))) :
            setStab act lab Y C) := rfl
    rw [e, hΨ, hfn, hfg]
  · obtain ⟨y, hy⟩ := y
    obtain ⟨a, ⟨ha, rfl⟩, -⟩ := hS.existsUnique_act_eq hC hx hy
    obtain ⟨p, hp⟩ : ∃ p, SemidirectProduct.mulEquivSubgroup hcompl p = f :=
      ⟨_, MulEquiv.apply_symm_apply _ f⟩
    have hf : f = (p.left : setStab act lab Y C) * p.right := by
      rw [← hp, SemidirectProduct.mulEquivSubgroup_apply]
    have hr : ((p.left : setStab act lab Y C) : S) ∈ ptStab act lab Y C :=
      (Subgroup.mem_subgroupOf).1 p.left.2
    have hk : ((p.right : setStab act lab Y C) : S) ∈ setStab act lab Y C ⊓ actStab act x :=
      (Subgroup.mem_subgroupOf).1 p.right.2
    obtain ⟨hka, hact⟩ := haff _ hr _ hk _ ha
    have hΨf : Ψ f = ⟨fn p.left, fg p.right⟩ := by
      rw [hf]
      exact hΨ p.left p.right
    have hfS : (f : S) = ((p.left : setStab act lab Y C) : S) *
        ((p.right : setStab act lab Y C) : S) := by
      rw [hf]
      rfl
    set r' : Subgroup.closure (lab '' C) := ⟨_, hmem hr⟩ with hr'
    set s' : Subgroup.closure (lab '' C) := ⟨_, hmem hka⟩ with hs'
    have hrs : ((r' * s' : Subgroup.closure (lab '' C)) : S) =
        ((p.left : setStab act lab Y C) : S) * (((p.right : setStab act lab Y C) : S) * a *
          ((p.right : setStab act lab Y C) : S)⁻¹) :=
      rfl
    have hmem2 : act ((r' * s' : Subgroup.closure (lab '' C)) : S) x ∈
        hexadFiber lab Y C ∅ := by
      rw [hrs, ← hact, ← hfS]
      exact h
    have e1 : (⟨act (f : S) (act a x), h⟩ : ↥(hexadFiber lab Y C ∅)) =
        ⟨act ((r' * s' : Subgroup.closure (lab '' C)) : S) x, hmem2⟩ := by
      apply Subtype.ext
      change act (f : S) (act a x) = act ((r' * s' : Subgroup.closure (lab '' C)) : S) x
      rw [hrs, hfS, hact]
    have e2 := hφ (p.right : setStab act lab Y C) ⟨a, hmem ha⟩ (hmem hka)
    have e3 : c ⟨act a x, hy⟩ = φ (Additive.ofMul ⟨a, hmem ha⟩) := hc ⟨a, hmem ha⟩ hy
    rw [e1, hc, hΨf]
    change φ (Additive.ofMul (r' * s')) =
      Multiplicative.toAdd (fn p.left) + ρ (fg p.right) (c ⟨act a x, hy⟩)
    rw [hfn, hfg, toAdd_ofAdd, ofMul_mul, map_add, e3]
    exact congrArg (φ (Additive.ofMul r') + ·) e2

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
