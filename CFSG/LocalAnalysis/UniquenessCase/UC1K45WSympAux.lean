module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {X N : Subgroup G} [X.Normal] [N.Normal]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
variable {B : LinearMap.BilinForm (ZMod 2) W}
variable {π : ↥X →* Multiplicative W}

theorem conjNormal_mem_center (g : G) {x : ↥X} (hx : x ∈ Subgroup.center ↥X) :
    MulAut.conjNormal g x ∈ Subgroup.center ↥X :=
  (Subgroup.characteristic_iff_map_le.1 Subgroup.centerCharacteristic (MulAut.conjNormal g))
    ⟨x, hx, rfl⟩

theorem center_mem_of_conjNormal_mem_center (g : G) {x : ↥X}
    (hx : MulAut.conjNormal g x ∈ Subgroup.center ↥X) : x ∈ Subgroup.center ↥X := by
  have h : MulAut.conjNormal g⁻¹ (MulAut.conjNormal g x) = x := by
    simp only [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  rw [← h]
  exact conjNormal_mem_center g⁻¹ hx

theorem subgroupOf_map_center :
    ((Subgroup.center ↥X).map X.subtype).subgroupOf X = Subgroup.center ↥X := by
  have h := Subgroup.comap_map_eq (f := X.subtype) (H := Subgroup.center ↥X)
  rw [Subgroup.comap_subtype] at h
  rw [Subgroup.ker_subtype, sup_bot_eq] at h
  exact h

theorem ker_le_conjNormal_ker (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    π.ker ≤ (π.comp (MulAut.conjNormal g).toMonoidHom).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hx' : x ∈ Subgroup.center ↥X := hπker ▸ hx
  have : π (MulAut.conjNormal g x) = 1 := by
    rw [← MonoidHom.mem_ker, hπker]
    exact conjNormal_mem_center g hx'
  simpa using this

@[expose] noncomputable def conjLift (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    ↥X ⧸ π.ker →* Multiplicative W :=
  QuotientGroup.lift π.ker (π.comp (MulAut.conjNormal g).toMonoidHom)
    (ker_le_conjNormal_ker hπker g)

@[expose] noncomputable def conjLin (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) : W →ₗ[ZMod 2] W :=
  ((AddMonoidHom.toMultiplicative (α := W) (β := W)).symm
    ((conjLift hπker g).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).symm.toMonoidHom)).toZModLinearMap 2

theorem conjLin_apply (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (x : ↥X) :
    conjLin hπsurj hπker g (Multiplicative.toAdd (π x)) =
      Multiplicative.toAdd (π (MulAut.conjNormal g x)) := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective π hπsurj)
      (QuotientGroup.mk x) = π x :=
    QuotientGroup.kerLift_mk (φ := π) x
  rw [conjLin, AddMonoidHom.coe_toZModLinearMap]
  change ((conjLift hπker g)
      ((QuotientGroup.quotientKerEquivOfSurjective π hπsurj).symm
        (Multiplicative.ofAdd (Multiplicative.toAdd (π x))))).toAdd = _
  rw [ofAdd_toAdd]
  rw [show (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).symm (π x) =
      QuotientGroup.mk x from (MulEquiv.symm_apply_eq _).mpr he]
  simp only [conjLift, QuotientGroup.lift_mk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

theorem conjLin_injective (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    Function.Injective (conjLin hπsurj hπker g) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker] at hw
  obtain ⟨x, hx⟩ := hπsurj (Multiplicative.ofAdd w)
  have hxw : Multiplicative.toAdd (π x) = w := by
    rw [hx, toAdd_ofAdd]
  rw [← hxw, conjLin_apply] at hw
  have h1 : π (MulAut.conjNormal g x) = 1 := by
    have := congrArg Multiplicative.ofAdd hw
    simpa using this
  have h2 : MulAut.conjNormal g x ∈ Subgroup.center ↥X := by
    rw [← MonoidHom.mem_ker, hπker] at h1
    exact h1
  have h3 : x ∈ Subgroup.center ↥X := center_mem_of_conjNormal_mem_center g h2
  have h4 : π x = 1 := by
    rw [← MonoidHom.mem_ker, hπker]
    exact h3
  rw [← hxw, h4]
  simp

theorem conjLin_bijective (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    Function.Bijective (conjLin hπsurj hπker g) :=
  ⟨conjLin_injective hπsurj hπker g,
    (LinearMap.injective_iff_surjective).mp (conjLin_injective hπsurj hπker g)⟩

@[expose] noncomputable def conjEquiv (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (conjLin hπsurj hπker g) (conjLin_bijective hπsurj hπker g)

theorem conjEquiv_apply (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (x : ↥X) :
    conjEquiv hπsurj hπker g (Multiplicative.toAdd (π x)) =
      Multiplicative.toAdd (π (MulAut.conjNormal g x)) := by
  rw [conjEquiv, LinearEquiv.ofBijective_apply, conjLin_apply]

theorem conjEquiv_mul (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g h : G) :
    conjEquiv hπsurj hπker (g * h) =
      conjEquiv hπsurj hπker g * conjEquiv hπsurj hπker h := by
  apply LinearEquiv.ext
  intro w
  obtain ⟨x, hx⟩ := hπsurj (Multiplicative.ofAdd w)
  have hxw : Multiplicative.toAdd (π x) = w := by rw [hx, toAdd_ofAdd]
  rw [← hxw]
  simp only [conjEquiv_apply, LinearEquiv.mul_apply]
  congr 1
  rw [map_mul, MulAut.mul_apply]

theorem conjEquiv_one (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) :
    conjEquiv hπsurj hπker 1 = 1 := by
  apply LinearEquiv.ext
  intro w
  obtain ⟨x, hx⟩ := hπsurj (Multiplicative.ofAdd w)
  have hxw : Multiplicative.toAdd (π x) = w := by rw [hx, toAdd_ofAdd]
  rw [← hxw, conjEquiv_apply, map_one, MulAut.one_apply]
  rfl

@[expose] noncomputable def conjHom (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) : G →* (W ≃ₗ[ZMod 2] W) where
  toFun := conjEquiv hπsurj hπker
  map_one' := conjEquiv_one hπsurj hπker
  map_mul' := conjEquiv_mul hπsurj hπker

@[expose] noncomputable def commConj (g : G) (x : ↥X) : ↥X :=
  MulAut.conjNormal g x * x⁻¹

@[expose] noncomputable def commSelf (g : G) (x : ↥X) : ↥X :=
  x * (MulAut.conjNormal g x)⁻¹

theorem coe_commConj (g : G) (x : ↥X) : (commConj g x : G) = ⁅g, (x : G)⁆ := by
  change (MulAut.conjNormal g x : G) * (x : G)⁻¹ = ⁅g, (x : G)⁆
  rw [MulAut.conjNormal_apply, commutatorElement_def]

theorem coe_commSelf (g : G) (x : ↥X) : (commSelf g x : G) = ⁅(x : G), g⁆ := by
  change (x : G) * (MulAut.conjNormal g x : G)⁻¹ = ⁅(x : G), g⁆
  rw [MulAut.conjNormal_apply, commutatorElement_def]
  group

theorem toAdd_pi_commConj (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (x : ↥X) :
    Multiplicative.toAdd (π (commConj g x)) =
      conjLin hπsurj hπker g (Multiplicative.toAdd (π x)) - Multiplicative.toAdd (π x) := by
  rw [commConj, map_mul, map_inv, toAdd_mul, toAdd_inv,
    conjLin_apply]
  abel

theorem conjEquiv_zpow (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (k : ℤ) :
    conjEquiv hπsurj hπker (g ^ k) = conjEquiv hπsurj hπker g ^ k :=
  map_zpow (conjHom hπsurj hπker) g k

theorem toAdd_pi_commSelf_zpow (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (k : ℤ) (x : ↥X) :
    Multiplicative.toAdd (π (commSelf (g ^ k) x)) =
      Multiplicative.toAdd (π x) -
        (conjEquiv hπsurj hπker g ^ k) (Multiplicative.toAdd (π x)) := by
  have h := conjEquiv_apply hπsurj hπker (g ^ k) x
  rw [conjEquiv_zpow] at h
  rw [commSelf, map_mul, map_inv, toAdd_mul, toAdd_inv, ← h]
  abel

theorem coe_pow_toLinearMap (u : W ≃ₗ[ZMod 2] W) (n : ℕ) :
    ((u ^ n : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) =
      (u : W →ₗ[ZMod 2] W) ^ n := by
  induction n with
  | zero => rw [pow_zero, LinearEquiv.coe_toLinearMap_one, pow_zero]; rfl
  | succ n ih => rw [pow_succ, LinearEquiv.coe_toLinearMap_mul, ih, pow_succ]

theorem range_pow_sub_le (x : W →ₗ[ZMod 2] W) (n : ℕ) :
    LinearMap.range (x ^ n - 1) ≤ LinearMap.range (x - 1) := by
  cases n with
  | zero => rw [pow_zero, sub_self, LinearMap.range_zero]; exact bot_le
  | succ n =>
    have hgeom : (x - 1) * (∑ i ∈ Finset.range (n + 1), x ^ i) = x ^ (n + 1) - 1 :=
      mul_geom_sum x (n + 1)
    rw [← hgeom]
    exact LinearMap.range_comp_le_range (∑ i ∈ Finset.range (n + 1), x ^ i) (x - 1)

theorem range_inv_sub_eq {f g : W →ₗ[ZMod 2] W} (hfg : f * g = 1) (hgf : g * f = 1) :
    LinearMap.range (g - 1) = LinearMap.range (f - 1) := by
  apply le_antisymm
  · rw [show g - 1 = (1 - f) * g by rw [sub_mul, one_mul, hfg]]
    calc LinearMap.range ((1 - f) * g) ≤ LinearMap.range (1 - f) :=
          LinearMap.range_comp_le_range g (1 - f)
      _ = LinearMap.range (f - 1) := by
          rw [show (1 : W →ₗ[ZMod 2] W) - f = -(f - 1) by abel,
            LinearMap.range_neg]
  · rw [show f - 1 = (1 - g) * f by rw [sub_mul, one_mul, hgf]]
    calc LinearMap.range ((1 - g) * f) ≤ LinearMap.range (1 - g) :=
          LinearMap.range_comp_le_range f (1 - g)
      _ = LinearMap.range (g - 1) := by
          rw [show (1 : W →ₗ[ZMod 2] W) - g = -(g - 1) by abel,
            LinearMap.range_neg]

theorem range_zpow_sub_le (u : W ≃ₗ[ZMod 2] W) (k : ℤ) :
    LinearMap.range (((u ^ k : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) - 1) ≤
      LinearMap.range ((u : W →ₗ[ZMod 2] W) - 1) := by
  rcases Int.eq_nat_or_neg k with ⟨n, hn⟩
  rcases hn with rfl | rfl
  · rw [zpow_natCast, coe_pow_toLinearMap]
    exact range_pow_sub_le (u : W →ₗ[ZMod 2] W) n
  · rw [zpow_neg, zpow_natCast]
    have hcoe : ((u ^ n)⁻¹ : W ≃ₗ[ZMod 2] W) = (u⁻¹) ^ n := (inv_pow u n).symm
    rw [hcoe, coe_pow_toLinearMap]
    have hfg : (u : W →ₗ[ZMod 2] W) * ((u⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = 1 := by
      rw [← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel, LinearEquiv.coe_toLinearMap_one]
      rfl
    have hgf : ((u⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) * (u : W →ₗ[ZMod 2] W) = 1 := by
      rw [← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one]
      rfl
    exact (range_pow_sub_le ((u⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) n).trans
      (le_of_eq (range_inv_sub_eq hfg hgf))

@[expose] noncomputable def rangeSubgroup (a : W ≃ₗ[ZMod 2] W) : Subgroup (Multiplicative W) where
  carrier := {w | Multiplicative.toAdd w ∈
    LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id)}
  one_mem' := by
    rw [Set.mem_setOf_eq, toAdd_one]
    exact ⟨0, by simp⟩
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, toAdd_mul] at hu hv ⊢
    exact add_mem hu hv
  inv_mem' := by
    intro u hu
    simp only [Set.mem_setOf_eq, toAdd_inv] at hu ⊢
    exact neg_mem hu

theorem mem_rangeSubgroup (a : W ≃ₗ[ZMod 2] W) (w : Multiplicative W) :
    w ∈ rangeSubgroup a ↔
      Multiplicative.toAdd w ∈ LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id) :=
  Iff.rfl

theorem card_rangeSubgroup (a : W ≃ₗ[ZMod 2] W) :
    Nat.card ↥(rangeSubgroup a) =
      Nat.card ↥(LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id)) :=
  Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd w.1, w.2⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem ker_le_comap_rangeSubgroup (hπker : π.ker = Subgroup.center ↥X)
    (a : W ≃ₗ[ZMod 2] W) : π.ker ≤ (rangeSubgroup a).comap π := by
  intro x hx
  rw [Subgroup.mem_comap, mem_rangeSubgroup]
  rw [MonoidHom.mem_ker] at hx
  simp [hx]

theorem conjEquiv_apply_eq_self_of_mem_N (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X)
    (hN : ∀ g : G, g ∈ N ↔ ∀ x ∈ X, ⁅g, x⁆ ∈ (Subgroup.center ↥X).map X.subtype)
    {g : G} (hg : g ∈ N) (x : ↥X) :
    conjEquiv hπsurj hπker g (Multiplicative.toAdd (π x)) = Multiplicative.toAdd (π x) := by
  rw [conjEquiv_apply]
  have hzx : ⁅g, (x : G)⁆ ∈ (Subgroup.center ↥X).map X.subtype := (hN g).mp hg x x.2
  have hmem : commConj g x ∈ Subgroup.center ↥X := by
    rw [← subgroupOf_map_center, Subgroup.mem_subgroupOf]
    rwa [coe_commConj]
  have hker : π (commConj g x) = 1 := by
    rw [← MonoidHom.mem_ker, hπker]
    exact hmem
  have h2 : π (MulAut.conjNormal g x) = π x := by
    have h := hker
    rw [commConj, map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  rw [h2]

theorem N_le_conjHom_ker (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X)
    (hN : ∀ g : G, g ∈ N ↔ ∀ x ∈ X, ⁅g, x⁆ ∈ (Subgroup.center ↥X).map X.subtype) :
    N ≤ (conjHom hπsurj hπker).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.ext
  intro w
  obtain ⟨x, hx⟩ := hπsurj (Multiplicative.ofAdd w)
  have hxw : Multiplicative.toAdd (π x) = w := by rw [hx, toAdd_ofAdd]
  rw [← hxw]
  exact conjEquiv_apply_eq_self_of_mem_N hπsurj hπker hN hg x

theorem conjHom_ker_eq (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X)
    (hN : ∀ g : G, g ∈ N ↔ ∀ x ∈ X, ⁅g, x⁆ ∈ (Subgroup.center ↥X).map X.subtype) :
    (conjHom hπsurj hπker).ker = N := by
  apply le_antisymm _ (N_le_conjHom_ker hπsurj hπker hN)
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  change conjEquiv hπsurj hπker g = 1 at hg
  rw [hN g]
  intro x hx
  let x' : ↥X := ⟨x, hx⟩
  have h1 : conjEquiv hπsurj hπker g (Multiplicative.toAdd (π x')) =
      Multiplicative.toAdd (π x') := by
    have := congrArg (fun e : W ≃ₗ[ZMod 2] W => e (Multiplicative.toAdd (π x'))) hg
    simpa using this
  rw [conjEquiv_apply] at h1
  have h2 : π (MulAut.conjNormal g x') = π x' := Multiplicative.toAdd.injective h1
  have h3 : π (commConj g x') = 1 := by
    rw [commConj, map_mul, map_inv, h2, mul_inv_cancel]
  have h4 : commConj g x' ∈ Subgroup.center ↥X := by
    rw [← hπker, MonoidHom.mem_ker]
    exact h3
  have h5 : (commConj g x' : G) ∈ (Subgroup.center ↥X).map X.subtype :=
    Subgroup.mem_map.mpr ⟨commConj g x', h4, rfl⟩
  rwa [coe_commConj] at h5

theorem commutator_le_comap_rangeSubgroup (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    ⁅X, Subgroup.zpowers g⁆ ≤
      ((rangeSubgroup (conjEquiv hπsurj hπker g)).comap π).map X.subtype := by
  rw [Subgroup.commutator_le]
  intro y hy b hb
  rw [Subgroup.mem_zpowers_iff] at hb
  obtain ⟨k, rfl⟩ := hb
  rw [Subgroup.mem_map]
  refine ⟨commSelf (g ^ k) ⟨y, hy⟩, ?_, ?_⟩
  · rw [Subgroup.mem_comap, mem_rangeSubgroup]
    have h := toAdd_pi_commSelf_zpow hπsurj hπker g k ⟨y, hy⟩
    rw [h]
    have hrange := range_zpow_sub_le (conjEquiv hπsurj hπker g) k
    have hmem := hrange (LinearMap.mem_range_self _ (Multiplicative.toAdd (π ⟨y, hy⟩)))
    have heq : Multiplicative.toAdd (π ⟨y, hy⟩) -
        (conjEquiv hπsurj hπker g ^ k) (Multiplicative.toAdd (π ⟨y, hy⟩)) =
        -((conjEquiv hπsurj hπker g ^ k) (Multiplicative.toAdd (π ⟨y, hy⟩)) -
          Multiplicative.toAdd (π ⟨y, hy⟩)) := by
      abel
    rw [heq]
    exact neg_mem hmem
  · simpa using coe_commSelf (g ^ k) ⟨y, hy⟩

theorem comap_rangeSubgroup_eq (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    (rangeSubgroup (conjEquiv hπsurj hπker g)).comap π =
      (⁅X, Subgroup.zpowers g⁆).subgroupOf X ⊔ π.ker := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap, mem_rangeSubgroup] at hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hx
    obtain ⟨y, hyw⟩ := hπsurj (Multiplicative.ofAdd w)
    have hyw' : Multiplicative.toAdd (π y) = w := by rw [hyw, toAdd_ofAdd]
    rw [← hyw'] at hw
    have hcy : Multiplicative.toAdd (π (commConj g y)) = Multiplicative.toAdd (π x) := by
      rw [toAdd_pi_commConj hπsurj hπker g y]
      exact hw
    have hpi : π (commConj g y) = π x := Multiplicative.toAdd.injective hcy
    have hR : commConj g y ∈ (⁅X, Subgroup.zpowers g⁆).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf, coe_commConj,
        ← Subgroup.commutator_comm (Subgroup.zpowers g) X]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers g) y.2
    have hker : x * (commConj g y)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpi, mul_inv_cancel]
    have hx' : x = (x * (commConj g y)⁻¹) * commConj g y := by group
    rw [hx']
    exact mul_mem (Subgroup.mem_sup_right hker) (Subgroup.mem_sup_left hR)
  · rw [sup_le_iff]
    constructor
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_comap, mem_rangeSubgroup]
      have hle := commutator_le_comap_rangeSubgroup hπsurj hπker g
      have hxC : (x : G) ∈
          ((rangeSubgroup (conjEquiv hπsurj hπker g)).comap π).map X.subtype := hle hx
      rw [Subgroup.mem_map] at hxC
      obtain ⟨z, hz, hzx⟩ := hxC
      rw [Subtype.ext hzx] at hz
      exact hz
    · exact ker_le_comap_rangeSubgroup hπker (conjEquiv hπsurj hπker g)

theorem subgroupOf_sup_eq_comap (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) :
    (⁅X, Subgroup.zpowers g⁆ ⊔ (Subgroup.center ↥X).map X.subtype).subgroupOf X =
      (rangeSubgroup (conjEquiv hπsurj hπker g)).comap π := by
  rw [Subgroup.subgroupOf_sup (Subgroup.commutator_le_left (H₁ := X) (H₂ := Subgroup.zpowers g))
      (Subgroup.map_subtype_le (Subgroup.center ↥X)), subgroupOf_map_center, ← hπker,
    ← comap_rangeSubgroup_eq hπsurj hπker g]

theorem card_comap_of_surjective {G' H' : Type*} [Group G'] [Group H']
    (f : G' →* H') (hf : Function.Surjective f) (K : Subgroup H') :
    Nat.card ↥(K.comap f) = Nat.card ↥f.ker * Nat.card ↥K := by
  let L : Subgroup G' := K.comap f
  have hker_le : f.ker ≤ L := by
    intro x hx
    change x ∈ K.comap f
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact K.one_mem
  have hcard_ker : Nat.card ↥(f.ker.subgroupOf L) = Nat.card ↥f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  let f' : ↥L →* ↥K :=
    { toFun := fun x => ⟨f x.1, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hf' : Function.Surjective f' := by
    intro k
    obtain ⟨x, hx⟩ := hf k.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hx]; exact k.2
    · ext; exact hx
  have hker' : f'.ker = f.ker.subgroupOf L := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact Subtype.ext_iff.mp h
    · intro h; exact Subtype.ext h
  calc Nat.card ↥L
      = Nat.card (↥L ⧸ f'.ker) * Nat.card ↥f'.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker
    _ = Nat.card ↥K * Nat.card ↥f'.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hf').toEquiv]
    _ = Nat.card ↥K * Nat.card ↥f.ker := by rw [hker', hcard_ker]
    _ = Nat.card ↥f.ker * Nat.card ↥K := Nat.mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
