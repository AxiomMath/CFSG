module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift
public import Mathlib.LinearAlgebra.BilinearMap
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {Y S : Type*} [Group Y] [Group S]

theorem commutatorElement_mul_center_left {u v z : Y} (hz : z ∈ Subgroup.center Y) :
    ⁅u * z, v⁆ = ⁅u, v⁆ := by
  have hzv : ⁅z, v⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz v).symm
  rw [CFSG.LocalAnalysis.GorensteinLyons.commutatorElement_mul_left_of_mem_center
    (hzv ▸ Subgroup.one_mem _), hzv, one_mul]

theorem commutatorElement_mul_center_right {u v z : Y} (hz : z ∈ Subgroup.center Y) :
    ⁅u, v * z⁆ = ⁅u, v⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_center_left hz, commutatorElement_inv]

theorem commutatorElement_eq_of_map_eq {π : Y →* S} (hZ : π.ker ≤ Subgroup.center Y)
    {u u' v v' : Y} (hu : π u = π u') (hv : π v = π v') : ⁅u, v⁆ = ⁅u', v'⁆ := by
  have hu' : u⁻¹ * u' ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
  have hv' : v⁻¹ * v' ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hv, inv_mul_cancel]
  have h1 : u' = u * (u⁻¹ * u') := by group
  have h2 : v' = v * (v⁻¹ * v') := by group
  rw [h1, h2, commutatorElement_mul_center_left (hZ hu'),
    commutatorElement_mul_center_right (hZ hv')]

theorem exists_unique_involution_lift [Finite Y] [Finite S] {π : Y →* S}
    (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center Y) (hZodd : Odd (Nat.card π.ker)) {t : S}
    (ht : orderOf t = 2) :
    ∃ t' : Y, π t' = t ∧ orderOf t' = 2 ∧
      ∀ y : Y, π y ∈ Subgroup.zpowers t → orderOf y = 2 → y = t' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ z ∈ π.ker, z ^ 2 = 1 → z = 1 := by
    intro z hz hz2
    have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have h2 : orderOf z ∣ Nat.card π.ker := by
      rw [← Subgroup.orderOf_mk z hz]
      exact orderOf_dvd_natCard _
    have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr hZodd) h1 h2
    exact orderOf_eq_one_iff.mp h3
  have hmap : ∀ y : Y, π y ∈ Subgroup.zpowers t → orderOf y = 2 → π y = t := by
    intro y hy hy2
    rw [mem_zpowers_iff_mem_range_orderOf, ht] at hy
    obtain ⟨k, hk, hky⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hk
    interval_cases k
    · exfalso
      rw [pow_zero] at hky
      have h1 : y = 1 := hker y (MonoidHom.mem_ker.mpr hky.symm)
        (by rw [← hy2]; exact pow_orderOf_eq_one y)
      rw [h1, orderOf_one] at hy2
      omega
    · rw [pow_one] at hky
      exact hky.symm
  set D := (Subgroup.zpowers t).comap π
  have hD2 : 2 ∣ Nat.card D := by
    let f : D →* Subgroup.zpowers t := (π.comp D.subtype).codRestrict _ fun d => d.2
    have hf : Function.Surjective f := by
      rintro ⟨s, hs⟩
      obtain ⟨y, rfl⟩ := hπ s
      exact ⟨⟨y, hs⟩, rfl⟩
    have h := Subgroup.card_dvd_of_surjective hf
    rwa [Nat.card_zpowers, ht] at h
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hD2
  have hd' : orderOf (d : Y) = 2 := by rw [Subgroup.orderOf_coe, hd]
  refine ⟨d, hmap d d.2 hd', hd', fun y hy hy2 => ?_⟩
  have hz : (d : Y)⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmap d d.2 hd', hmap y hy hy2, inv_mul_cancel]
  have hcomm : Commute (d : Y) ((d : Y)⁻¹ * y) := Subgroup.mem_center_iff.mp (hZ hz) (d : Y)
  have hyd : y = (d : Y) * ((d : Y)⁻¹ * y) := by group
  have hy1 : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
  have hd1 : (d : Y) ^ 2 = 1 := by rw [← hd']; exact pow_orderOf_eq_one _
  have hz2 : ((d : Y)⁻¹ * y) ^ 2 = 1 := by
    have h := hy1
    rw [hyd, hcomm.mul_pow, hd1, one_mul] at h
    exact h
  have h1 := hker _ hz hz2
  rw [inv_mul_eq_one] at h1
  exact h1.symm

@[expose] noncomputable def zmodBilinOfBiadditive {p : ℕ} {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (b : M → M → ZMod p) (h1 : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (h2 : ∀ x y y', b x (y + y') = b x y + b x y') : LinearMap.BilinForm (ZMod p) M :=
  AddMonoidHom.toZModLinearMap p (AddMonoidHom.mk'
    (fun x => AddMonoidHom.toZModLinearMap p (AddMonoidHom.mk' (b x) (h2 x)))
    (fun x x' => by ext y; exact h1 x x' y))

theorem zmodBilinOfBiadditive_apply {p : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (b : M → M → ZMod p) (h1 : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (h2 : ∀ x y y', b x (y + y') = b x y + b x y') (x y : M) :
    zmodBilinOfBiadditive b h1 h2 x y = b x y :=
  rfl

@[expose] def kernelOmega {π : Y →* S} (hZ : π.ker ≤ Subgroup.center Y) (p : ℕ) : Subgroup Y where
  carrier := {z | z ∈ π.ker ∧ z ^ p = 1}
  one_mem' := ⟨one_mem _, one_pow p⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [(show Commute a b from Subgroup.mem_center_iff.mp (hZ hb.1) a).mul_pow, ha.2, hb.2,
      one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem kernelOmega_isElementaryAbelian {π : Y →* S} (hZ : π.ker ≤ Subgroup.center Y) (p : ℕ) :
    CFSG.IsElementaryAbelian p (kernelOmega hZ p) where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_center_iff.mp (hZ b.2.1) (a : Y))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z =>
    Subtype.ext (by rw [Subgroup.coe_pow, z.2.2, Subgroup.coe_one])

theorem commute_of_mem_comap_of_forms {π : Y →* S} (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center Y) {p : ℕ} [Fact p.Prime] {E C : Subgroup S}
    [hE : CFSG.IsElementaryAbelian p E] (hCE : C ≤ Subgroup.normalizer (E : Set S))
    (hforms : ∀ B : LinearMap.BilinForm (ZMod p) (Additive E), (∀ x, B x x = 0) →
      (∀ (c : C) (x y : E), B (Additive.ofMul (E.normalizerMonoidHom ⟨c, hCE c.2⟩ x))
        (Additive.ofMul (E.normalizerMonoidHom ⟨c, hCE c.2⟩ y)) =
          B (Additive.ofMul x) (Additive.ofMul y)) → B = 0) :
    ∀ u ∈ E.comap π, ∀ v ∈ E.comap π, u * v = v * u := by
  set W := kernelOmega hZ p
  have : CFSG.IsElementaryAbelian p W := kernelOmega_isElementaryAbelian hZ p
  set ℓ : S → Y := Function.surjInv hπ
  have hℓ : ∀ s, π (ℓ s) = s := Function.surjInv_eq hπ
  have hcomW : ∀ a b : Y, π a ∈ E → π b ∈ E → ⁅a, b⁆ ∈ W := by
    intro a b ha hb
    have hker : ⁅a, b⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (mul_comm' (⟨π a, ha⟩ : E) ⟨π b, hb⟩)
    refine ⟨hker, ?_⟩
    have hap : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (π a) ha
    rw [← CFSG.LocalAnalysis.GorensteinLyons.commutatorElement_pow_left_of_mem_center
      (hZ hker) p, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hZ hap) b |>.symm
  have hℓE : ∀ x : E, π (ℓ x) ∈ E := fun x => by rw [hℓ]; exact x.2
  let pair : E → E → W := fun x y => ⟨⁅ℓ x, ℓ y⁆, hcomW _ _ (hℓE x) (hℓE y)⟩
  have hcen : ∀ x y : E, ⁅ℓ x, ℓ y⁆ ∈ Subgroup.center Y := fun x y =>
    hZ (hcomW _ _ (hℓE x) (hℓE y)).1
  have hpl : ∀ x x' y : E, pair (x * x') y = pair x y * pair x' y := by
    intro x x' y
    apply Subtype.ext
    change ⁅ℓ (x * x' : E), ℓ y⁆ = ⁅ℓ x, ℓ y⁆ * ⁅ℓ x', ℓ y⁆
    rw [commutatorElement_eq_of_map_eq hZ (u' := ℓ x * ℓ x') (v' := ℓ y)
      (by rw [map_mul, hℓ, hℓ, hℓ]; rfl) rfl,
      CFSG.LocalAnalysis.GorensteinLyons.commutatorElement_mul_left_of_mem_center (hcen x' y),
      (Subgroup.mem_center_iff.mp (hcen x' y) _).symm]
  have hpr : ∀ x y y' : E, pair x (y * y') = pair x y * pair x y' := by
    intro x y y'
    apply Subtype.ext
    change ⁅ℓ x, ℓ (y * y' : E)⁆ = ⁅ℓ x, ℓ y⁆ * ⁅ℓ x, ℓ y'⁆
    have hc' : ⁅ℓ y', ℓ x⁆ ∈ Subgroup.center Y := by
      rw [← commutatorElement_inv]
      exact inv_mem (hcen x y')
    rw [commutatorElement_eq_of_map_eq hZ (u' := ℓ x) (v' := ℓ y * ℓ y') rfl
      (by rw [map_mul, hℓ, hℓ, hℓ]; rfl), ← commutatorElement_inv,
      CFSG.LocalAnalysis.GorensteinLyons.commutatorElement_mul_left_of_mem_center hc',
      mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
  have hpd : ∀ x : E, pair x x = 1 := fun x => Subtype.ext (commutatorElement_self _)
  have hpc : ∀ (c : C) (x y : E), pair (E.normalizerMonoidHom ⟨c, hCE c.2⟩ x)
      (E.normalizerMonoidHom ⟨c, hCE c.2⟩ y) = pair x y := by
    intro c x y
    apply Subtype.ext
    change ⁅ℓ (E.normalizerMonoidHom ⟨c, hCE c.2⟩ x : E),
      ℓ (E.normalizerMonoidHom ⟨c, hCE c.2⟩ y : E)⁆ = ⁅ℓ x, ℓ y⁆
    set g := ℓ (c : S)
    rw [commutatorElement_eq_of_map_eq hZ (u' := g * ℓ x * g⁻¹) (v' := g * ℓ y * g⁻¹)
      (by simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_inv, hℓ, g])
      (by simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_inv, hℓ, g]),
      ← CFSG.LocalAnalysis.GorensteinLyons.conj_commutatorElement_eq,
      Subgroup.mem_center_iff.mp (hcen x y) g, mul_inv_cancel_right]
  have hpair : ∀ x y : E, pair x y = 1 := by
    intro x y
    have hdual : ∀ f : Module.Dual (ZMod p) (Additive W),
        f (Additive.ofMul (pair x y)) = 0 := by
      intro f
      let b : Additive E → Additive E → ZMod p := fun a a' =>
        f (Additive.ofMul (pair (Additive.toMul a) (Additive.toMul a')))
      have hb1 : ∀ a a' a'', b (a + a') a'' = b a a'' + b a' a'' := by
        intro a a' a''
        change f (Additive.ofMul (pair (Additive.toMul a * Additive.toMul a') _)) = _
        rw [hpl, ofMul_mul, map_add]
      have hb2 : ∀ a a' a'', b a (a' + a'') = b a a' + b a a'' := by
        intro a a' a''
        change f (Additive.ofMul (pair _ (Additive.toMul a' * Additive.toMul a''))) = _
        rw [hpr, ofMul_mul, map_add]
      have hB := hforms (zmodBilinOfBiadditive b hb1 hb2)
        (fun a => by
          rw [zmodBilinOfBiadditive_apply]
          change f (Additive.ofMul (pair _ _)) = 0
          rw [hpd, ofMul_one, map_zero])
        (fun c a a' => by
          rw [zmodBilinOfBiadditive_apply, zmodBilinOfBiadditive_apply]
          change f (Additive.ofMul (pair _ _)) = f (Additive.ofMul (pair _ _))
          rw [toMul_ofMul, toMul_ofMul, toMul_ofMul, toMul_ofMul, hpc])
      have h := congrArg (fun B : LinearMap.BilinForm (ZMod p) (Additive E) =>
        B (Additive.ofMul x) (Additive.ofMul y)) hB
      simpa [zmodBilinOfBiadditive_apply, b] using h
    have h := (Module.forall_dual_apply_eq_zero_iff (ZMod p) (Additive.ofMul (pair x y))).mp hdual
    exact h
  intro u hu v hv
  have h := congrArg Subtype.val (hpair ⟨π u, hu⟩ ⟨π v, hv⟩)
  change ⁅ℓ (π u), ℓ (π v)⁆ = 1 at h
  rw [commutatorElement_eq_of_map_eq hZ (u' := u) (v' := v) (hℓ _) (hℓ _),
    commutatorElement_eq_one_iff_mul_comm] at h
  exact h

end CFSG.RankThree.GroupTheory
