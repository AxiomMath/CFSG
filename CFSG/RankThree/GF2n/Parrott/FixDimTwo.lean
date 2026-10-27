module

public import CFSG.RankThree.GF2n.Parrott.SplitV
public import CFSG.LinearAlgebra.F2OrderNineFixed
public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
public import CFSG.RankThree.GF2n.Parrott.FixDim

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open Polynomial Module

variable {G : Type} [Group G] [Finite G] {z : G}

section AddAutLinearEquiv

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] noncomputable def mulAutOfLinearEquiv (u : M ≃ₗ[ZMod 2] M) :
    MulAut (Multiplicative M) where
  toFun x := Multiplicative.ofAdd (u x.toAdd)
  invFun x := Multiplicative.ofAdd (u.symm x.toAdd)
  left_inv x := by
    show Multiplicative.ofAdd (u.symm (u x.toAdd)) = x
    rw [u.symm_apply_apply x.toAdd]
    simp
  right_inv x := by
    show Multiplicative.ofAdd (u (u.symm x.toAdd)) = x
    rw [u.apply_symm_apply x.toAdd]
    simp
  map_mul' x y := by
    show Multiplicative.ofAdd (u (x.toAdd + y.toAdd)) =
      Multiplicative.ofAdd (u x.toAdd) * Multiplicative.ofAdd (u y.toAdd)
    rw [map_add, ofAdd_add]

@[expose] noncomputable def addAutLinearEquiv :
    MulAut (Multiplicative M) ≃* (M ≃ₗ[ZMod 2] M) where
  toFun g :=
    { toLinearMap := mulAutToLinearMap g
      invFun := mulAutToLinearMap g.symm
      left_inv := by
        intro m
        simp [mulAutToLinearMap_apply]
      right_inv := by
        intro m
        simp [mulAutToLinearMap_apply] }
  invFun := mulAutOfLinearEquiv
  left_inv g := by
    ext x
    simp [mulAutOfLinearEquiv, mulAutToLinearMap_apply]
  right_inv u := by
    ext x
    change mulAutToLinearMap (mulAutOfLinearEquiv u) x = u x
    rw [mulAutToLinearMap_apply]
    rfl
  map_mul' g₁ g₂ := by
    ext x
    simp [mulAutToLinearMap_apply]

noncomputable abbrev addAutLinearEquivMonoidHom :
    MulAut (Multiplicative M) →* (M ≃ₗ[ZMod 2] M) :=
  (addAutLinearEquiv (M := M)).toMonoidHom

@[simp] theorem addAutLinearEquiv_apply (g : MulAut (Multiplicative M)) (m : M) :
    addAutLinearEquiv g m = (g (Multiplicative.ofAdd m)).toAdd := by
  simp [addAutLinearEquiv, mulAutToLinearMap_apply]

theorem addAutLinearEquivMonoidHom_toLinearMap (g : MulAut (Multiplicative M)) :
    (addAutLinearEquivMonoidHom g).toLinearMap = mulAutToLinearMap g := by
  rfl

@[simp] theorem addAutLinearEquivMonoidHom_apply (g : MulAut (Multiplicative M)) (m : M) :
    addAutLinearEquivMonoidHom g m = (g (Multiplicative.ofAdd m)).toAdd := by
  simp [addAutLinearEquivMonoidHom]

theorem addAutLinearEquivMonoidHom_injective :
    Function.Injective (addAutLinearEquivMonoidHom (M := M)) := by
  intro g h hgh
  apply (addAutLinearEquiv (M := M)).injective
  simpa [addAutLinearEquivMonoidHom] using hgh

theorem addAutLinearEquivMonoidHom_pow (g : MulAut (Multiplicative M)) (k : ℕ) :
    addAutLinearEquivMonoidHom (g ^ k) = addAutLinearEquivMonoidHom g ^ k :=
  map_pow _ g k

end AddAutLinearEquiv

section FixSubmoduleKer

variable (h : Tim79a.ParrottHyp z)

@[expose] noncomputable def conjVLinearMap (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  (addAutLinearEquivMonoidHom
    (MulAut.congr (mulEquivVAdd (z := z)) (conjV h x))).toLinearMap

@[simp] theorem conjVLinearMap_apply (x : H z) (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    conjVLinearMap h x v = Additive.ofMul ((conjV h x) (Additive.toMul v)) := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [conjVLinearMap, addAutLinearEquivMonoidHom_toLinearMap, mulAutToLinearMap_apply]
  rfl

theorem fixSubmodule_eq_ker (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    fixSubmodule h x = LinearMap.ker (conjVLinearMap h x - 1) := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  rw [mem_fixSubmodule_iff, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero, mem_autFixedSubgroup]
  change conjV h x (Additive.toMul v) = Additive.toMul v ↔ conjVLinearMap h x v = v
  rw [conjVLinearMap_apply]
  constructor
  · intro hfix
    simpa using congrArg Additive.ofMul hfix
  · intro hfix
    simpa using congrArg Additive.toMul hfix

end FixSubmoduleKer

section ConjZCube

variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem conjZ_cube_eq_one (h : Tim79a.ParrottHyp z) {y : H z} (hy : orderOf y = 9) :
    (conjZ z y) ^ 3 = 1 := by
  have hdvd9 : orderOf (conjZ z y) ∣ 9 := by
    simpa [hy] using orderOf_map_dvd (conjZ z) y
  have hdvd6 : orderOf (conjZ z y) ∣ Nat.card (MulAut (centerIn (J z))) :=
    orderOf_dvd_natCard _
  rw [card_mulAut_centerIn_J h] at hdvd6
  have hdvd3 : orderOf (conjZ z y) ∣ 3 := by
    have hgcd := Nat.dvd_gcd hdvd9 hdvd6
    norm_num at hgcd
    exact hgcd
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd3

end ConjZCube

section ConjVNeOne

variable [hN : ((J z).subgroupOf (H z)).Normal]

private theorem conjJ'_eq_one_of_conjV_eq_one (h : Tim79a.ParrottHyp z) {σ : H z}
    (hσ : orderOf σ = 3) (hZσ : conjZ z σ = 1) (hVσ : conjV h σ = 1) :
    conjJ' z σ = 1 := by
  apply MulEquiv.ext
  intro x
  have hpi : QuotientV.pi z (conjJ' z σ x) = QuotientV.pi z x := by
    have h := congrArg (fun g : MulAut (QuotientV.V z) => g (QuotientV.pi z x)) hVσ
    simpa [conjV_mk] using h
  have hker : conjJ' z σ x * x⁻¹ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker]
    calc QuotientV.pi z (conjJ' z σ x * x⁻¹)
        = QuotientV.pi z (conjJ' z σ x) * (QuotientV.pi z x)⁻¹ := by rw [map_mul, map_inv]
      _ = QuotientV.pi z x * (QuotientV.pi z x)⁻¹ := by rw [hpi]
      _ = 1 := mul_inv_cancel _
  rw [QuotientV.pi_ker] at hker
  let ζ : centerIn (J z) :=
    ⟨((conjJ' z σ x * x⁻¹ : J z) : G), Subgroup.mem_subgroupOf.mp hker⟩
  let ζJ : J z := ⟨(ζ : G), ζ.2.1⟩
  have hrel : (conjJ' z σ x : G) = (ζ : G) * (x : G) := by
    have hζ : (ζ : G) = (conjJ' z σ x : G) * (x : G)⁻¹ := rfl
    rw [hζ]
    group
  have hconjx : conjJ' z σ x = ζJ * x := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hrel
  have hfixζ : conjJ' z σ ζJ = ζJ := by
    apply Subtype.ext
    change (conjJ' z σ ζJ : G) = (ζ : G)
    rw [conjJ'_apply_coe]
    have hcent : (ζ : G) ∈ Subgroup.centralizer ({(σ : G)} : Set G) :=
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZσ ζ.2
    have hcomm : (ζ : G) * (σ : G) = (σ : G) * (ζ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hcent
    rw [← hcomm]
    group
  have hpow : ∀ k : ℕ, ((conjJ' z σ : MulAut (J z)) ^ k) x = ζJ ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc ((conjJ' z σ : MulAut (J z)) ^ (k + 1)) x
            = (conjJ' z σ) (((conjJ' z σ : MulAut (J z)) ^ k) x) := by
              rw [pow_succ']
              rfl
          _ = (conjJ' z σ) (ζJ ^ k * x) := by rw [ih]
          _ = (conjJ' z σ) (ζJ ^ k) * (conjJ' z σ) x := by rw [map_mul]
          _ = ζJ ^ k * (ζJ * x) := by rw [map_pow, hfixζ, hconjx]
          _ = ζJ ^ (k + 1) * x := by group
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have h3 : (conjJ' z σ : MulAut (J z)) ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  have hx3 : ((conjJ' z σ : MulAut (J z)) ^ 3) x = x := by rw [h3]; rfl
  have hζ3 : ζJ ^ 3 = 1 := by
    have h := hpow 3
    rw [hx3] at h
    have h' : ζJ ^ 3 * x = 1 * x := by simpa using h.symm
    exact mul_right_cancel h'
  have hζ2 : (ζ : G) * (ζ : G) = 1 := centerIn_J_sq h ζ.2
  have hζ3G : (ζ : G) ^ 3 = 1 := by
    have := congrArg (fun j : J z => (j : G)) hζ3
    simpa using this
  have hζeq : (ζ : G) = 1 := by
    have hcube : (ζ : G) ^ 3 = (ζ : G) * ((ζ : G) * (ζ : G)) := by
      rw [pow_succ, pow_two]
      group
    rw [hcube, hζ2, mul_one] at hζ3G
    exact hζ3G
  have hζJ_one : ζJ = 1 := by
    apply Subtype.ext
    change (ζ : G) = 1
    exact hζeq
  rw [hconjx, hζJ_one, one_mul]
  rfl

theorem conjV_ne_one_of_order_three (h : Tim79a.ParrottHyp z) {σ : H z}
    (hσ : orderOf σ = 3) (hZσ : conjZ z σ = 1) :
    conjV h σ ≠ 1 := by
  intro hVσ
  have hconjJ : conjJ' z σ = 1 := conjJ'_eq_one_of_conjV_eq_one h hσ hZσ hVσ
  have hσcent : (σ : G) ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hfix : conjJ' z σ ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [hconjJ]
      rfl
    have hcoe := congrArg (fun j : J z => (j : G)) hfix
    rw [conjJ'_apply_coe] at hcoe
    have hcomm : (σ : G) * (y : G) = (y : G) * (σ : G) := by
      calc (σ : G) * (y : G) = ((σ : G) * (y : G) * (σ : G)⁻¹) * (σ : G) := by group
        _ = (y : G) * (σ : G) := by rw [hcoe]
    exact hcomm.symm
  have hHyp : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z := by
    obtain ⟨-, -, -, hcent, -⟩ := h
    simpa [J, H] using hcent
  have hσJ : (σ : G) ∈ J z := hHyp ⟨σ.2, hσcent⟩
  have hdvd : orderOf σ ∣ Nat.card (J z) := by
    simpa [Subgroup.orderOf_coe] using Subgroup.orderOf_dvd_natCard (J z) hσJ
  rw [hσ, card_J h] at hdvd
  have h3dvd : 3 ∣ 2 ^ 10 := hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
  norm_num at h32

end ConjVNeOne

theorem linearEquiv_toLinearMap_pow {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] M) (k : ℕ) :
    e.toLinearMap ^ k = (e ^ k).toLinearMap := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, LinearEquiv.coe_toLinearMap_mul]

section FixDimTwo

variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem fixDimV_eq_two (h : Tim79a.ParrottHyp z) {y σ : H z}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ) :
    fixDimV h σ = 2 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hy9 : y ^ 9 = 1 := by rw [← hy, pow_orderOf_eq_one]
  have hσ3 : orderOf σ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hZσ : conjZ z σ = 1 := by
    rw [← hyσ, map_pow, conjZ_cube_eq_one h hy]
  have hg9 : (MulAut.congr (mulEquivVAdd (z := z)) (conjV h y)) ^ 9 = 1 := by
    rw [← map_pow,
      show (conjV h y) ^ 9 = conjV h (y ^ 9) from (map_pow (conjV h) y 9).symm, hy9,
      map_one (conjV h)]
    exact map_one (MulAut.congr (mulEquivVAdd (z := z)) : MulAut (QuotientV.V z) →*
      MulAut (Multiplicative (Additive (QuotientV.V z))))
  have hT9 : (conjVLinearMap h y) ^ 9 = 1 := by
    dsimp only [conjVLinearMap]
    rw [linearEquiv_toLinearMap_pow, ← addAutLinearEquivMonoidHom_pow, hg9, map_one,
      LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  have hg3 : (MulAut.congr (mulEquivVAdd (z := z)) (conjV h y)) ^ 3 =
      MulAut.congr (mulEquivVAdd (z := z)) (conjV h σ) := by
    rw [← map_pow,
      show (conjV h y) ^ 3 = conjV h (y ^ 3) from (map_pow (conjV h) y 3).symm, hyσ]
  have hT3 : (conjVLinearMap h y) ^ 3 = conjVLinearMap h σ := by
    dsimp only [conjVLinearMap]
    rw [linearEquiv_toLinearMap_pow, ← addAutLinearEquivMonoidHom_pow, hg3]
  have hT3_ne_one : (conjVLinearMap h y) ^ 3 ≠ 1 := by
    intro h3
    have hlin : conjVLinearMap h σ = 1 := by
      rw [← hT3, h3]
    let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    have heσ : addAutLinearEquivMonoidHom
        (MulAut.congr (mulEquivVAdd (z := z)) (conjV h σ)) =
          LinearEquiv.refl (ZMod 2) (Additive (QuotientV.V z)) := by
      apply LinearEquiv.ext
      intro v
      have hv := LinearMap.congr_fun hlin v
      rw [show conjVLinearMap h σ = (addAutLinearEquivMonoidHom
        (MulAut.congr (mulEquivVAdd (z := z)) (conjV h σ))).toLinearMap from rfl] at hv
      simpa using hv
    have hmapone : addAutLinearEquivMonoidHom
        (1 : MulAut (Multiplicative (Additive (QuotientV.V z)))) =
          LinearEquiv.refl (ZMod 2) (Additive (QuotientV.V z)) := by
      apply LinearEquiv.ext
      intro v
      simp
    have hgσ : MulAut.congr (mulEquivVAdd (z := z)) (conjV h σ) = 1 := by
      apply addAutLinearEquivMonoidHom_injective
      rw [hmapone]
      exact heσ
    have hconjV : conjV h σ = 1 := by
      simpa using (MulAut.congr (mulEquivVAdd (z := z))).injective hgσ
    exact conjV_ne_one_of_order_three h hσ3 hZσ hconjV
  have hmain := CFSG.LinearAlgebra.F2OrderNineFixed.finrank_ker_cube_sub_one_eq_two
    (V := Additive (QuotientV.V z)) (finrank_addV h) (conjVLinearMap h y) hT9 hT3_ne_one
  rw [fixDimV, fixSubmodule_eq_ker h σ, ← hT3]
  exact hmain

theorem card_centralizerJ_eq_sixteen (h : Tim79a.ParrottHyp z) {y σ : H z}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ) :
    Nat.card (centralizerJ σ) = 16 := by
  let _ : CommGroup (QuotientV.V z) := commGroupV h
  let _ : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hσ3 : orderOf σ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hZσ : conjZ z σ = 1 := by
    rw [← hyσ, map_pow, conjZ_cube_eq_one h hy]
  have hcenter_le : Subgroup.center (J z) ≤ centralizerJ σ := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZσ hjZ)
  have hinf : centralizerJ σ ⊓ Subgroup.center (J z) = Subgroup.center (J z) :=
    inf_eq_right.mpr hcenter_le
  have hform := card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
    (z := z) (h := h) (x := σ) hσ3
  rw [hform, hinf, card_center_subgroupOf_J h, fixDimV_eq_two h hy hyσ]
  norm_num

end FixDimTwo

end CFSG.RankThree.GF2n.Parrott
