module

public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.RankThree.CentralExtension.InvariantComplement


public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {D : Type*} [Group D]

section ClassTwo

variable (hc : ∀ x y : D, ⁅x, y⁆ ∈ center D)
include hc

omit hc in
theorem mul_eq_commutatorElement_mul (x y : D) : x * y = ⁅x, y⁆ * y * x := by
  rw [commutatorElement_def]; group

theorem commute_commutatorElement (x y g : D) : Commute ⁅x, y⁆ g :=
  (mem_center_iff.1 (hc x y) g).symm

theorem commutatorElement_mul_left_class_two (x y z : D) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, mem_center_iff.1 (hc y z) x, mul_inv_cancel_right]
  exact (commute_commutatorElement hc y z ⁅x, z⁆).eq

theorem commutatorElement_mul_right_class_two (x y z : D) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅x, y⁆ y,
    mem_center_iff.1 (hc x z) y, ← mul_assoc, mul_inv_cancel_right]

end ClassTwo

section Baer

variable (hc : ∀ x y : D, ⁅x, y⁆ ∈ center D)

theorem commutatorElement_pow_self (x : D) (n : ℕ) : ⁅x ^ n, x⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 ((Commute.refl x).pow_left n).eq

theorem commutatorElement_zpow_self (x : D) (n : ℤ) : ⁅x ^ n, x⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 ((Commute.refl x).zpow_left n).eq

include hc in
theorem baer_assoc (h : ℕ) (x y z : D) :
    x * y * ⁅x, y⁆ ^ h * z * ⁅x * y * ⁅x, y⁆ ^ h, z⁆ ^ h =
      x * (y * z * ⁅y, z⁆ ^ h) * ⁅x, y * z * ⁅y, z⁆ ^ h⁆ ^ h := by
  have hk₁ : ⁅x, y⁆ ^ h ∈ center D := pow_mem (hc x y) h
  have hk₂ : ⁅y, z⁆ ^ h ∈ center D := pow_mem (hc y z) h
  rw [commutatorElement_mul_center_left hk₁, commutatorElement_mul_center_right hk₂,
    commutatorElement_mul_left_class_two hc, commutatorElement_mul_right_class_two hc]
  have e₁ : x * y * ⁅x, y⁆ ^ h * z * (⁅x, z⁆ * ⁅y, z⁆) ^ h =
      x * y * z * (⁅x, y⁆ ^ h * (⁅x, z⁆ * ⁅y, z⁆) ^ h) := by
    rw [mul_assoc (x * y), ← mem_center_iff.1 hk₁ z]; group
  have e₂ : x * (y * z * ⁅y, z⁆ ^ h) * (⁅x, y⁆ * ⁅x, z⁆) ^ h =
      x * y * z * (⁅y, z⁆ ^ h * (⁅x, y⁆ * ⁅x, z⁆) ^ h) := by group
  rw [e₁, e₂]
  congr 1
  have key : (⟨⁅x, y⁆, hc x y⟩ : center D) ^ h * ((⟨⁅x, z⁆, hc x z⟩ : center D) *
      ⟨⁅y, z⁆, hc y z⟩) ^ h = (⟨⁅y, z⁆, hc y z⟩ : center D) ^ h *
      ((⟨⁅x, y⁆, hc x y⟩ : center D) * ⟨⁅x, z⁆, hc x z⟩) ^ h := by
    rw [mul_pow, mul_pow]
    conv_rhs => rw [mul_comm, mul_assoc]
  exact congrArg Subtype.val key

variable {p : ℕ} (hexp : ∀ x : D, x ^ p = 1) (hodd : p % 2 = 1)

include hc hexp hodd in
theorem baer_comm (x y : D) :
    x * y * ⁅x, y⁆ ^ ((p - 1) / 2) = y * x * ⁅y, x⁆ ^ ((p - 1) / 2) := by
  set h := (p - 1) / 2 with hh
  have h2 : 2 * h + 1 = p := by omega
  have hp1 : ⁅x, y⁆ ^ (h + 1) = (⁅x, y⁆ ^ h)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, show h + 1 + h = 2 * h + 1 by ring, h2, hexp]
  calc x * y * ⁅x, y⁆ ^ h = ⁅x, y⁆ * y * x * ⁅x, y⁆ ^ h := by
        rw [mul_eq_commutatorElement_mul x y]
    _ = y * x * (⁅x, y⁆ * ⁅x, y⁆ ^ h) := by
        rw [(commute_commutatorElement hc x y y).eq, mul_assoc y ⁅x, y⁆ x,
          (commute_commutatorElement hc x y x).eq]
        simp only [mul_assoc]
    _ = y * x * (⁅x, y⁆ ^ h)⁻¹ := by rw [← pow_succ', hp1]
    _ = y * x * ⁅y, x⁆ ^ h := by rw [← inv_pow, commutatorElement_inv]

abbrev baerAddCommGroup : AddCommGroup D where
  add x y := x * y * ⁅x, y⁆ ^ ((p - 1) / 2)
  add_assoc x y z := baer_assoc hc ((p - 1) / 2) x y z
  zero := 1
  zero_add x := by
    change 1 * x * ⁅(1 : D), x⁆ ^ ((p - 1) / 2) = x
    rw [commutatorElement_one_left, one_pow, mul_one, one_mul]
  add_zero x := by
    change x * 1 * ⁅x, (1 : D)⁆ ^ ((p - 1) / 2) = x
    rw [commutatorElement_one_right, one_pow, mul_one, mul_one]
  neg x := x⁻¹
  neg_add_cancel x := by
    change x⁻¹ * x * ⁅x⁻¹, x⁆ ^ ((p - 1) / 2) = 1
    rw [← zpow_neg_one, commutatorElement_zpow_self, one_pow, mul_one, zpow_neg_one,
      inv_mul_cancel]
  add_comm x y := baer_comm hc hexp hodd x y
  nsmul n x := x ^ n
  nsmul_zero x := pow_zero x
  nsmul_succ n x := by
    change x ^ (n + 1) = x ^ n * x * ⁅x ^ n, x⁆ ^ ((p - 1) / 2)
    rw [commutatorElement_pow_self, one_pow, mul_one, pow_succ]
  zsmul n x := x ^ n
  zsmul_zero' x := zpow_zero x
  zsmul_succ' n x := by
    change x ^ ((n.succ : ℕ) : ℤ) = x ^ (n : ℤ) * x * ⁅x ^ (n : ℤ), x⁆ ^ ((p - 1) / 2)
    rw [commutatorElement_zpow_self, one_pow, mul_one, ← zpow_add_one]
    rfl
  zsmul_neg' n x := by
    change x ^ (Int.negSucc n) = (x ^ ((n.succ : ℕ) : ℤ))⁻¹
    rw [zpow_negSucc, zpow_natCast]

end Baer

theorem exists_ofMul_of_eq (v : Additive (Abelianization D)) :
    ∃ x : D, Additive.ofMul (Abelianization.of x) = v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  refine ⟨x, ?_⟩
  change Additive.ofMul (QuotientGroup.mk x : Abelianization D) = v
  rw [hx]
  rfl

theorem abelianization_of_commutatorElement (x y : D) : Abelianization.of ⁅x, y⁆ = 1 := by
  rw [← MonoidHom.mem_ker, Abelianization.ker_of]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

section Form

variable {p : ℕ} (hZ : center D = commutator D) (ε : center D ≃* Multiplicative (ZMod p))

@[expose] def centerCommFormLeft (w : Additive (Abelianization D)) :
    Additive (Abelianization D) →+ ZMod p :=
  AddMonoidHom.mk' (fun v => Multiplicative.toAdd
    (CFSG.OddSolvableUnitary.commPairing hZ ε (Additive.toMul v) (Additive.toMul w)))
    fun v v' => by simp

@[expose] def centerCommFormRight (v : Additive (Abelianization D)) :
    Additive (Abelianization D) →+ ZMod p :=
  AddMonoidHom.mk' (fun w => Multiplicative.toAdd
    (CFSG.OddSolvableUnitary.commPairing hZ ε (Additive.toMul v) (Additive.toMul w)))
    fun w w' => by simp

variable [Module (ZMod p) (Additive (Abelianization D))]

@[expose] def centerCommForm : LinearMap.BilinForm (ZMod p) (Additive (Abelianization D)) :=
  LinearMap.mk₂ (ZMod p)
    (fun v w => Multiplicative.toAdd
      (CFSG.OddSolvableUnitary.commPairing hZ ε (Additive.toMul v) (Additive.toMul w)))
    (fun v v' w => map_add (centerCommFormLeft hZ ε w) v v')
    (fun c v w => ZMod.map_smul (centerCommFormLeft hZ ε w) c v)
    (fun v w w' => map_add (centerCommFormRight hZ ε v) w w')
    (fun c v w => ZMod.map_smul (centerCommFormRight hZ ε v) c w)

theorem centerCommForm_apply (x y : D) :
    centerCommForm hZ ε (Additive.ofMul (Abelianization.of x))
        (Additive.ofMul (Abelianization.of y)) =
      Multiplicative.toAdd
        (ε ⟨⁅x, y⁆, CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ x y⟩) :=
  rfl

theorem centerCommForm_isAlt_nondegenerate :
    (centerCommForm hZ ε).IsAlt ∧ (centerCommForm hZ ε).Nondegenerate := by
  obtain ⟨B, hBa, hBn, hB⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  have hEq : B = centerCommForm hZ ε := by
    refine LinearMap.BilinForm.ext fun v w => ?_
    obtain ⟨x, rfl⟩ := exists_ofMul_of_eq v
    obtain ⟨y, rfl⟩ := exists_ofMul_of_eq w
    rw [hB, centerCommForm_apply]
  exact hEq ▸ ⟨hBa, hBn⟩

end Form

variable (D) in
@[expose] def centerFixingAut : Subgroup (MulAut D) where
  carrier := {α | ∀ z ∈ center D, α z = z}
  one_mem' _ _ := rfl
  mul_mem' {α β} hα hβ z hz := by rw [MulAut.mul_apply, hβ z hz, hα z hz]
  inv_mem' {α} hα z hz := by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (hα z hz).symm

section Action

variable {p : ℕ} [Module (ZMod p) (Additive (Abelianization D))]

variable (p) in
@[expose] def autAbelianizationEndZMod :
    MulAut D →* Module.End (ZMod p) (Additive (Abelianization D)) where
  toFun ψ := (MonoidHom.toAdditive (Abelianization.map (ψ : D →* D))).toZModLinearMap p
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of_eq v
    rfl
  map_mul' ψ ψ' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of_eq v
    rfl

variable (p) in
@[expose] def autAbelianizationGLZMod :
    MulAut D →* LinearMap.GeneralLinearGroup (ZMod p) (Additive (Abelianization D)) :=
  (autAbelianizationEndZMod p).toHomUnits

theorem autAbelianizationGLZMod_apply (ψ : MulAut D) (x : D) :
    ((autAbelianizationGLZMod p ψ : LinearMap.GeneralLinearGroup (ZMod p)
        (Additive (Abelianization D))) :
        Additive (Abelianization D) →ₗ[ZMod p] Additive (Abelianization D))
        (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (ψ x)) :=
  rfl

variable (hZ : center D = commutator D) (ε : center D ≃* Multiplicative (ZMod p))

theorem autAbelianizationGLZMod_mem_bilinIsometryGroup (α : centerFixingAut D) :
    autAbelianizationGLZMod p (α : MulAut D) ∈
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (centerCommForm hZ ε) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
  intro v w
  obtain ⟨x, rfl⟩ := exists_ofMul_of_eq v
  obtain ⟨y, rfl⟩ := exists_ofMul_of_eq w
  rw [autAbelianizationGLZMod_apply, autAbelianizationGLZMod_apply, centerCommForm_apply,
    centerCommForm_apply]
  congr 2
  exact Subtype.ext (show ⁅(α : MulAut D) x, (α : MulAut D) y⁆ = ⁅x, y⁆ by
    rw [← map_commutatorElement]
    exact α.2 _ (CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ x y))

@[expose] def centerFixingAutSp : centerFixingAut D →*
    CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (centerCommForm hZ ε) :=
  ((autAbelianizationGLZMod p).comp (centerFixingAut D).subtype).codRestrict _
    fun α => autAbelianizationGLZMod_mem_bilinIsometryGroup hZ ε α

theorem centerFixingAutSp_apply (α : centerFixingAut D) (x : D) :
    (((centerFixingAutSp hZ ε α : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        (centerCommForm hZ ε)) : LinearMap.GeneralLinearGroup (ZMod p)
        (Additive (Abelianization D))) :
        Additive (Abelianization D) →ₗ[ZMod p] Additive (Abelianization D))
        (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of ((α : MulAut D) x)) :=
  rfl

end Action

section Section

variable {p : ℕ} [hp : Fact p.Prime] [Module (ZMod p) (Additive (Abelianization D))]

theorem exists_baer_section (hp2 : p ≠ 2) (hZ : center D = commutator D)
    (hexp : ∀ x : D, x ^ p = 1) :
    ∃ σ : Additive (Abelianization D) → D,
      (∀ v, Additive.ofMul (Abelianization.of (σ v)) = v) ∧
      ∀ v w, σ (v + w) = σ v * σ w * ⁅σ v, σ w⁆ ^ ((p - 1) / 2) := by
  classical
  have hc : ∀ x y : D, ⁅x, y⁆ ∈ center D :=
    CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  let B : AddCommGroup D := baerAddCommGroup hc hexp hodd
  have hadd : ∀ x y : D, x + y = x * y * ⁅x, y⁆ ^ ((p - 1) / 2) := fun _ _ => rfl
  have hzero : (0 : D) = 1 := rfl
  have hnsmul : ∀ (n : ℕ) (x : D), n • x = x ^ n := fun _ _ => rfl
  have M : Module (ZMod p) D := AddCommGroup.zmodModule fun x => by rw [hnsmul, hexp, hzero]
  let Zadd : AddSubgroup D :=
    { carrier := center D
      add_mem' := fun {a b} ha hb => by
        change a + b ∈ center D
        rw [hadd]
        exact mul_mem (mul_mem ha hb) (pow_mem (hc a b) _)
      zero_mem' := by change (0 : D) ∈ center D; rw [hzero]; exact one_mem _
      neg_mem' := fun {a} ha => by change a⁻¹ ∈ center D; exact inv_mem ha }
  let Zs : Submodule (ZMod p) D := AddSubgroup.toZModSubmodule p Zadd
  have hZs : ∀ x, x ∈ Zs ↔ x ∈ center D := fun x => Iff.rfl
  let prAdd : D →+ Additive (Abelianization D) :=
    { toFun := fun x => Additive.ofMul (Abelianization.of x)
      map_zero' := by rw [hzero, map_one, ofMul_one]
      map_add' := fun x y => by
        change Additive.ofMul (Abelianization.of (x * y * ⁅x, y⁆ ^ ((p - 1) / 2))) =
          Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of y)
        rw [map_mul Abelianization.of, map_mul Abelianization.of, map_pow Abelianization.of,
          abelianization_of_commutatorElement, one_pow, mul_one, ofMul_mul] }
  let pr : D →ₗ[ZMod p] Additive (Abelianization D) := prAdd.toZModLinearMap p
  have hpr : ∀ x, pr x = Additive.ofMul (Abelianization.of x) := fun _ => rfl
  have hprZ : ∀ x, pr x = 0 ↔ x ∈ center D := by
    intro x
    rw [hpr, ofMul_eq_zero, ← MonoidHom.mem_ker, Abelianization.ker_of, hZ]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl Zs
  have hinj : Function.Injective (pr.domRestrict W) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hxW⟩ hx
    rw [LinearMap.domRestrict_apply, hprZ] at hx
    have hmem : x ∈ Zs ⊓ W := ⟨(hZs x).2 hx, hxW⟩
    rw [hW.inf_eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsurj : Function.Surjective (pr.domRestrict W) := by
    intro v
    obtain ⟨x, rfl⟩ := exists_ofMul_of_eq v
    have hx : x ∈ Zs ⊔ W := by rw [hW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [LinearMap.domRestrict_apply, ← hpr, map_add, (hprZ z).2 ((hZs z).1 hz), zero_add]
  let e := LinearEquiv.ofBijective (pr.domRestrict W) ⟨hinj, hsurj⟩
  refine ⟨fun v => ((e.symm v : W) : D), fun v => ?_, fun v w => ?_⟩
  · rw [← hpr]
    change pr.domRestrict W (e.symm v) = v
    exact e.apply_symm_apply v
  · beta_reduce
    rw [map_add, Submodule.coe_add, hadd]

end Section

theorem section_cocycle_aux {P R A B z z' k : D} (hz : z ∈ center D) :
    P * R * k * ((A * B * k)⁻¹ * (A * z * (B * z'))) = P * z * (R * z') := by
  calc P * R * k * ((A * B * k)⁻¹ * (A * z * (B * z'))) = P * R * (B⁻¹ * (z * B)) * z' := by
        group
    _ = P * (z * R) * z' := by
        rw [← mem_center_iff.1 hz B, inv_mul_cancel_left, mul_assoc P R z,
          mem_center_iff.1 hz R]
    _ = P * z * (R * z') := by group

section Lift

open CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} [hp : Fact p.Prime] [Module (ZMod p) (Additive (Abelianization D))]
  (hZ : center D = commutator D) (ε : center D ≃* Multiplicative (ZMod p))

theorem exists_section_centerFixingAutSp (hp2 : p ≠ 2) (hexp : ∀ x : D, x ^ p = 1) :
    ∃ s : bilinIsometryGroup (centerCommForm hZ ε) →* centerFixingAut D,
      (centerFixingAutSp hZ ε).comp s = MonoidHom.id _ := by
  classical
  obtain ⟨σ, hσ1, hσ2⟩ := exists_baer_section hp2 hZ hexp
  have hc : ∀ x y : D, ⁅x, y⁆ ∈ center D :=
    CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ
  set β := centerCommForm hZ ε with hβ
  set h := (p - 1) / 2 with hh
  let vD : D → Additive (Abelianization D) := fun x => Additive.ofMul (Abelianization.of x)
  have hvD : ∀ x, vD x = Additive.ofMul (Abelianization.of x) := fun _ => rfl
  have hvDmul : ∀ x y, vD (x * y) = vD x + vD y := fun x y => by
    rw [hvD, hvD, hvD, map_mul, ofMul_mul]
  have hvDinv : ∀ x, vD x⁻¹ = -vD x := fun x => by rw [hvD, hvD, map_inv, ofMul_inv]
  have hvD0 : ∀ c, vD c = 0 ↔ c ∈ center D := fun c => by
    rw [hvD, ofMul_eq_zero, ← MonoidHom.mem_ker, Abelianization.ker_of, hZ]
  have hvDσ : ∀ w, vD (σ w) = w := hσ1
  let zD : D → D := fun x => (σ (vD x))⁻¹ * x
  have hzD : ∀ x, zD x = (σ (vD x))⁻¹ * x := fun _ => rfl
  have hzDc : ∀ x, zD x ∈ center D := fun x =>
    (hvD0 _).1 (by rw [hzD, hvDmul, hvDinv, hvDσ, neg_add_cancel])
  have hxz : ∀ x, σ (vD x) * zD x = x := fun x => mul_inv_cancel_left _ _
  have hvσc : ∀ w c, c ∈ center D → vD (σ w * c) = w := fun w c hc' => by
    rw [hvDmul, hvDσ, (hvD0 c).2 hc', add_zero]
  have hzσc : ∀ w c, c ∈ center D → zD (σ w * c) = c := fun w c hc' => by
    rw [hzD, hvσc w c hc', inv_mul_cancel_left]
  have hβσ : ∀ v w, β v w = Multiplicative.toAdd (ε ⟨⁅σ v, σ w⁆, hc _ _⟩) := fun v w => by
    conv_lhs => rw [← hvDσ v, ← hvDσ w]
    exact centerCommForm_apply hZ ε (σ v) (σ w)
  let app : bilinIsometryGroup β → Additive (Abelianization D) → Additive (Abelianization D) :=
    fun s v => ((s : LinearMap.GeneralLinearGroup (ZMod p) (Additive (Abelianization D))) :
      Additive (Abelianization D) →ₗ[ZMod p] Additive (Abelianization D)) v
  have happ_mul : ∀ s t v, app (s * t) v = app s (app t v) := fun _ _ _ => rfl
  have happ_one : ∀ v, app 1 v = v := fun _ => rfl
  have happ_add : ∀ s v w, app s (v + w) = app s v + app s w := fun s v w => map_add _ v w
  have happ_zero : ∀ s, app s 0 = 0 := fun s => map_zero _
  have hiso : ∀ s v w, ⁅σ (app s v), σ (app s w)⁆ = ⁅σ v, σ w⁆ := by
    intro s v w
    have h1 := (mem_bilinIsometryGroup.1 s.2) v w
    change β (app s v) (app s w) = β v w at h1
    rw [hβσ, hβσ] at h1
    exact congrArg Subtype.val (ε.injective (Multiplicative.toAdd.injective h1))
  let L : bilinIsometryGroup β → D → D := fun s x => σ (app s (vD x)) * zD x
  have hL : ∀ s x, L s x = σ (app s (vD x)) * zD x := fun _ _ => rfl
  have hvL : ∀ s x, vD (L s x) = app s (vD x) := fun s x => hvσc _ _ (hzDc x)
  have hzL : ∀ s x, zD (L s x) = zD x := fun s x => hzσc _ _ (hzDc x)
  have hLL : ∀ s t x, L s (L t x) = L (s * t) x := fun s t x => by
    rw [hL s, hvL, hzL, ← happ_mul]
  have hL1 : ∀ x, L 1 x = x := fun x => by rw [hL, happ_one]; exact hxz x
  have hLmul : ∀ s x y, L s (x * y) = L s x * L s y := by
    intro s x y
    have hxy : x * y = σ (vD x) * zD x * (σ (vD y) * zD y) := by rw [hxz, hxz]
    rw [hL, hL, hL, hzD (x * y), hvDmul x y, happ_add, hσ2, hσ2, hiso, hxy]
    exact section_cocycle_aux (hzDc x)
  have hLfix : ∀ s, ∀ z ∈ center D, L s z = z := fun s z hz => by
    rw [hL, hzD, (hvD0 z).2 hz, happ_zero, mul_inv_cancel_left]
  let Lequiv : bilinIsometryGroup β → MulAut D := fun s =>
    { toFun := L s
      invFun := L s⁻¹
      left_inv := fun x => by rw [hLL, inv_mul_cancel, hL1]
      right_inv := fun x => by rw [hLL, mul_inv_cancel, hL1]
      map_mul' := hLmul s }
  let sec : bilinIsometryGroup β →* centerFixingAut D :=
    { toFun := fun s => ⟨Lequiv s, fun z hz => hLfix s z hz⟩
      map_one' := Subtype.ext (MulEquiv.ext fun x => hL1 x)
      map_mul' := fun s t => Subtype.ext (MulEquiv.ext fun x => (hLL s t x).symm) }
  refine ⟨sec, MonoidHom.ext fun s => ?_⟩
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨x, rfl⟩ := exists_ofMul_of_eq v
  exact hvL s x

theorem ker_centerFixingAutSp [Finite D] :
    (centerFixingAutSp hZ ε).ker =
      (MulAut.conj : D →* MulAut D).range.subgroupOf (centerFixingAut D) := by
  classical
  have hc : ∀ x y : D, ⁅x, y⁆ ∈ center D :=
    CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ
  ext ⟨α, hα⟩
  rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · intro h1
    have htriv : ∀ x : D, Abelianization.of (α x) = Abelianization.of x := by
      intro x
      have h2 := congrArg (fun g : bilinIsometryGroup (centerCommForm hZ ε) =>
        ((g : LinearMap.GeneralLinearGroup (ZMod p) (Additive (Abelianization D))) :
          Additive (Abelianization D) →ₗ[ZMod p] Additive (Abelianization D))
          (Additive.ofMul (Abelianization.of x))) h1
      exact Additive.ofMul.injective h2
    have hf : ∀ x : D, x⁻¹ * α x ∈ center D := fun x => by
      rw [hZ, ← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, htriv,
        inv_mul_cancel]
    let f : D →* center D :=
      { toFun := fun x => ⟨x⁻¹ * α x, hf x⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          change (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
          rw [map_mul, mul_inv_rev]
          calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
            _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [mem_center_iff.1 (hf x) y⁻¹]
            _ = x⁻¹ * α x * (y⁻¹ * α y) := by group) }
    have hfval : ∀ x, (f x : D) = x⁻¹ * α x := fun _ => rfl
    let ℓ : Additive (Abelianization D) →ₗ[ZMod p] ZMod p :=
      (MonoidHom.toAdditiveLeft (ε.toMonoidHom.comp (Abelianization.lift f))).toZModLinearMap p
    have hℓ : ∀ x, ℓ (Additive.ofMul (Abelianization.of x)) = Multiplicative.toAdd (ε (f x)) :=
      fun x => rfl
    obtain ⟨-, hβn⟩ := centerCommForm_isAlt_nondegenerate hZ ε
    have : Finite (Additive (Abelianization D)) :=
      Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
        fun v => exists_ofMul_of_eq v
    have : FiniteDimensional (ZMod p) (Additive (Abelianization D)) := Module.Finite.of_finite
    set w := ((centerCommForm hZ ε).toDual hβn).symm ℓ with hwdef
    have hw : ∀ v, centerCommForm hZ ε w v = ℓ v := fun v => by
      rw [← LinearMap.BilinForm.toDual_def hβn, hwdef, LinearEquiv.apply_symm_apply]
    obtain ⟨u, hu⟩ := exists_ofMul_of_eq w
    refine ⟨u, MulEquiv.ext fun x => ?_⟩
    have h1 := hw (Additive.ofMul (Abelianization.of x))
    rw [← hu, centerCommForm_apply, hℓ] at h1
    have h2 : ⁅u, x⁆ = x⁻¹ * α x := by
      have h3 := ε.injective (Multiplicative.toAdd.injective h1)
      rw [← hfval]
      exact congrArg Subtype.val h3
    rw [MulAut.conj_apply]
    calc u * x * u⁻¹ = ⁅u, x⁆ * x := by rw [commutatorElement_def]; group
      _ = x⁻¹ * α x * x := by rw [h2]
      _ = α x := by rw [← mem_center_iff.1 (hf x) x, mul_inv_cancel_left]
  · rintro ⟨g, rfl⟩
    refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
    obtain ⟨x, rfl⟩ := exists_ofMul_of_eq v
    rw [centerFixingAutSp_apply, MulAut.conj_apply, map_mul Abelianization.of,
      map_mul Abelianization.of, map_inv Abelianization.of, mul_inv_cancel_comm]
    rfl

end Lift

section Main

open CFSG.LocalAnalysis.ComponentInitial

theorem odd_exponent_extraspecial_center_fixing_automorphism_split [Finite D] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hexp : ∀ x : D, x ^ p = 1)
    (hZ : center D = commutator D) (ε : center D ≃* Multiplicative (ZMod p))
    [Module (ZMod p) (Additive (Abelianization D))] :
    ((centerCommForm hZ ε).IsAlt ∧ (centerCommForm hZ ε).Nondegenerate) ∧
      Function.Surjective (centerFixingAutSp hZ ε) ∧
      (centerFixingAutSp hZ ε).ker =
        (MulAut.conj : D →* MulAut D).range.subgroupOf (centerFixingAut D) ∧
      (∃ s : bilinIsometryGroup (centerCommForm hZ ε) →* centerFixingAut D,
        (centerFixingAutSp hZ ε).comp s = MonoidHom.id _) ∧
      ∃ J : Subgroup (centerFixingAut D),
        ((MulAut.conj : D →* MulAut D).range.subgroupOf (centerFixingAut D)).Normal ∧
        (MulAut.conj : D →* MulAut D).range.subgroupOf (centerFixingAut D) ⊓ J = ⊥ ∧
        (MulAut.conj : D →* MulAut D).range.subgroupOf (centerFixingAut D) ⊔ J = ⊤ ∧
        Function.Bijective ((centerFixingAutSp hZ ε).domRestrict J) := by
  obtain ⟨s, hs⟩ := exists_section_centerFixingAutSp hZ ε hp2 hexp
  have hker := ker_centerFixingAutSp hZ ε
  have hsec : ∀ t, centerFixingAutSp hZ ε (s t) = t := fun t => DFunLike.congr_fun hs t
  refine ⟨centerCommForm_isAlt_nondegenerate hZ ε, fun t => ⟨s t, hsec t⟩, hker, ⟨s, hs⟩,
    s.range, ?_, ?_, ?_, ?_⟩
  · rw [← hker]
    infer_instance
  · rw [← hker, eq_bot_iff]
    rintro α ⟨hαker, t, rfl⟩
    have hαker' : s t ∈ (centerFixingAutSp hZ ε).ker := hαker
    rw [MonoidHom.mem_ker, hsec] at hαker'
    rw [hαker', map_one]
    exact one_mem _
  · rw [← hker, eq_top_iff]
    intro α _
    have h1 : α * (s (centerFixingAutSp hZ ε α))⁻¹ ∈ (centerFixingAutSp hZ ε).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsec, mul_inv_cancel]
    have h2 := mul_mem_sup h1
      (MonoidHom.mem_range.2 ⟨centerFixingAutSp hZ ε α, rfl⟩ :
        s (centerFixingAutSp hZ ε α) ∈ s.range)
    rwa [inv_mul_cancel_right] at h2
  · refine ⟨?_, fun t => ⟨⟨s t, t, rfl⟩, hsec t⟩⟩
    rw [injective_iff_map_eq_one]
    rintro ⟨α, t, rfl⟩ h
    rw [MonoidHom.domRestrict_apply, hsec] at h
    subst h
    exact Subtype.ext (map_one s)

end Main

end CFSG.RankThree.CentralExtension
