module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField

namespace CFSG
end CFSG
open CFSG

/-!
# Near-field coordinates for the sharp branch of Huppert--Blackburn XI.11.16

This file constructs the right near-field attached to the sharply triply
transitive branch. It contains only the coordinate construction; the missing
XI.2.6 classification of the resulting near-field is kept separate.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFAppendixII

universe u v

private structure SharpNearFieldCarrier (D : Type*) where
  val : WithZero D

private def sharpNearFieldCarrierEquiv (D : Type*) :
    SharpNearFieldCarrier D ≃ WithZero D where
  toFun := SharpNearFieldCarrier.val
  invFun := SharpNearFieldCarrier.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- A right near-field whose additive group comes from an elementary abelian
`p`-group has additive characteristic `p`. -/
public theorem rightNearField_addOrderOf_one_eq_of_isElementaryAbelian
    {p : ℕ} (hp : Nat.Prime p) {F K : Type*} [Group F]
    [IsElementaryAbelian p F] [RightNearField K]
    (e : Additive F ≃+ K) : addOrderOf (1 : K) = p := by
  let x : F := (e.symm (1 : K)).toMul
  have hxne : x ≠ 1 := by
    intro hx
    have hone_zero : e.symm (1 : K) = 0 := by
      apply Additive.toMul.injective
      exact hx
    have : (1 : K) = 0 := by
      calc
        (1 : K) = e (e.symm (1 : K)) := (e.apply_symm_apply 1).symm
        _ = e 0 := by rw [hone_zero]
        _ = 0 := e.map_zero
    exact one_ne_zero this
  have hxdvd : orderOf x ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p F) x
  have hxorder : orderOf x = p :=
    (hp.eq_one_or_self_of_dvd (orderOf x) hxdvd).resolve_left (by
      intro hxone
      exact hxne (orderOf_eq_one_iff.mp hxone))
  calc
    addOrderOf (1 : K) = addOrderOf (e.symm (1 : K)) :=
      (e.symm.addOrderOf_eq 1).symm
    _ = orderOf x := rfl
    _ = p := hxorder

set_option backward.isDefEq.respectTransparency false in
/-- Additive coordinates on the regular Frobenius kernel extend to coordinates
on the whole point set, with the fixed point represented by `none`. -/
public theorem huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
    {G Omega K : Type*} [Group G] [MulAction G Omega] [AddZeroClass K]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (eAdd : Additive F ≃+ K) :
    ∃ ePoint : Omega ≃ Option K,
      ePoint a = none ∧
        ePoint b = some 0 ∧
          ∀ f : F,
            ePoint (((f : MulAction.stabilizer G a) : G) • b) =
              some (eAdd (Additive.ofMul f)) := by
  classical
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  obtain ⟨kernelPointEquiv, hkernel_apply⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
      htwo a b hab F hFrob
  let kernelToK : F ≃ K :=
    Additive.ofMul.trans eAdd.toEquiv
  let affineEquiv : X ≃ K :=
    kernelPointEquiv.symm.trans kernelToK
  let pointEquiv : Omega ≃ Option K :=
    (Equiv.optionSubtypeNe a).symm.trans (Equiv.optionCongr affineEquiv)
  have hkernel_b : kernelPointEquiv.symm b' = 1 := by
    apply kernelPointEquiv.injective
    rw [kernelPointEquiv.apply_symm_apply, hkernel_apply]
    simp [b']
  refine ⟨pointEquiv, ?_, ?_, ?_⟩
  · simp [pointEquiv]
  · change (Equiv.optionCongr affineEquiv)
        ((Equiv.optionSubtypeNe a).symm b) = some 0
    rw [Equiv.optionSubtypeNe_symm_of_ne hab.symm]
    change some (affineEquiv b') = some 0
    congr 1
    change eAdd (Additive.ofMul (kernelPointEquiv.symm b')) = 0
    rw [hkernel_b]
    exact eAdd.map_zero
  · intro f
    change pointEquiv
        ((((f : MulAction.stabilizer G a) • b' : X) : Omega)) =
      some (eAdd (Additive.ofMul f))
    rw [← hkernel_apply f]
    change (Equiv.optionCongr affineEquiv)
        ((Equiv.optionSubtypeNe a).symm (kernelPointEquiv f : Omega)) =
      some (eAdd (Additive.ofMul f))
    rw [Equiv.optionSubtypeNe_symm_of_ne
      (SubMulAction.neq_of_mem_ofStabilizer G a)]
    change some (affineEquiv (kernelPointEquiv f)) =
      some (eAdd (Additive.ofMul f))
    congr 1
    change eAdd
        (Additive.ofMul (kernelPointEquiv.symm (kernelPointEquiv f))) =
      eAdd (Additive.ofMul f)
    rw [kernelPointEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- In projective near-field coordinates, sharp triple transitivity supplies
an involution interchanging infinity and zero while fixing one. -/
public theorem huppert_blackburn_XI_projectivePointEquiv_exists_normalized_swap
    {G Omega K : Type*} [Group G] [MulAction G Omega]
    [Zero K] [One K]
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (ePoint : Omega ≃ Option K)
    (hPointA : ePoint a = none)
    (hPointB : ePoint b = some 0)
    (hzero_one : (0 : K) ≠ 1) :
    ∃ t : G,
      t ≠ 1 ∧ t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
        t • ePoint.symm (some 1) = ePoint.symm (some 1) := by
  let c : Omega := ePoint.symm (some 1)
  have hPointC : ePoint c = some 1 := ePoint.apply_symm_apply (some 1)
  have hca : c ≠ a := by
    intro hca
    have h := congrArg ePoint hca
    rw [hPointC, hPointA] at h
    exact Option.some_ne_none 1 h
  have hcb : c ≠ b := by
    intro hcb
    have h := congrArg ePoint hcb
    rw [hPointC, hPointB] at h
    exact hzero_one (Option.some.inj h).symm
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  obtain ⟨t, ht, _ht_unique⟩ :=
    hsharp a b c b a c hab hac hbc hab.symm hbc hac
  rcases ht with ⟨hta, htb, htc⟩
  have htne : t ≠ 1 := by
    intro htone
    apply hab
    simpa [htone] using hta
  have ht_sq_maps :
      (t ^ 2) • a = a ∧ (t ^ 2) • b = b ∧ (t ^ 2) • c = c := by
    constructor
    · rw [pow_two, mul_smul, hta, htb]
    constructor
    · rw [pow_two, mul_smul, htb, hta]
    · rw [pow_two, mul_smul, htc, htc]
  have ht_sq : t ^ 2 = 1 :=
    ExistsUnique.unique
      (hsharp a b c a b c hab hac hbc hab hac hbc)
      ht_sq_maps (by simp)
  exact ⟨t, htne, ht_sq, hta, htb, htc⟩

set_option backward.isDefEq.respectTransparency false in
/-- In projective coordinates, the Frobenius kernel acts on the affine line by
translations and fixes infinity. -/
public theorem huppert_blackburn_XI_projectivePointEquiv_kernel_action
    {G Omega K : Type*} [Group G] [MulAction G Omega] [AddGroup K]
    (a b : Omega)
    (F : Subgroup (MulAction.stabilizer G a))
    (eAdd : Additive F ≃+ K)
    (ePoint : Omega ≃ Option K)
    (hPointA : ePoint a = none)
    (hPointF :
      ∀ f : F,
        ePoint (((f : MulAction.stabilizer G a) : G) • b) =
          some (eAdd (Additive.ofMul f))) :
    ∀ f : F, ∀ y : Option K,
      ePoint (((f : MulAction.stabilizer G a) : G) • ePoint.symm y) =
        Option.map (fun x => eAdd (Additive.ofMul f) + x) y := by
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  intro f y
  cases y with
  | none =>
      rw [hPointA_symm, (f : MulAction.stabilizer G a).property, hPointA]
      rfl
  | some x =>
      let r : F := (eAdd.symm x).toMul
      have hPointR :
          ePoint (((r : MulAction.stabilizer G a) : G) • b) = some x := by
        rw [hPointF]
        change some (eAdd (eAdd.symm x)) = some x
        rw [eAdd.apply_symm_apply]
      have hPointR_symm :
          ePoint.symm (some x) =
            (((r : MulAction.stabilizer G a) : G) • b) := by
        apply ePoint.injective
        rw [ePoint.apply_symm_apply, hPointR]
      rw [hPointR_symm, ← mul_smul]
      change
        ePoint (((((f * r : F) : MulAction.stabilizer G a)) : G) • b) =
          some (eAdd (Additive.ofMul f) + x)
      rw [hPointF]
      congr 1
      change eAdd (Additive.ofMul (f * r)) =
        eAdd (Additive.ofMul f) + x
      rw [show Additive.ofMul (f * r) =
          Additive.ofMul f + Additive.ofMul r from rfl, eAdd.map_add]
      change eAdd (Additive.ofMul f) + eAdd (eAdd.symm x) =
        eAdd (Additive.ofMul f) + x
      rw [eAdd.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- In projective coordinates, inverse action by the two-point stabilizer is
right multiplication on the affine line and fixes infinity. -/
public theorem huppert_blackburn_XI_projectivePointEquiv_twoPointStabilizer_action
    {G Omega K : Type*} [Group G] [MulAction G Omega]
    [AddGroup K] [GroupWithZero K]
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (eAdd : Additive F ≃+ K)
    (eUnits :
      MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) ≃* Kˣ)
    (hmul_coordinate :
      ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        ∀ x : K,
          (((eAdd.symm (x * (eUnits d : K))).toMul : F) :
              MulAction.stabilizer G a) =
            (d : MulAction.stabilizer G a)⁻¹ *
              (((eAdd.symm x).toMul : F) :
                MulAction.stabilizer G a) *
              (d : MulAction.stabilizer G a))
    (ePoint : Omega ≃ Option K)
    (hPointA : ePoint a = none)
    (hPointF :
      ∀ f : F,
        ePoint (((f : MulAction.stabilizer G a) : G) • b) =
          some (eAdd (Additive.ofMul f))) :
    ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      ∀ y : Option K,
        ePoint
            ((((d : MulAction.stabilizer G a) : G)⁻¹) •
              ePoint.symm y) =
          Option.map (fun x => x * (eUnits d : K)) y := by
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  intro d y
  have hdb : (((d : H) : G) • b) = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp d.property)
  cases y with
  | none =>
      rw [hPointA_symm]
      change ePoint (((((d : H)⁻¹ : H) : G)) • a) = none
      rw [((d : H)⁻¹).property, hPointA]
  | some x =>
      let r : F := (eAdd.symm x).toMul
      let s : F := (eAdd.symm (x * (eUnits d : K))).toMul
      have hPointR :
          ePoint (((r : H) : G) • b) = some x := by
        rw [hPointF]
        change some (eAdd (eAdd.symm x)) = some x
        rw [eAdd.apply_symm_apply]
      have hPointR_symm :
          ePoint.symm (some x) = (((r : H) : G) • b) := by
        apply ePoint.injective
        rw [ePoint.apply_symm_apply, hPointR]
      have hsH : (s : H) = (d : H)⁻¹ * (r : H) * (d : H) := by
        exact hmul_coordinate d x
      have hsG :
          ((s : H) : G) =
            (((d : H) : G)⁻¹) * ((r : H) : G) * ((d : H) : G) := by
        exact congrArg Subtype.val hsH
      have haction :
          (((d : H) : G)⁻¹) • (((r : H) : G) • b) =
            ((s : H) : G) • b := by
        calc
          (((d : H) : G)⁻¹) • (((r : H) : G) • b) =
              ((((d : H) : G)⁻¹) * ((r : H) : G)) • b :=
            (mul_smul _ _ _).symm
          _ = ((((d : H) : G)⁻¹) * ((r : H) : G)) •
              (((d : H) : G) • b) := by rw [hdb]
          _ = (((((d : H) : G)⁻¹) * ((r : H) : G)) *
              ((d : H) : G)) • b := (mul_smul _ _ _).symm
          _ = ((s : H) : G) • b := by rw [hsG]
      rw [hPointR_symm, haction, hPointF]
      change some (eAdd (eAdd.symm (x * (eUnits d : K)))) =
        some (x * (eUnits d : K))
      rw [eAdd.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The elementary abelian Frobenius kernel supplies addition, while regular
conjugation by the two-point stabilizer supplies the nonzero multiplication
of a right near-field. -/
public theorem huppert_blackburn_XI_sharpTriple_exists_rightNearField
    {G : Type u} {Omega : Type v} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F) :
    ∃ (K : Type u) (_ : RightNearField K) (_ : Finite K),
      ∃ eAdd : Additive F ≃+ K,
        ∃ eUnits :
            MulAction.stabilizer (MulAction.stabilizer G a)
                (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) ≃* Kˣ,
          ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
            ∀ x : K,
              (((eAdd.symm (x * (eUnits d : K))).toMul : F) :
                  MulAction.stabilizer G a) =
                (d : MulAction.stabilizer G a)⁻¹ *
                  (((eAdd.symm x).toMul : F) :
                    MulAction.stabilizer G a) *
                  (d : MulAction.stabilizer G a) := by
  classical
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  letI : F.Normal := hFrob.normal
  letI : IsMulCommutative F := hFcomm
  letI : CommGroup F := IsMulCommutative.instCommGroup
  rcases huppert_blackburn_XI_twoPointStabilizer_exists_conjEquiv
      htwo hsharp a b hab F hFrob with ⟨z, hz, e, he⟩
  let punctureEquiv : {x : F // x ≠ 1} ≃ {x : Additive F // x ≠ 0} :=
    { toFun := fun x => ⟨Additive.ofMul x.1, by simpa using x.2⟩
      invFun := fun x => ⟨x.1.toMul, by simpa using x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  let invEquiv : D ≃ D := Equiv.inv D
  let qEquiv : D ≃ {x : Additive F // x ≠ 0} :=
    (invEquiv.trans e).trans punctureEquiv
  have hqEquiv_apply (d : D) :
      (((qEquiv d).1.toMul : F) : H) =
        (d : H)⁻¹ * (z : H) * (d : H) := by
    simpa [qEquiv, invEquiv, punctureEquiv] using he d⁻¹
  let withZeroEquiv : WithZero D ≃ Additive F :=
    (Equiv.optionCongr qEquiv).trans (Equiv.optionSubtypeNe 0)
  have hwithZero_zero : withZeroEquiv 0 = 0 := by
    change (Equiv.optionSubtypeNe 0)
      ((Equiv.optionCongr qEquiv) (none : Option D)) = 0
    rw [Equiv.optionCongr_apply]
    rfl
  let K := SharpNearFieldCarrier D
  let mulCoord : K ≃ WithZero D := sharpNearFieldCarrierEquiv D
  let addCoord : K ≃ Additive F := mulCoord.trans withZeroEquiv
  letI : AddCommGroup K := addCoord.addCommGroup
  let addEquiv : Additive F ≃+ K := (addCoord.addEquiv).symm
  have hmulCoord_zero : mulCoord (0 : K) = 0 := by
    apply withZeroEquiv.injective
    change addCoord (0 : K) = withZeroEquiv 0
    rw [hwithZero_zero]
    exact (addCoord.addEquiv).map_zero
  letI : One K := mulCoord.one
  letI : Mul K := mulCoord.mul
  letI : Inv K := mulCoord.Inv
  letI : Div K := mulCoord.div
  letI : Pow K ℕ := mulCoord.pow ℕ
  letI : Pow K ℤ := mulCoord.pow ℤ
  letI : GroupWithZero K :=
    mulCoord.injective.groupWithZero mulCoord hmulCoord_zero
      (by simp [Equiv.one_def])
      (by intro x y; simp [Equiv.mul_def])
      (by intro x; simp [Equiv.inv_def])
      (by intro x y; simp [Equiv.div_def])
      (by intro x n; simp [Equiv.pow_def])
      (by intro x n; simp [Equiv.pow_def])
  let qPoint (d : D) : K := mulCoord.symm (d : WithZero D)
  have hmulCoord_q (d : D) : mulCoord (qPoint d) = (d : WithZero D) :=
    mulCoord.apply_symm_apply (d : WithZero D)
  have hwithZero_q (d : D) :
      withZeroEquiv (d : WithZero D) = (qEquiv d : Additive F) := by
    change (Equiv.optionSubtypeNe 0)
      ((Equiv.optionCongr qEquiv) (some d)) = (qEquiv d : Additive F)
    rw [Equiv.optionCongr_apply]
    rfl
  have haddEquiv_q (d : D) :
      addEquiv.symm (qPoint d) = (qEquiv d : Additive F) := by
    change addCoord (qPoint d) = (qEquiv d : Additive F)
    change withZeroEquiv (mulCoord (qPoint d)) = (qEquiv d : Additive F)
    rw [hmulCoord_q, hwithZero_q]
  have hqPoint_mul (r d : D) :
      qPoint r * qPoint d = qPoint (r * d) := by
    apply mulCoord.injective
    rw [Equiv.mul_def, hmulCoord_q, hmulCoord_q, hmulCoord_q]
    simp
  let conjAdd (d : D) : Additive F ≃+ Additive F :=
    MulEquiv.toAdditive (MulAut.conjNormal (H := F) (d : H)⁻¹)
  have hconjAdd_apply (d : D) (x : Additive F) :
      (((conjAdd d x).toMul : F) : H) =
        (d : H)⁻¹ * ((x.toMul : F) : H) * (d : H) := by
    simp [conjAdd, MulAut.conjNormal_symm_apply]
  have hqEquiv_conj (r d : D) :
      (qEquiv (r * d)).1 = conjAdd d (qEquiv r).1 := by
    change ((qEquiv (r * d)).1.toMul : F) =
      ((conjAdd d (qEquiv r).1).toMul : F)
    apply Subtype.ext
    calc
      (((qEquiv (r * d)).1.toMul : F) : H) =
          ((r * d : D) : H)⁻¹ * (z : H) * ((r * d : D) : H) :=
        hqEquiv_apply (r * d)
      _ = (d : H)⁻¹ *
          ((r : H)⁻¹ * (z : H) * (r : H)) * (d : H) := by
        change (((r : H) * (d : H))⁻¹) * (z : H) *
            ((r : H) * (d : H)) = _
        group
      _ = (d : H)⁻¹ *
          (((qEquiv r).1.toMul : F) : H) * (d : H) := by
        rw [hqEquiv_apply r]
      _ = (((conjAdd d (qEquiv r).1).toMul : F) : H) :=
        (hconjAdd_apply d (qEquiv r).1).symm
  have hmul_right (x : K) (d : D) :
      x * qPoint d = addEquiv (conjAdd d (addEquiv.symm x)) := by
    by_cases hx : x = 0
    · subst x
      simp
    · have hxcoord : addEquiv.symm x ≠ 0 := by
        intro hzero
        apply hx
        apply addEquiv.symm.injective
        simpa using hzero
      let r : D := qEquiv.symm ⟨addEquiv.symm x, hxcoord⟩
      have hx_eq : x = qPoint r := by
        apply addEquiv.symm.injective
        rw [haddEquiv_q]
        exact congrArg Subtype.val
          (qEquiv.apply_symm_apply ⟨addEquiv.symm x, hxcoord⟩).symm
      rw [hx_eq, hqPoint_mul]
      apply addEquiv.symm.injective
      rw [haddEquiv_q, addEquiv.symm_apply_apply, haddEquiv_q]
      exact hqEquiv_conj r d
  let hNF : RightNearField K :=
    { (inferInstance : AddCommGroup K),
      (inferInstance : GroupWithZero K) with
      right_distrib := by
        intro x y c
        by_cases hc : c = 0
        · simp [hc]
        · have hccoord : addEquiv.symm c ≠ 0 := by
            intro hzero
            apply hc
            apply addEquiv.symm.injective
            simpa using hzero
          let d : D := qEquiv.symm ⟨addEquiv.symm c, hccoord⟩
          have hc_eq : c = qPoint d := by
            apply addEquiv.symm.injective
            rw [haddEquiv_q]
            exact congrArg Subtype.val
              (qEquiv.apply_symm_apply ⟨addEquiv.symm c, hccoord⟩).symm
          rw [hc_eq, hmul_right, hmul_right, hmul_right]
          apply addEquiv.symm.injective
          rw [addEquiv.symm_apply_apply]
          calc
            conjAdd d (addEquiv.symm (x + y)) =
                conjAdd d (addEquiv.symm x + addEquiv.symm y) := by
              rw [addEquiv.symm.map_add]
            _ = conjAdd d (addEquiv.symm x) +
                conjAdd d (addEquiv.symm y) :=
              (conjAdd d).map_add (addEquiv.symm x) (addEquiv.symm y)
            _ = addEquiv.symm
                (addEquiv (conjAdd d (addEquiv.symm x)) +
                  addEquiv (conjAdd d (addEquiv.symm y))) := by
              rw [addEquiv.symm.map_add, addEquiv.symm_apply_apply,
                addEquiv.symm_apply_apply] }
  letI : RightNearField K := hNF
  let hKfinite : Finite K :=
    Finite.of_injective addEquiv.symm addEquiv.symm.injective
  let mulEquiv : K ≃* WithZero D := mulCoord.mulEquiv
  let unitCoord : Kˣ ≃* D :=
    (Units.mapEquiv mulEquiv).trans WithZero.unitsWithZeroEquiv
  have hunitCoord_symm_apply (d : D) :
      ((unitCoord.symm d : Kˣ) : K) = qPoint d := by
    apply mulCoord.injective
    rw [hmulCoord_q]
    simp [unitCoord, mulEquiv]
  have hmul_coordinate (d : D) (x : K) :
      (((addEquiv.symm (x * (unitCoord.symm d : K))).toMul : F) : H) =
        (d : H)⁻¹ * (((addEquiv.symm x).toMul : F) : H) * (d : H) := by
    rw [hunitCoord_symm_apply, hmul_right, addEquiv.symm_apply_apply]
    exact hconjAdd_apply d (addEquiv.symm x)
  exact ⟨K, hNF, hKfinite, addEquiv, unitCoord.symm, hmul_coordinate⟩

end External
end CFSG.BenderSuzuki
