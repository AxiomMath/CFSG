module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.SubgroupRectangular

namespace CFSG
end CFSG
open CFSG

/-!
# The abelian core in Hering's theorem

This file formalizes Peterfalvi's direct proof of the abelian case in
Chapter IV, Section 3 of *Le théorème de Bender--Suzuki, I*.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII
open scoped Pointwise IsMulCommutative

universe u

/-- The fixed coordinate model for the order-eight elementary abelian layer
in Peterfalvi's proof. -/
public abbrev II1Hering31AbelianV :=
  Multiplicative (Fin 3 → ZMod 2)

/-- Peterfalvi's first coordinate transvection on the elementary abelian
layer, before passing to multiplicative notation. -/
private def ii1Hering31AbelianSLin :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun x := ![x 0, x 1 + x 2, x 2]
  map_add' x y := by
    ext i
    fin_cases i
    · simp
    · simp
      abel
    · simp
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_add]

private theorem ii1Hering31AbelianSLin_involutive :
    Function.Involutive ii1Hering31AbelianSLin := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  intro x
  ext i
  fin_cases i
  · simp [ii1Hering31AbelianSLin]
  · simp [ii1Hering31AbelianSLin]
    ring_nf
    simp [htwo]
  · simp [ii1Hering31AbelianSLin]

/-- Peterfalvi's second coordinate transvection on the elementary abelian
layer, before passing to multiplicative notation. -/
private def ii1Hering31AbelianTLin :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun x := ![x 0 + x 1 + x 2, x 1, x 2]
  map_add' x y := by
    ext i
    fin_cases i
    · simp
      ring
    · simp
    · simp
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mul_add]

private theorem ii1Hering31AbelianTLin_involutive :
    Function.Involutive ii1Hering31AbelianTLin := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  intro x
  ext i
  fin_cases i
  · simp [ii1Hering31AbelianTLin]
    ring_nf
    simp [htwo]
  · simp [ii1Hering31AbelianTLin]
  · simp [ii1Hering31AbelianTLin]

/-- The first explicit involution in Peterfalvi IV.3, step 3. -/
private noncomputable def ii1Hering31AbelianS :
    MulAut II1Hering31AbelianV :=
  AddEquiv.toMultiplicative
    (LinearEquiv.ofInvolutive ii1Hering31AbelianSLin
      ii1Hering31AbelianSLin_involutive).toAddEquiv

/-- The second explicit involution in Peterfalvi IV.3, step 3. -/
private noncomputable def ii1Hering31AbelianT :
    MulAut II1Hering31AbelianV :=
  AddEquiv.toMultiplicative
    (LinearEquiv.ofInvolutive ii1Hering31AbelianTLin
      ii1Hering31AbelianTLin_involutive).toAddEquiv

private def ii1Hering31AbelianV1 : II1Hering31AbelianV :=
  Multiplicative.ofAdd ![(1 : ZMod 2), 0, 0]

private def ii1Hering31AbelianV2 : II1Hering31AbelianV :=
  Multiplicative.ofAdd ![(0 : ZMod 2), 1, 0]

private def ii1Hering31AbelianV3 : II1Hering31AbelianV :=
  Multiplicative.ofAdd ![(0 : ZMod 2), 0, 1]

@[simp] private theorem ii1Hering31AbelianS_v1 :
    ii1Hering31AbelianS ii1Hering31AbelianV1 =
      ii1Hering31AbelianV1 := by
  decide

@[simp] private theorem ii1Hering31AbelianS_v2 :
    ii1Hering31AbelianS ii1Hering31AbelianV2 =
      ii1Hering31AbelianV2 := by
  decide

@[simp] private theorem ii1Hering31AbelianS_v3 :
    ii1Hering31AbelianS ii1Hering31AbelianV3 =
      ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by
  decide

@[simp] private theorem ii1Hering31AbelianT_v1 :
    ii1Hering31AbelianT ii1Hering31AbelianV1 =
      ii1Hering31AbelianV1 := by
  decide

@[simp] private theorem ii1Hering31AbelianT_v2 :
    ii1Hering31AbelianT ii1Hering31AbelianV2 =
      ii1Hering31AbelianV1 * ii1Hering31AbelianV2 := by
  decide

@[simp] private theorem ii1Hering31AbelianT_v3 :
    ii1Hering31AbelianT ii1Hering31AbelianV3 =
      ii1Hering31AbelianV1 * ii1Hering31AbelianV3 := by
  decide

private theorem ii1Hering31AbelianS_sq :
    ii1Hering31AbelianS ^ 2 = 1 := by
  apply DFunLike.ext _ _
  intro v
  change ii1Hering31AbelianS (ii1Hering31AbelianS v) = v
  exact congrArg Multiplicative.ofAdd
    (ii1Hering31AbelianSLin_involutive v.toAdd)

private theorem ii1Hering31AbelianT_sq :
    ii1Hering31AbelianT ^ 2 = 1 := by
  apply DFunLike.ext _ _
  intro v
  change ii1Hering31AbelianT (ii1Hering31AbelianT v) = v
  exact congrArg Multiplicative.ofAdd
    (ii1Hering31AbelianTLin_involutive v.toAdd)

private theorem ii1Hering31AbelianS_ne_one :
    ii1Hering31AbelianS ≠ 1 := by
  intro h
  have hv := DFunLike.congr_fun h ii1Hering31AbelianV3
  have hne : ii1Hering31AbelianV2 * ii1Hering31AbelianV3 ≠
      ii1Hering31AbelianV3 := by
    decide
  apply hne
  calc
    ii1Hering31AbelianV2 * ii1Hering31AbelianV3 =
        ii1Hering31AbelianS ii1Hering31AbelianV3 := by simp
    _ = ii1Hering31AbelianV3 := hv

private theorem ii1Hering31AbelianT_ne_one :
    ii1Hering31AbelianT ≠ 1 := by
  intro h
  have hv := DFunLike.congr_fun h ii1Hering31AbelianV2
  have hne : ii1Hering31AbelianV1 * ii1Hering31AbelianV2 ≠
      ii1Hering31AbelianV2 := by
    decide
  apply hne
  calc
    ii1Hering31AbelianV1 * ii1Hering31AbelianV2 =
        ii1Hering31AbelianT ii1Hering31AbelianV2 := by simp
    _ = ii1Hering31AbelianV2 := hv

private theorem ii1Hering31AbelianS_fixed_cases
    (v : II1Hering31AbelianV) (hfix : ii1Hering31AbelianS v = v)
    (hne : v ≠ 1) :
    v = ii1Hering31AbelianV1 ∨
      v = ii1Hering31AbelianV2 ∨
      v = ii1Hering31AbelianV1 * ii1Hering31AbelianV2 := by
  revert hfix hne
  decide +revert

/-- The coordinate action induced by `a = s * t` with the left-conjugation
convention used by the extension data.  It is the inverse of Peterfalvi's
displayed right-action matrix and has the same fixed points. -/
private noncomputable def ii1Hering31AbelianA :
    MulAut II1Hering31AbelianV :=
  ii1Hering31AbelianS * ii1Hering31AbelianT

/-- The coordinate action induced by `b = a²`; this agrees with
Peterfalvi's displayed matrix for `b`. -/
private noncomputable def ii1Hering31AbelianB :
    MulAut II1Hering31AbelianV :=
  ii1Hering31AbelianA ^ 2

@[simp] private theorem ii1Hering31AbelianB_v1 :
    ii1Hering31AbelianB ii1Hering31AbelianV1 =
      ii1Hering31AbelianV1 := by
  decide

@[simp] private theorem ii1Hering31AbelianB_v2 :
    ii1Hering31AbelianB ii1Hering31AbelianV2 =
      ii1Hering31AbelianV2 := by
  decide

@[simp] private theorem ii1Hering31AbelianB_v3 :
    ii1Hering31AbelianB ii1Hering31AbelianV3 =
      ii1Hering31AbelianV1 * ii1Hering31AbelianV3 := by
  decide

private theorem ii1Hering31AbelianB_sq :
    ii1Hering31AbelianB ^ 2 = 1 := by
  apply DFunLike.ext _ _
  intro v
  revert v
  decide +revert

private theorem ii1Hering31AbelianB_ne_one :
    ii1Hering31AbelianB ≠ 1 := by
  intro h
  have hv := DFunLike.congr_fun h ii1Hering31AbelianV3
  have hne : ii1Hering31AbelianV1 * ii1Hering31AbelianV3 ≠
      ii1Hering31AbelianV3 := by
    decide
  apply hne
  calc
    ii1Hering31AbelianV1 * ii1Hering31AbelianV3 =
        ii1Hering31AbelianB ii1Hering31AbelianV3 := by simp
    _ = ii1Hering31AbelianV3 := hv

private theorem ii1Hering31AbelianA_fixed_nonzero_eq_v1
    (v : II1Hering31AbelianV) (hfix : ii1Hering31AbelianA v = v)
    (hne : v ≠ 1) : v = ii1Hering31AbelianV1 := by
  revert hfix hne
  decide +revert

private theorem ii1Hering31AbelianST_fixed_nonzero_eq_v1
    (v : II1Hering31AbelianV)
    (hS : ii1Hering31AbelianS v = v)
    (hT : ii1Hering31AbelianT v = v) (hne : v ≠ 1) :
    v = ii1Hering31AbelianV1 := by
  revert hS hT hne
  decide +revert

/-- A fixed involutory coordinate permutation used in the elementary-kernel
base case of Peterfalvi's induction. -/
private noncomputable def ii1Hering31AbelianSwap :
    MulAut II1Hering31AbelianV :=
  AddEquiv.toMultiplicative
    (LinearEquiv.piCongrLeft (ZMod 2) (fun _ : Fin 3 => ZMod 2)
      (Equiv.swap 0 1)).toAddEquiv

private theorem ii1Hering31AbelianSwap_sq :
    ii1Hering31AbelianSwap ^ 2 = 1 := by
  apply DFunLike.ext _ _
  intro v
  ext i
  fin_cases i <;>
    simp [pow_two, ii1Hering31AbelianSwap, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', Equiv.swap_apply_def]

private theorem ii1Hering31AbelianSwap_ne_one :
    ii1Hering31AbelianSwap ≠ 1 := by
  intro h
  have hv := DFunLike.congr_fun h
    (Multiplicative.ofAdd ![(1 : ZMod 2), 0, 0])
  have hv0 := congrFun (congrArg Multiplicative.toAdd hv) 0
  norm_num [ii1Hering31AbelianSwap, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft', Equiv.swap_apply_def] at hv0

/-- Transport automorphisms across a multiplicative equivalence. -/
@[expose] public noncomputable def ii1Hering31AbelianTransportAut
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    MulAut A →* MulAut B where
  toFun alpha := e.symm.trans (alpha.trans e)
  map_one' := by
    apply DFunLike.ext _ _
    intro b
    simp
  map_mul' := by
    intro alpha beta
    apply DFunLike.ext _ _
    intro b
    simp

/-- A multiplicative equivalence transports the kernel of squaring. -/
public noncomputable def ii1Hering31AbelianTwoTorsionEquiv
    {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    (powMonoidHom 2 : A →* A).ker ≃*
      (powMonoidHom 2 : B →* B).ker where
  toFun a := ⟨e a, by simpa using congrArg e a.property⟩
  invFun b := ⟨e.symm b, by simpa using congrArg e.symm b.property⟩
  left_inv a := by apply Subtype.ext; exact e.symm_apply_apply a
  right_inv b := by apply Subtype.ext; exact e.apply_symm_apply b
  map_mul' a b := by apply Subtype.ext; exact map_mul e a.1 b.1

/-- Conjugation on a normal elementary abelian layer, written in the fixed
three-dimensional `F₂` coordinate model. -/
@[expose] public noncomputable def ii1Hering31AbelianCoordinateAction
    {X : Type u} [Group X]
    (V : Subgroup X) (hV : V.Normal)
    (coord : V ≃* II1Hering31AbelianV) :
    X →* MulAut II1Hering31AbelianV := by
  letI : V.Normal := hV
  exact (ii1Hering31AbelianTransportAut coord).comp
    (MulAut.conjNormal (H := V))

public theorem ii1Hering31AbelianCoordinateAction_apply
    {X : Type u} [Group X]
    (V : Subgroup X) (hV : V.Normal)
    (coord : V ≃* II1Hering31AbelianV)
    (x : X) (v : V) :
    ii1Hering31AbelianCoordinateAction V hV coord x (coord v) =
      coord ⟨x * (v : X) * x⁻¹, by
        exact hV.conj_mem (v : X) v.property x⟩ := by
  letI : V.Normal := hV
  dsimp [ii1Hering31AbelianCoordinateAction,
    ii1Hering31AbelianTransportAut]
  rw [coord.symm_apply_apply]
  exact congrArg coord (Subtype.ext rfl)

/-- The exact abstract data used by Peterfalvi's abelian extension argument.
The two-torsion subgroup `V` is canonical inside `Q`, ambient conjugation on
`V` realizes all of `GL(3,2)`, and `Q` is precisely the kernel of that action.
The final field records the single conjugacy class of quotient involutions in
a form stable under quotienting by `V`. -/
public structure II1Hering31AbelianExtensionData
    (X : Type u) [Group X] [Finite X] where
  Q : Subgroup X
  V : Subgroup X
  Q_normal : Q.Normal
  V_normal : V.Normal
  Q_commutative : IsMulCommutative Q
  Q_isPGroup : IsPGroup 2 Q
  V_le_Q : V ≤ Q
  V_twoTorsion : ∀ q : Q, (q : X) ∈ V ↔ q ^ 2 = 1
  V_coord : V ≃* II1Hering31AbelianV
  V_action_transitive : ∀ v w : V, v ≠ 1 → w ≠ 1 →
    ∃ x : X, x * (v : X) * x⁻¹ = (w : X)
  action : X →* MulAut II1Hering31AbelianV
  action_on_V : ∀ x : X, ∀ v : V,
    action x (V_coord v) = V_coord ⟨x * (v : X) * x⁻¹, by
      exact V_normal.conj_mem (v : X) v.property x⟩
  action_surjective : Function.Surjective action
  action_ker : action.ker = Q
  quotient_involutions_conjugate :
    ∀ {x y : X}, x ∉ Q → x ^ 2 ∈ Q → y ∉ Q → y ^ 2 ∈ Q →
      ∃ g : X, g⁻¹ * x * g * y⁻¹ ∈ Q

/-- The canonical two-torsion layer in Peterfalvi's data has cardinality
eight. -/
public theorem II1Hering31AbelianExtensionData.V_card
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) : Nat.card d.V = 8 := by
  calc
    Nat.card d.V = Nat.card II1Hering31AbelianV :=
      Nat.card_congr d.V_coord.toEquiv
    _ = 8 := by
      rw [Nat.card_eq_fintype_card]
      norm_num [II1Hering31AbelianV, ZMod.card]

/-- The two-torsion of `Q` is exactly the distinguished order-eight layer. -/
public theorem II1Hering31AbelianExtensionData.Q_twoTorsion_card
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) :
    Nat.card {q : d.Q // q ^ 2 = 1} = 8 := by
  let e : {q : d.Q // q ^ 2 = 1} ≃ d.V :=
    { toFun := fun q => ⟨(q.1 : X), (d.V_twoTorsion q.1).2 q.2⟩
      invFun := fun v => ⟨⟨(v : X), d.V_le_Q v.property⟩,
        (d.V_twoTorsion ⟨(v : X), d.V_le_Q v.property⟩).1 v.property⟩
      left_inv := by intro q; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro v; apply Subtype.ext; rfl }
  calc
    Nat.card {q : d.Q // q ^ 2 = 1} = Nat.card d.V := Nat.card_congr e
    _ = 8 := d.V_card

/-- The abelian kernel in Peterfalvi's data is homocyclic of rank three. -/
public theorem II1Hering31AbelianExtensionData.Q_homocyclic
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) :
    ∃ e : ℕ, 0 < e ∧ Nonempty
      (d.Q ≃* Multiplicative (Fin 3 → ZMod (2 ^ e))) := by
  letI : d.Q.Normal := d.Q_normal
  letI : MulDistribMulAction X d.Q :=
    MulDistribMulAction.compHom d.Q (MulAut.conjNormal (H := d.Q))
  have htrans : ∀ q : d.Q, q ∈ involutions d.Q →
      ∀ r : d.Q, r ∈ involutions d.Q → ∃ x : X, r = x • q := by
    intro q hq r hr
    let qV : d.V := ⟨(q : X), (d.V_twoTorsion q).2 hq.sq_eq_one⟩
    let rV : d.V := ⟨(r : X), (d.V_twoTorsion r).2 hr.sq_eq_one⟩
    have hqV : qV ≠ 1 := by
      intro h
      apply hq.ne_one
      apply Subtype.ext
      simpa [qV] using congrArg d.V.subtype h
    have hrV : rV ≠ 1 := by
      intro h
      apply hr.ne_one
      apply Subtype.ext
      simpa [rV] using congrArg d.V.subtype h
    obtain ⟨x, hx⟩ := d.V_action_transitive qV rV hqV hrV
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx.symm
  obtain ⟨e, r, he, ⟨f⟩⟩ :=
    External.Higman.homocyclic_of_abelian_twoGroup_of_involutions_transitive
      d.Q_isPGroup d.Q_commutative htrans
  have hpow : 2 ^ r = 8 := by
    rw [← External.Higman.lemma1_twoTorsion_card_of_homocyclic he f]
    exact d.Q_twoTorsion_card
  have hr : r = 3 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    calc
      2 ^ r = 8 := hpow
      _ = 2 ^ 3 := by norm_num
  subst r
  exact ⟨e, he, ⟨f⟩⟩

/-- Inside `Q`, the distinguished subgroup `V` is exactly the kernel of
squaring. -/
public theorem II1Hering31AbelianExtensionData.V_subgroupOf_eq_sq_ker
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) :
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    d.V.subgroupOf d.Q = (powMonoidHom 2 : d.Q →* d.Q).ker := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  ext q
  exact d.V_twoTorsion q

/-- Exponent two forces the whole homocyclic kernel to be its distinguished
two-torsion layer. -/
public theorem II1Hering31AbelianExtensionData.Q_eq_V_of_homocyclic_one
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (f : d.Q ≃* Multiplicative (Fin 3 → ZMod (2 ^ 1))) : d.Q = d.V := by
  have hQcard : Nat.card d.Q = 8 := by
    calc
      Nat.card d.Q =
          Nat.card (Multiplicative (Fin 3 → ZMod (2 ^ 1))) :=
        Nat.card_congr f.toEquiv
      _ = 8 := by
        rw [Nat.card_eq_fintype_card]
        norm_num [ZMod.card]
  exact (Subgroup.eq_of_le_of_card_ge d.V_le_Q (by
    rw [d.V_card, hQcard])).symm

/-- Above exponent two, every element of `V` has a square root in `Q`. -/
public theorem II1Hering31AbelianExtensionData.exists_square_root_of_mem_V
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    {e : ℕ} (he : 0 < e)
    (f : d.Q ≃* Multiplicative (Fin 3 → ZMod (2 ^ e)))
    (hQV : d.Q ≠ d.V) (v : d.V) :
    ∃ q : d.Q, q ^ 2 = ⟨(v : X), d.V_le_Q v.property⟩ := by
  have heTwo : 2 ≤ e := by
    by_contra h
    have heOne : e = 1 := by omega
    subst e
    exact hQV (d.Q_eq_V_of_homocyclic_one f)
  let vQ : d.Q := ⟨(v : X), d.V_le_Q v.property⟩
  have hvQ2 : vQ ^ 2 = 1 := (d.V_twoTorsion vQ).1 v.property
  have hvPow : vQ ^ (2 ^ (e - 1)) = 1 := by
    rw [show 2 ^ (e - 1) = 2 * 2 ^ (e - 2) by
      calc
        2 ^ (e - 1) = 2 ^ ((e - 2) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 2) := by simp [pow_succ, Nat.mul_comm]]
    rw [pow_mul, hvQ2, one_pow]
  obtain ⟨q, hq⟩ :=
    External.Higman.lemma1_exists_power_root_of_homocyclic
      (e := e) (f := e - 1) (Nat.sub_le e 1) f hvPow
  refine ⟨q, ?_⟩
  simpa [show e - (e - 1) = 1 by omega] using hq

/-- Squaring identifies the two-torsion of `Q / V` with `V` itself.  This is
the equivariant layer shift used in Peterfalvi step 2. -/
public noncomputable def
    II1Hering31AbelianExtensionData.quotientTwoTorsionEquiv
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    {e : ℕ} (he : 0 < e)
    (f : d.Q ≃* Multiplicative (Fin 3 → ZMod (2 ^ e)))
    (hQV : d.Q ≠ d.V) :
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let VQ : Subgroup d.Q := d.V.subgroupOf d.Q
    (powMonoidHom 2 : (d.Q ⧸ VQ) →* (d.Q ⧸ VQ)).ker ≃* d.V := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let VQ : Subgroup d.Q := d.V.subgroupOf d.Q
  let sq : d.Q →* d.Q := powMonoidHom 2
  have hVQker : VQ = sq.ker := by
    simpa [VQ, sq] using d.V_subgroupOf_eq_sq_ker
  let eSq : d.Q ⧸ VQ ≃* sq.range :=
    (QuotientGroup.quotientMulEquivOfEq hVQker).trans
      (QuotientGroup.quotientKerEquivRange sq)
  let W : Subgroup (d.Q ⧸ VQ) :=
    (powMonoidHom 2 : (d.Q ⧸ VQ) →* (d.Q ⧸ VQ)).ker
  let toV : W →* d.V :=
    { toFun := fun w =>
        ⟨(((eSq w : sq.range) : d.Q) : X), (d.V_twoTorsion
          ((eSq w : sq.range) : d.Q)).2 (by
            have hwSq : (eSq (w ^ 2) : sq.range) = eSq 1 :=
              congrArg eSq w.property
            have hwSq' : (eSq w : sq.range) ^ 2 = 1 := by
              simpa using hwSq
            exact congrArg Subtype.val hwSq')⟩
      map_one' := by
        apply Subtype.ext
        simp [eSq]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [eSq] }
  change W ≃* d.V
  refine MulEquiv.ofBijective toV ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply eSq.injective
    apply Subtype.ext
    apply d.Q.subtype_injective
    exact congrArg d.V.subtype hab
  · intro v
    obtain ⟨q, hq⟩ := d.exists_square_root_of_mem_V he f hQV v
    let w0 : d.Q ⧸ VQ := QuotientGroup.mk' VQ q
    have hw0 : w0 ^ 2 = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff (N := VQ) (q ^ 2)).2
      change ((q ^ 2 : d.Q) : X) ∈ d.V
      rw [hq]
      exact v.property
    let w : W := ⟨w0, hw0⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change (((eSq w : sq.range) : d.Q) : X) = (v : X)
    have heSq : eSq w =
        QuotientGroup.quotientKerEquivRange sq (QuotientGroup.mk q) := by
      simp [eSq, w, w0]
    rw [heSq]
    change ((sq q : d.Q) : X) = (v : X)
    simpa [sq] using congrArg d.Q.subtype hq

/-- Quotienting a non-elementary abelian extension by its canonical
two-torsion layer produces another extension of the same kind.  The new
coordinates are obtained by squaring representatives in `Q / V`. -/
public noncomputable def II1Hering31AbelianExtensionData.quotient
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) (hQV : d.Q ≠ d.V) :
    letI : d.V.Normal := d.V_normal
    II1Hering31AbelianExtensionData (X ⧸ d.V) := by
  classical
  letI : d.V.Normal := d.V_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let qX : X →* X ⧸ d.V := QuotientGroup.mk' d.V
  let qQ : d.Q →* X ⧸ d.V := qX.comp d.Q.subtype
  let Qbar : Subgroup (X ⧸ d.V) := qQ.range
  have hker : qQ.ker = d.V.subgroupOf d.Q := by
    ext q
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' d.V (q : X) = 1 ↔ (q : X) ∈ d.V
    exact QuotientGroup.eq_one_iff (N := d.V) (q : X)
  let eQ : d.Q ⧸ d.V.subgroupOf d.Q ≃* Qbar :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange qQ)
  have hQbarNormal : Qbar.Normal := by
    have hQbarMap : Qbar = d.Q.map qX := by
      ext z
      simp [Qbar, qQ]
    rw [hQbarMap]
    exact d.Q_normal.map qX (QuotientGroup.mk'_surjective d.V)
  have hQbarComm : IsMulCommutative Qbar := by
    refine ⟨⟨fun a b => ?_⟩⟩
    rcases a.property with ⟨a0, ha0⟩
    rcases b.property with ⟨b0, hb0⟩
    apply Subtype.ext
    change (a : X ⧸ d.V) * (b : X ⧸ d.V) =
      (b : X ⧸ d.V) * (a : X ⧸ d.V)
    rw [← ha0, ← hb0]
    exact congrArg qQ (mul_comm a0 b0)
  letI : IsMulCommutative Qbar := hQbarComm
  letI : CommGroup Qbar := IsMulCommutative.instCommGroup
  have hQbarP : IsPGroup 2 Qbar :=
    (d.Q_isPGroup.to_quotient (d.V.subgroupOf d.Q)).of_equiv eQ
  let Wbar : Subgroup Qbar := (powMonoidHom 2 : Qbar →* Qbar).ker
  let Vbar : Subgroup (X ⧸ d.V) := Wbar.map Qbar.subtype
  letI : Qbar.Normal := hQbarNormal
  letI : Wbar.Characteristic := by
    simpa [Wbar] using
      Wielandt.powMonoidHom_ker_characteristic (H := Qbar) 2
  have hVbarNormal : Vbar.Normal := by
    simpa [Vbar] using
      (ConjAct.normal_of_characteristic_of_normal (H := Qbar) (K := Wbar))
  have hVbarLe : Vbar ≤ Qbar := by
    intro x hx
    rcases hx with ⟨w, _hw, rfl⟩
    exact w.property
  have hVbarTorsion : ∀ q : Qbar,
      (q : X ⧸ d.V) ∈ Vbar ↔ q ^ 2 = 1 := by
    intro q
    constructor
    · intro hq
      rcases hq with ⟨w, hw, hqw⟩
      have hEq : w = q := Qbar.subtype_injective hqw
      simpa [Wbar, hEq] using hw
    · intro hq
      exact Subgroup.mem_map.mpr ⟨q, by simpa [Wbar] using hq, rfl⟩
  let e : ℕ := Classical.choose d.Q_homocyclic
  have he : 0 < e := (Classical.choose_spec d.Q_homocyclic).1
  let f : d.Q ≃* Multiplicative (Fin 3 → ZMod (2 ^ e)) :=
    Classical.choice (Classical.choose_spec d.Q_homocyclic).2
  let eOld := d.quotientTwoTorsionEquiv he f hQV
  let eTors : Wbar ≃*
      (powMonoidHom 2 :
        (d.Q ⧸ d.V.subgroupOf d.Q) →*
          (d.Q ⧸ d.V.subgroupOf d.Q)).ker :=
    ii1Hering31AbelianTwoTorsionEquiv eQ.symm
  let eMap : Wbar ≃* Vbar :=
    Wbar.equivMapOfInjective Qbar.subtype Qbar.subtype_injective
  let coord : Vbar ≃* II1Hering31AbelianV :=
    eMap.symm.trans (eTors.trans (eOld.trans d.V_coord))
  have hVactionKer : d.V ≤ d.action.ker := by
    rw [d.action_ker]
    exact d.V_le_Q
  let actionBar : (X ⧸ d.V) →* MulAut II1Hering31AbelianV :=
    QuotientGroup.lift d.V d.action hVactionKer
  have hEQ (q : d.Q) :
      eQ (QuotientGroup.mk' (d.V.subgroupOf d.Q) q) =
        ⟨qQ q, ⟨q, rfl⟩⟩ := by
    apply Qbar.subtype_injective
    simp [eQ, qQ, qX]
    rfl
  have hOldVal (w : Wbar) (q : d.Q)
      (hqw : (w.1 : X ⧸ d.V) = qQ q) :
      ((eOld (eTors w) : d.V) : X) = ((q ^ 2 : d.Q) : X) := by
    have heQsymm : eQ.symm w.1 =
        QuotientGroup.mk' (d.V.subgroupOf d.Q) q := by
      apply eQ.injective
      rw [eQ.apply_symm_apply]
      rw [hEQ]
      exact Subtype.ext hqw
    change ((d.quotientTwoTorsionEquiv he f hQV
      (ii1Hering31AbelianTwoTorsionEquiv eQ.symm w) : d.V) : X) = _
    simp [ii1Hering31AbelianTwoTorsionEquiv, heQsymm,
      II1Hering31AbelianExtensionData.quotientTwoTorsionEquiv]
    rfl
  have hCoordMap (w : Wbar) :
      coord (eMap w) = d.V_coord (eOld (eTors w)) := by
    simp [coord]
  have hActionOn : ∀ x : X ⧸ d.V, ∀ v : Vbar,
      actionBar x (coord v) = coord ⟨x * (v : X ⧸ d.V) * x⁻¹, by
        exact hVbarNormal.conj_mem (v : X ⧸ d.V) v.property x⟩ := by
    intro xbar v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.V xbar
    rw [show actionBar (qX x) = d.action x by
      exact QuotientGroup.lift_mk' d.V hVactionKer x]
    let w : Wbar := eMap.symm v
    have hv : eMap w = v := eMap.apply_symm_apply v
    rw [← hv]
    rcases w.1.property with ⟨q, hq⟩
    let qConj : d.Q :=
      ⟨x * (q : X) * x⁻¹,
        d.Q_normal.conj_mem (q : X) q.property x⟩
    let wConjQ : Qbar :=
      ⟨qX x * (w.1 : X ⧸ d.V) * (qX x)⁻¹,
        hQbarNormal.conj_mem (w.1 : X ⧸ d.V) w.1.property (qX x)⟩
    have hwConjQ2 : wConjQ ^ 2 = 1 := by
      apply Qbar.subtype_injective
      change (qX x * (w.1 : X ⧸ d.V) * (qX x)⁻¹) ^ 2 = 1
      have hw2Q : w.1 ^ 2 = 1 := by
        have hwKer := MonoidHom.mem_ker.mp w.property
        simpa [powMonoidHom_apply] using hwKer
      have hw2 : (w.1 : X ⧸ d.V) ^ 2 = 1 := by
        exact congrArg Qbar.subtype hw2Q
      rw [pow_two]
      calc
        (qX x * (w.1 : X ⧸ d.V) * (qX x)⁻¹) *
            (qX x * (w.1 : X ⧸ d.V) * (qX x)⁻¹) =
            qX x * ((w.1 : X ⧸ d.V) ^ 2) * (qX x)⁻¹ := by
              simp only [pow_two]
              group
        _ = 1 := by rw [hw2]; simp
    let wConj : Wbar := ⟨wConjQ, by simpa [Wbar] using hwConjQ2⟩
    have hqConj : (wConj.1 : X ⧸ d.V) = qQ qConj := by
      change qX x * (w.1 : X ⧸ d.V) * (qX x)⁻¹ =
        qX (x * (q : X) * x⁻¹)
      rw [← hq]
      simp [qQ]
    have hConjMap :
        (⟨qX x * ((eMap w : Vbar) : X ⧸ d.V) * (qX x)⁻¹, by
          exact hVbarNormal.conj_mem
            ((eMap w : Vbar) : X ⧸ d.V) (eMap w).property (qX x)⟩ : Vbar) =
          eMap wConj := by
      apply Vbar.subtype_injective
      change qX x * ((eMap w : Vbar) : X ⧸ d.V) * (qX x)⁻¹ =
        ((eMap wConj : Vbar) : X ⧸ d.V)
      rw [Subgroup.coe_equivMapOfInjective_apply]
      rw [Subgroup.coe_equivMapOfInjective_apply]
      rfl
    rw [hConjMap]
    rw [hCoordMap w, hCoordMap wConj]
    rw [d.action_on_V]
    apply congrArg d.V_coord
    apply d.V.subtype_injective
    change x * ((eOld (eTors w) : d.V) : X) * x⁻¹ =
      ((eOld (eTors wConj) : d.V) : X)
    rw [hOldVal w q hq.symm, hOldVal wConj qConj hqConj]
    simp [qConj, pow_two]
  have hActionSurjective : Function.Surjective actionBar := by
    exact QuotientGroup.lift_surjective_of_surjective
      d.V d.action d.action_surjective hVactionKer
  have hActionKer : actionBar.ker = Qbar := by
    rw [show actionBar.ker = Subgroup.map qX d.action.ker by
      simpa [actionBar, qX] using
        QuotientGroup.ker_lift d.V d.action hVactionKer]
    rw [d.action_ker]
    ext z
    simp [Qbar, qQ]
  have hTrans : ∀ v w : Vbar, v ≠ 1 → w ≠ 1 →
      ∃ x : X ⧸ d.V, x * (v : X ⧸ d.V) * x⁻¹ = (w : X ⧸ d.V) := by
    intro v w hv hw
    let vOld : d.V := d.V_coord.symm (coord v)
    let wOld : d.V := d.V_coord.symm (coord w)
    have hvOld : vOld ≠ 1 := by
      intro hvOld
      apply hv
      apply coord.injective
      simpa [vOld] using congrArg d.V_coord hvOld
    have hwOld : wOld ≠ 1 := by
      intro hwOld
      apply hw
      apply coord.injective
      simpa [wOld] using congrArg d.V_coord hwOld
    obtain ⟨x, hx⟩ := d.V_action_transitive vOld wOld hvOld hwOld
    refine ⟨qX x, ?_⟩
    let z : Vbar := ⟨qX x * (v : X ⧸ d.V) * (qX x)⁻¹, by
      exact hVbarNormal.conj_mem (v : X ⧸ d.V) v.property (qX x)⟩
    have hz : z = w := by
      apply coord.injective
      calc
        coord z =
          actionBar (qX x) (coord v) := (hActionOn (qX x) v).symm
        _ = d.action x (coord v) := by
          exact congrArg (fun a => a (coord v))
            (QuotientGroup.lift_mk' d.V hVactionKer x)
        _ = d.action x (d.V_coord vOld) := by simp [vOld]
        _ = d.V_coord ⟨x * (vOld : X) * x⁻¹, by
            exact d.V_normal.conj_mem (vOld : X) vOld.property x⟩ :=
          d.action_on_V x vOld
        _ = d.V_coord wOld := by
          congr 1
          exact Subtype.ext hx
        _ = coord w := by simp [wOld]
    exact congrArg Vbar.subtype hz
  have hQbarPreimage : ∀ x : X, qX x ∈ Qbar ↔ x ∈ d.Q := by
    intro x
    constructor
    · intro hx
      rcases hx with ⟨q, hq⟩
      have hqxV : (q : X) / x ∈ d.V :=
        (QuotientGroup.eq_iff_div_mem).1 hq
      have hqxQ : (q : X) / x ∈ d.Q := d.V_le_Q hqxV
      have hxEq : x = ((q : X) / x)⁻¹ * (q : X) := by
        simp [div_eq_mul_inv]
      rw [hxEq]
      exact d.Q.mul_mem (d.Q.inv_mem hqxQ) q.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hQuotientInvolutions :
      ∀ {x y : X ⧸ d.V}, x ∉ Qbar → x ^ 2 ∈ Qbar →
        y ∉ Qbar → y ^ 2 ∈ Qbar →
        ∃ g : X ⧸ d.V, g⁻¹ * x * g * y⁻¹ ∈ Qbar := by
    intro x y hxQ hx2 hyQ hy2
    obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective d.V x
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective d.V y
    have hx0Q : x0 ∉ d.Q := by
      intro hx0
      exact hxQ ((hQbarPreimage x0).2 hx0)
    have hx02 : x0 ^ 2 ∈ d.Q := by
      change (qX x0) ^ 2 ∈ Qbar at hx2
      exact (hQbarPreimage (x0 ^ 2)).1 (by simpa only [map_pow] using hx2)
    have hy0Q : y0 ∉ d.Q := by
      intro hy0
      exact hyQ ((hQbarPreimage y0).2 hy0)
    have hy02 : y0 ^ 2 ∈ d.Q := by
      change (qX y0) ^ 2 ∈ Qbar at hy2
      exact (hQbarPreimage (y0 ^ 2)).1 (by simpa only [map_pow] using hy2)
    obtain ⟨g, hg⟩ :=
      d.quotient_involutions_conjugate hx0Q hx02 hy0Q hy02
    refine ⟨qX g, ?_⟩
    exact (hQbarPreimage (g⁻¹ * x0 * g * y0⁻¹)).2 hg
  exact
    { Q := Qbar
      V := Vbar
      Q_normal := hQbarNormal
      V_normal := hVbarNormal
      Q_commutative := hQbarComm
      Q_isPGroup := hQbarP
      V_le_Q := hVbarLe
      V_twoTorsion := hVbarTorsion
      V_coord := coord
      V_action_transitive := hTrans
      action := actionBar
      action_on_V := hActionOn
      action_surjective := hActionSurjective
      action_ker := hActionKer
      quotient_involutions_conjugate := hQuotientInvolutions }

/-- The kernel subgroup in the descended extension is the image of `Q`. -/
public theorem II1Hering31AbelianExtensionData.quotient_Q
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) (hQV : d.Q ≠ d.V) :
    letI : d.V.Normal := d.V_normal
    (d.quotient hQV).Q =
      ((QuotientGroup.mk' d.V).comp d.Q.subtype).range := by
  rfl

/-- Membership in the descended kernel can be checked on representatives. -/
public theorem II1Hering31AbelianExtensionData.mem_quotient_Q_mk_iff
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) (hQV : d.Q ≠ d.V) (x : X) :
    letI : d.V.Normal := d.V_normal
    QuotientGroup.mk' d.V x ∈ (d.quotient hQV).Q ↔ x ∈ d.Q := by
  letI : d.V.Normal := d.V_normal
  rw [d.quotient_Q hQV]
  constructor
  · rintro ⟨q, hq⟩
    have hqxV : (q : X) / x ∈ d.V :=
      (QuotientGroup.eq_iff_div_mem).1 hq
    have hqxQ : (q : X) / x ∈ d.Q := d.V_le_Q hqxV
    have hxEq : x = ((q : X) / x)⁻¹ * (q : X) := by
      simp [div_eq_mul_inv]
    rw [hxEq]
    exact d.Q.mul_mem (d.Q.inv_mem hqxQ) q.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Peterfalvi IV.3, step 2, induction core. Assuming the proposition for
all smaller ambient extensions, the hypothesis that every involution of `X`
lies in `Q` yields a lift outside `Q` whose square is a nonidentity element of
the canonical layer `V`. -/
public theorem
    II1Hering31AbelianExtensionData.exists_lift_square_mem_V_ne_one_of_induction
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (ih : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ∀ dY : II1Hering31AbelianExtensionData Y,
        ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q) :
    ∃ x : X, x ∉ d.Q ∧ x ^ 2 ∈ d.V ∧ x ^ 2 ≠ 1 := by
  classical
  by_cases hQV : d.Q = d.V
  · obtain ⟨x, hxAction⟩ := d.action_surjective ii1Hering31AbelianSwap
    have hxQ : x ∉ d.Q := by
      intro hxQ
      apply ii1Hering31AbelianSwap_ne_one
      rw [← hxAction]
      exact MonoidHom.mem_ker.mp (by simpa [d.action_ker] using hxQ)
    have hx2Q : x ^ 2 ∈ d.Q := by
      rw [← d.action_ker, MonoidHom.mem_ker, map_pow, hxAction,
        ii1Hering31AbelianSwap_sq]
    have hx2V : x ^ 2 ∈ d.V := by simpa [← hQV] using hx2Q
    have hx2ne : x ^ 2 ≠ 1 := by
      intro hx2
      have hxne : x ≠ 1 := by
        intro hx
        apply hxQ
        rw [hx]
        exact d.Q.one_mem
      exact hxQ (hall x ⟨hxne, hx2⟩)
    exact ⟨x, hxQ, hx2V, hx2ne⟩
  · letI : d.V.Normal := d.V_normal
    let dbar : II1Hering31AbelianExtensionData (X ⧸ d.V) := d.quotient hQV
    have hVneBot : d.V ≠ ⊥ := by
      intro hV
      have hcard := d.V_card
      rw [hV] at hcard
      norm_num at hcard
    have hcardLt : Nat.card (X ⧸ d.V) < Nat.card X :=
      natCard_quotient_lt_natCard_of_ne_bot d.V hVneBot
    obtain ⟨y, hyInv, hyQ⟩ := ih hcardLt dbar
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.V y
    have hxQ : x ∉ d.Q := by
      intro hx
      exact hyQ ((d.mem_quotient_Q_mk_iff hQV x).2 hx)
    have hx2V : x ^ 2 ∈ d.V := by
      apply (QuotientGroup.eq_one_iff (N := d.V) (x ^ 2)).1
      simpa using hyInv.sq_eq_one
    have hx2ne : x ^ 2 ≠ 1 := by
      intro hx2
      have hxne : x ≠ 1 := by
        intro hx
        apply hxQ
        rw [hx]
        exact d.Q.one_mem
      exact hxQ (hall x ⟨hxne, hx2⟩)
    exact ⟨x, hxQ, hx2V, hx2ne⟩

/-- Peterfalvi IV.3, step 2, normalized form. Any lift of a quotient
involution can be adjusted on the right by an element of `Q` so that its
square is a nonidentity element of `V`. -/
public theorem
    II1Hering31AbelianExtensionData.exists_adjustment_square_mem_V_ne_one_of_induction
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (ih : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ∀ dY : II1Hering31AbelianExtensionData Y,
        ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q)
    {x : X} (hxQ : x ∉ d.Q) (hx2Q : x ^ 2 ∈ d.Q) :
    ∃ c : d.Q,
      (x * (c : X)) ^ 2 ∈ d.V ∧ (x * (c : X)) ^ 2 ≠ 1 := by
  obtain ⟨y, hyQ, hy2V, hy2ne⟩ :=
    d.exists_lift_square_mem_V_ne_one_of_induction hall ih
  obtain ⟨g, hg⟩ := d.quotient_involutions_conjugate
    hxQ hx2Q hyQ (d.V_le_Q hy2V)
  let r : d.Q := ⟨g⁻¹ * x * g * y⁻¹, hg⟩
  let e : d.Q := ⟨y⁻¹ * (r : X)⁻¹ * y,
    by simpa using
      d.Q_normal.conj_mem (r : X)⁻¹ (d.Q.inv_mem r.property) y⁻¹⟩
  let c : d.Q := ⟨g * (e : X) * g⁻¹,
    d.Q_normal.conj_mem (e : X) e.property g⟩
  refine ⟨c, ?_, ?_⟩
  · have hxc : x * (c : X) = g * y * g⁻¹ := by
      simp [c, e, r]
      group
    rw [hxc]
    have hy2Conj : g * y ^ 2 * g⁻¹ ∈ d.V :=
      d.V_normal.conj_mem (y ^ 2) hy2V g
    simpa [pow_two] using hy2Conj
  · intro hxc2
    apply hy2ne
    have hxc : x * (c : X) = g * y * g⁻¹ := by
      simp [c, e, r]
      group
    calc
      y ^ 2 = g⁻¹ * (x * (c : X)) ^ 2 * g := by
        rw [hxc]
        simp only [pow_two]
        group
      _ = 1 := by rw [hxc2]; simp

/-- The norm map `q |-> alpha(q) * q` for an automorphism of an abelian
group.  This is Peterfalvi's endomorphism `alpha + 1`. -/
public def ii1Hering31AbelianNorm
    {Q : Type*} [CommGroup Q] (alpha : MulAut Q) : Q →* Q where
  toFun q := alpha q * q
  map_one' := by simp
  map_mul' := by
    intro q r
    simp only [map_mul]
    ac_rfl

/-- Peterfalvi IV.3, step 1: if every ambient involution belongs to the
abelian normal subgroup `Q`, then the square of a lift of a quotient
involution is not in the corresponding norm image. -/
public theorem ii1Hering31_square_not_mem_abelianNorm
    {X : Type*} [Group X]
    (Q : Subgroup X) [Q.Normal]
    (hQcomm : IsMulCommutative Q)
    (hall : ∀ y : X, IsInvolution y → y ∈ Q)
    {x : X} (hxQ : x ∉ Q) (hx2 : x ^ 2 ∈ Q) :
    letI : IsMulCommutative Q := hQcomm
    letI : CommGroup Q := IsMulCommutative.instCommGroup
    ⟨x ^ 2, hx2⟩ ∉
      (ii1Hering31AbelianNorm (MulAut.conjNormal (H := Q) x)).range := by
  letI : IsMulCommutative Q := hQcomm
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  let alpha : MulAut Q := MulAut.conjNormal (H := Q) x
  intro hsquare
  rcases hsquare with ⟨q, hq⟩
  have hqX := congrArg Q.subtype hq
  have hqX' : (((alpha q * q : Q) : X)) = x ^ 2 := by
    simpa [ii1Hering31AbelianNorm, alpha] using hqX
  have hnormInvX :
      (q : X)⁻¹ * (x * (q : X)⁻¹ * x⁻¹) = (x ^ 2)⁻¹ := by
    calc
      (q : X)⁻¹ * (x * (q : X)⁻¹ * x⁻¹) =
          ((q⁻¹ * (alpha q)⁻¹ : Q) : X) := by
            simp [alpha, MulAut.conjNormal_apply, mul_assoc]
      _ = (((alpha q * q)⁻¹ : Q) : X) := by
        congr 1
        simp [mul_comm]
      _ = (x ^ 2)⁻¹ := by
        simpa using congrArg Inv.inv hqX'
  let y : X := (q : X)⁻¹ * x
  have hy2 : y ^ 2 = 1 := by
    calc
      y ^ 2 = ((q : X)⁻¹ * (x * (q : X)⁻¹ * x⁻¹)) * x ^ 2 := by
        simp [y, pow_two]
        group
      _ = 1 := by rw [hnormInvX]; simp
  have hyNe : y ≠ 1 := by
    intro hy
    apply hxQ
    have hx : x = (q : X) := by
      dsimp [y] at hy
      calc
        x = 1 * x := by simp
        _ = ((q : X) * (q : X)⁻¹) * x := by simp
        _ = (q : X) * ((q : X)⁻¹ * x) := by group
        _ = (q : X) := by rw [hy]; simp
    rw [hx]
    exact q.property
  have hyQ : y ∈ Q := hall y ⟨hyNe, hy2⟩
  apply hxQ
  have hx : x = (q : X) * y := by simp [y]
  rw [hx]
  exact Q.mul_mem q.property hyQ

/-- Peterfalvi IV.3, step 3.  A lift of the first explicit transvection can
be chosen with square exactly the first basis involution. -/
private theorem
    II1Hering31AbelianExtensionData.exists_normalized_S_lift_of_induction
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (ih : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ∀ dY : II1Hering31AbelianExtensionData Y,
        ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q) :
    ∃ s : X, s ∉ d.Q ∧ d.action s = ii1Hering31AbelianS ∧
      s ^ 2 = (d.V_coord.symm ii1Hering31AbelianV1 : d.V) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  obtain ⟨s0, hs0Action⟩ := d.action_surjective ii1Hering31AbelianS
  have hs0Q : s0 ∉ d.Q := by
    intro hs0Q
    apply ii1Hering31AbelianS_ne_one
    rw [← hs0Action]
    exact MonoidHom.mem_ker.mp (by simpa [d.action_ker] using hs0Q)
  have hs02Q : s0 ^ 2 ∈ d.Q := by
    rw [← d.action_ker, MonoidHom.mem_ker, map_pow, hs0Action,
      ii1Hering31AbelianS_sq]
  obtain ⟨c, hsc2V, hsc2ne⟩ :=
    d.exists_adjustment_square_mem_V_ne_one_of_induction
      hall ih hs0Q hs02Q
  let s : X := s0 * (c : X)
  have hsAction : d.action s = ii1Hering31AbelianS := by
    rw [show s = s0 * (c : X) by rfl, map_mul, hs0Action]
    have hcKer : (c : X) ∈ d.action.ker := by
      rw [d.action_ker]
      exact c.property
    rw [MonoidHom.mem_ker.mp hcKer, mul_one]
  have hsQ : s ∉ d.Q := by
    intro hsQ
    have hsOne : d.action s = 1 :=
      MonoidHom.mem_ker.mp (by simpa [d.action_ker] using hsQ)
    exact ii1Hering31AbelianS_ne_one (hsAction.symm.trans hsOne)
  let v : d.V := ⟨s ^ 2, hsc2V⟩
  have hvne : d.V_coord v ≠ 1 := by
    intro hv
    have hvOne : v = 1 := d.V_coord.injective (by simpa using hv)
    apply hsc2ne
    simpa [v] using congrArg d.V.subtype hvOne
  have hvFix : ii1Hering31AbelianS (d.V_coord v) = d.V_coord v := by
    rw [← hsAction]
    rw [d.action_on_V]
    apply congrArg d.V_coord
    apply Subtype.ext
    simp [v, pow_two]
    group
  have hvNotV2 : d.V_coord v ≠ ii1Hering31AbelianV2 := by
    intro hv2
    have hnotNorm := ii1Hering31_square_not_mem_abelianNorm
      d.Q d.Q_commutative hall hsQ (d.V_le_Q hsc2V)
    apply hnotNorm
    let qV : d.V := d.V_coord.symm ii1Hering31AbelianV3
    let qQ : d.Q := ⟨(qV : X), d.V_le_Q qV.property⟩
    let conjV : d.V := ⟨s * (qV : X) * s⁻¹,
      d.V_normal.conj_mem (qV : X) qV.property s⟩
    have hconjV : d.V_coord conjV =
        ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by
      calc
        d.V_coord conjV = d.action s (d.V_coord qV) :=
          (d.action_on_V s qV).symm
        _ = ii1Hering31AbelianS ii1Hering31AbelianV3 := by
          simp [hsAction, qV]
        _ = ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by simp
    let normV : d.V := conjV * qV
    have hnormV : d.V_coord normV = ii1Hering31AbelianV2 := by
      rw [map_mul, hconjV]
      simp [qV]
      decide
    refine ⟨qQ, ?_⟩
    apply d.Q.subtype_injective
    change ((normV : d.V) : X) = s ^ 2
    have hnormEq : normV = v :=
      d.V_coord.injective (hnormV.trans hv2.symm)
    simpa [v] using congrArg d.V.subtype hnormEq
  rcases ii1Hering31AbelianS_fixed_cases (d.V_coord v) hvFix hvne with
    hv1 | hv2 | hv12
  · refine ⟨s, hsQ, hsAction, ?_⟩
    have hvEq : v = d.V_coord.symm ii1Hering31AbelianV1 :=
      d.V_coord.injective
        (hv1.trans
          (d.V_coord.apply_symm_apply ii1Hering31AbelianV1).symm)
    simpa [v] using congrArg d.V.subtype hvEq
  · exact (hvNotV2 hv2).elim
  · let qV : d.V := d.V_coord.symm ii1Hering31AbelianV3
    let s' : X := s * (qV : X)
    have hs'Action : d.action s' = ii1Hering31AbelianS := by
      rw [show s' = s * (qV : X) by rfl, map_mul, hsAction]
      have hqKer : (qV : X) ∈ d.action.ker := by
        rw [d.action_ker]
        exact d.V_le_Q qV.property
      rw [MonoidHom.mem_ker.mp hqKer, mul_one]
    let conjV : d.V := ⟨s * (qV : X) * s⁻¹,
      d.V_normal.conj_mem (qV : X) qV.property s⟩
    have hconjV : d.V_coord conjV =
        ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by
      calc
        d.V_coord conjV = d.action s (d.V_coord qV) :=
          (d.action_on_V s qV).symm
        _ = ii1Hering31AbelianS ii1Hering31AbelianV3 := by
          simp [hsAction, qV]
        _ = ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by simp
    let squareV : d.V := conjV * v * qV
    have hsquareV : d.V_coord squareV = ii1Hering31AbelianV1 := by
      rw [map_mul, map_mul, hconjV, hv12]
      simp [qV]
      decide
    have hs'2Square : s' ^ 2 = (squareV : X) := by
      simp [s', squareV, conjV, v, pow_two]
      group
    refine ⟨s', ?_, hs'Action, ?_⟩
    · intro hs'Q
      have hs'One : d.action s' = 1 :=
        MonoidHom.mem_ker.mp (by simpa [d.action_ker] using hs'Q)
      exact ii1Hering31AbelianS_ne_one (hs'Action.symm.trans hs'One)
    · rw [hs'2Square]
      have hsquareEq : squareV =
          d.V_coord.symm ii1Hering31AbelianV1 :=
        d.V_coord.injective
          (hsquareV.trans
            (d.V_coord.apply_symm_apply ii1Hering31AbelianV1).symm)
      exact congrArg d.V.subtype hsquareEq

private theorem ii1Hering31Abelian_basis_relation_dvd_two
    (n1 n2 n3 : ℕ)
    (h : ii1Hering31AbelianV1 ^ n1 * ii1Hering31AbelianV2 ^ n2 *
      ii1Hering31AbelianV3 ^ n3 = 1) :
    2 ∣ n1 ∧ 2 ∣ n2 ∧ 2 ∣ n3 := by
  have h0 := congrFun (congrArg Multiplicative.toAdd h) 0
  have h1 := congrFun (congrArg Multiplicative.toAdd h) 1
  have h2 := congrFun (congrArg Multiplicative.toAdd h) 2
  constructor
  · rw [← ZMod.natCast_eq_zero_iff n1 2]
    simpa [ii1Hering31AbelianV1, ii1Hering31AbelianV2,
      ii1Hering31AbelianV3, ← ofAdd_nsmul] using h0
  constructor
  · rw [← ZMod.natCast_eq_zero_iff n2 2]
    simpa [ii1Hering31AbelianV1, ii1Hering31AbelianV2,
      ii1Hering31AbelianV3, ← ofAdd_nsmul] using h1
  · rw [← ZMod.natCast_eq_zero_iff n3 2]
    simpa [ii1Hering31AbelianV1, ii1Hering31AbelianV2,
      ii1Hering31AbelianV3, ← ofAdd_nsmul] using h2

private theorem II1Hering31AbelianExtensionData.layer_coordinates_unique
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (m : ℕ) (hm : 0 < m) (c1 c2 c3 : d.Q)
    (h1 : c1 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩)
    (h2 : c2 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (h3 : c3 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    {n1 n2 n3 : ℕ} (hn1 : n1 < 2 ^ m) (hn2 : n2 < 2 ^ m)
    (hn3 : n3 < 2 ^ m) (hrel : c1 ^ n1 * c2 ^ n2 * c3 ^ n3 = 1) :
    n1 = 0 ∧ n2 = 0 ∧ n3 = 0 := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  have hdiv : ∀ l ≤ m,
      2 ^ l ∣ n1 ∧ 2 ^ l ∣ n2 ∧ 2 ^ l ∣ n3 := by
    intro l hl
    induction l with
    | zero => simp
    | succ l ih =>
        have hlm : l < m := by omega
        obtain ⟨hd1, hd2, hd3⟩ := ih (by omega)
        obtain ⟨k1, hk1⟩ := hd1
        obtain ⟨k2, hk2⟩ := hd2
        obtain ⟨k3, hk3⟩ := hd3
        have hexp : 2 ^ l * 2 ^ (m - l - 1) = 2 ^ (m - 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hpow (c : d.Q) (k : ℕ) :
            (c ^ (2 ^ l * k)) ^ 2 ^ (m - l - 1) =
              (c ^ 2 ^ (m - 1)) ^ k := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          calc
            2 ^ l * k * 2 ^ (m - l - 1) =
                (2 ^ l * 2 ^ (m - l - 1)) * k := by ac_rfl
            _ = 2 ^ (m - 1) * k := by rw [hexp]
        have htopRel :
            (c1 ^ 2 ^ (m - 1)) ^ k1 *
                (c2 ^ 2 ^ (m - 1)) ^ k2 *
                (c3 ^ 2 ^ (m - 1)) ^ k3 = 1 := by
          rw [← hpow c1 k1, ← hpow c2 k2, ← hpow c3 k3]
          rw [← hk1, ← hk2, ← hk3]
          rw [← mul_pow]
          rw [← mul_pow]
          rw [hrel, one_pow]
        rw [h1, h2, h3] at htopRel
        let v1 : d.V := d.V_coord.symm ii1Hering31AbelianV1
        let v2 : d.V := d.V_coord.symm ii1Hering31AbelianV2
        let v3 : d.V := d.V_coord.symm ii1Hering31AbelianV3
        have hvRel : v1 ^ k1 * v2 ^ k2 * v3 ^ k3 = 1 := by
          apply d.V.subtype_injective
          simpa [v1, v2, v3] using congrArg d.Q.subtype htopRel
        have hcoordRel : ii1Hering31AbelianV1 ^ k1 *
            ii1Hering31AbelianV2 ^ k2 * ii1Hering31AbelianV3 ^ k3 = 1 := by
          simpa [v1, v2, v3] using congrArg d.V_coord hvRel
        obtain ⟨he1, he2, he3⟩ :=
          ii1Hering31Abelian_basis_relation_dvd_two k1 k2 k3 hcoordRel
        obtain ⟨r1, hr1⟩ := he1
        obtain ⟨r2, hr2⟩ := he2
        obtain ⟨r3, hr3⟩ := he3
        constructor
        · refine ⟨r1, ?_⟩
          rw [hk1, hr1, pow_succ]
          ac_rfl
        constructor
        · refine ⟨r2, ?_⟩
          rw [hk2, hr2, pow_succ]
          ac_rfl
        · refine ⟨r3, ?_⟩
          rw [hk3, hr3, pow_succ]
          ac_rfl
  obtain ⟨hd1, hd2, hd3⟩ := hdiv m le_rfl
  exact ⟨Nat.eq_zero_of_dvd_of_lt hd1 hn1,
    Nat.eq_zero_of_dvd_of_lt hd2 hn2,
    Nat.eq_zero_of_dvd_of_lt hd3 hn3⟩

private def ii1Hering31IntPowerHom {Q : Type*} [Group Q] (c : Q) :
    ℤ →+ Additive Q where
  toFun i := Additive.ofMul (c ^ i)
  map_zero' := by simp
  map_add' i j := Additive.toMul.injective (zpow_add c i j)

private noncomputable def ii1Hering31ZModPowerHom
    {Q : Type*} [Group Q] (n : ℕ) (c : Q) (hc : c ^ n = 1) :
    ZMod n →+ Additive Q :=
  ZMod.lift n ⟨ii1Hering31IntPowerHom c, by
    change c ^ (n : ℤ) = 1
    simpa using hc⟩

private noncomputable def ii1Hering31CyclicZModHom
    {Q : Type*} [Group Q] (n : ℕ) (c : Q) (hc : c ^ n = 1) :
    Multiplicative (ZMod n) →* Q :=
  (MulEquiv.multiplicativeAdditive Q).toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (ii1Hering31ZModPowerHom n c hc))

private theorem ii1Hering31ZModPowerHom_one
    {Q : Type*} [Group Q] (n : ℕ) (c : Q) (hc : c ^ n = 1) :
    ii1Hering31ZModPowerHom n c hc (1 : ZMod n) = Additive.ofMul c := by
  rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by norm_num]
  rw [ii1Hering31ZModPowerHom, ZMod.lift_coe]
  change Additive.ofMul (c ^ (1 : ℤ)) = Additive.ofMul c
  simp

private theorem ii1Hering31CyclicZModHom_apply
    {Q : Type*} [Group Q] (n : ℕ) [NeZero n]
    (c : Q) (hc : c ^ n = 1) (z : ZMod n) :
    ii1Hering31CyclicZModHom n c hc (Multiplicative.ofAdd z) =
      c ^ z.val := by
  have hz : z = ((z.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val z).symm
  have hone : ii1Hering31CyclicZModHom n c hc
      (Multiplicative.ofAdd (1 : ZMod n)) = c := by
    exact congrArg Additive.toMul (ii1Hering31ZModPowerHom_one n c hc)
  calc
    ii1Hering31CyclicZModHom n c hc (Multiplicative.ofAdd z) =
        ii1Hering31CyclicZModHom n c hc
          (Multiplicative.ofAdd ((z.val : ℕ) : ZMod n)) :=
      congrArg (fun w => ii1Hering31CyclicZModHom n c hc
        (Multiplicative.ofAdd w)) hz
    _ = ii1Hering31CyclicZModHom n c hc
          ((Multiplicative.ofAdd (1 : ZMod n)) ^ z.val) := by
            congr 2
            apply Multiplicative.ext
            change ((z.val : ℕ) : ZMod n) = z.val • (1 : ZMod n)
            rw [← ZMod.natCast_zmod_val z]
            simp
    _ = (ii1Hering31CyclicZModHom n c hc
          (Multiplicative.ofAdd (1 : ZMod n))) ^ z.val := by rw [map_pow]
    _ = c ^ z.val := by rw [hone]

private theorem ii1Hering31_pow_zmod_add_val
    {Q : Type*} [Group Q]
    (n : ℕ) [NeZero n] (c : Q) (hc : c ^ n = 1)
    (z w : ZMod n) : c ^ (z + w).val = c ^ z.val * c ^ w.val := by
  let f := ii1Hering31CyclicZModHom n c hc
  calc
    c ^ (z + w).val = f (Multiplicative.ofAdd (z + w)) := by
      rw [ii1Hering31CyclicZModHom_apply]
    _ = f (Multiplicative.ofAdd z * Multiplicative.ofAdd w) := rfl
    _ = f (Multiplicative.ofAdd z) * f (Multiplicative.ofAdd w) := by
      rw [map_mul]
    _ = c ^ z.val * c ^ w.val := by
      rw [ii1Hering31CyclicZModHom_apply,
        ii1Hering31CyclicZModHom_apply]

private theorem ii1Hering31_pow_zmod_neg_val
    {Q : Type*} [Group Q]
    (n : ℕ) [NeZero n] (c : Q) (hc : c ^ n = 1)
    (z : ZMod n) : c ^ (-z).val = (c ^ z.val)⁻¹ := by
  let f := ii1Hering31CyclicZModHom n c hc
  calc
    c ^ (-z).val = f (Multiplicative.ofAdd (-z)) := by
      rw [ii1Hering31CyclicZModHom_apply]
    _ = f ((Multiplicative.ofAdd z)⁻¹) := rfl
    _ = (f (Multiplicative.ofAdd z))⁻¹ := by rw [map_inv]
    _ = (c ^ z.val)⁻¹ := by rw [ii1Hering31CyclicZModHom_apply]

private theorem ii1Hering31_pow_zmod_mul_val
    {Q : Type*} [Group Q]
    (n : ℕ) [NeZero n] (c : Q) (hc : c ^ n = 1)
    (z w : ZMod n) : c ^ (z * w).val = (c ^ z.val) ^ w.val := by
  let f := ii1Hering31CyclicZModHom n c hc
  calc
    c ^ (z * w).val = f (Multiplicative.ofAdd (z * w)) := by
      rw [ii1Hering31CyclicZModHom_apply]
    _ = f ((Multiplicative.ofAdd z) ^ w.val) := by
      congr 2
      apply Multiplicative.toAdd.injective
      change z * w = w.val • z
      rw [← ZMod.natCast_zmod_val w]
      simp [mul_comm]
    _ = (f (Multiplicative.ofAdd z)) ^ w.val := by rw [map_pow]
    _ = (c ^ z.val) ^ w.val := by rw [ii1Hering31CyclicZModHom_apply]

private theorem ii1Hering31_pow_zmod_natCast_val
    {Q : Type*} [Group Q]
    (n : ℕ) [NeZero n] (c : Q) (hc : c ^ n = 1) (a : ℕ) :
    c ^ (((a : ℕ) : ZMod n).val) = c ^ a := by
  let f := ii1Hering31CyclicZModHom n c hc
  have hone : f (Multiplicative.ofAdd (1 : ZMod n)) = c := by
    exact congrArg Additive.toMul (ii1Hering31ZModPowerHom_one n c hc)
  calc
    c ^ (((a : ℕ) : ZMod n).val) =
        f (Multiplicative.ofAdd ((a : ℕ) : ZMod n)) := by
      rw [ii1Hering31CyclicZModHom_apply]
    _ = f ((Multiplicative.ofAdd (1 : ZMod n)) ^ a) := by
      congr 2
      apply Multiplicative.ext
      change ((a : ℕ) : ZMod n) = a • (1 : ZMod n)
      rw [← ZMod.natCast_zmod_val ((a : ℕ) : ZMod n)]
      simp
    _ = f (Multiplicative.ofAdd (1 : ZMod n)) ^ a := by rw [map_pow]
    _ = c ^ a := by rw [hone]

private def ii1Hering31CoordProj (n : ℕ) (i : Fin 3) :
    Multiplicative (Fin 3 → ZMod n) →* Multiplicative (ZMod n) where
  toFun x := Multiplicative.ofAdd (x.toAdd i)
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def ii1Hering31LayerCoordHom
    {Q : Type*} [Group Q] (hcomm : IsMulCommutative Q)
    (m : ℕ) (c1 c2 c3 : Q)
    (hc1 : c1 ^ 2 ^ m = 1) (hc2 : c2 ^ 2 ^ m = 1)
    (hc3 : c3 ^ 2 ^ m = 1) :
    Multiplicative (Fin 3 → ZMod (2 ^ m)) →* Q := by
  letI : IsMulCommutative Q := hcomm
  let f1 := (ii1Hering31CyclicZModHom (2 ^ m) c1 hc1).comp
    (ii1Hering31CoordProj (2 ^ m) 0)
  let f2 := (ii1Hering31CyclicZModHom (2 ^ m) c2 hc2).comp
    (ii1Hering31CoordProj (2 ^ m) 1)
  let f3 := (ii1Hering31CyclicZModHom (2 ^ m) c3 hc3).comp
    (ii1Hering31CoordProj (2 ^ m) 2)
  exact
    { toFun := fun x => f1 x * f2 x * f3 x
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul]
        ac_rfl }

private theorem ii1Hering31LayerCoordHom_apply
    {Q : Type*} [Group Q] (hcomm : IsMulCommutative Q)
    (m : ℕ) (c1 c2 c3 : Q)
    (hc1 : c1 ^ 2 ^ m = 1) (hc2 : c2 ^ 2 ^ m = 1)
    (hc3 : c3 ^ 2 ^ m = 1)
    (x : Multiplicative (Fin 3 → ZMod (2 ^ m))) :
    ii1Hering31LayerCoordHom hcomm m c1 c2 c3 hc1 hc2 hc3 x =
      c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
        c3 ^ (x.toAdd 2).val := by
  simp [ii1Hering31LayerCoordHom, ii1Hering31CoordProj,
    ii1Hering31CyclicZModHom_apply]

private theorem II1Hering31AbelianExtensionData.layerCoordHom_injective
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (m : ℕ) (hm : 0 < m) (c1 c2 c3 : d.Q)
    (h1 : c1 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩)
    (h2 : c2 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (h3 : c3 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc1 : c1 ^ 2 ^ m = 1) (hc2 : c2 ^ 2 ^ m = 1)
    (hc3 : c3 ^ 2 ^ m = 1) :
    Function.Injective
      (ii1Hering31LayerCoordHom d.Q_commutative m c1 c2 c3
        hc1 hc2 hc3) := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  intro x y hxy
  let z := x * y⁻¹
  have hzMap : ii1Hering31LayerCoordHom d.Q_commutative m c1 c2 c3
      hc1 hc2 hc3 z = 1 := by
    simp [z, hxy]
  rw [ii1Hering31LayerCoordHom_apply] at hzMap
  obtain ⟨hz1, hz2, hz3⟩ := d.layer_coordinates_unique m hm c1 c2 c3
    h1 h2 h3 (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hzMap
  have hzOne : z = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · apply ZMod.val_injective
      simpa [z] using hz1
    · apply ZMod.val_injective
      simpa [z] using hz2
    · apply ZMod.val_injective
      simpa [z] using hz3
  have hxyOne : x * y⁻¹ = 1 := by simpa [z] using hzOne
  calc
    x = (x * y⁻¹) * y := by group
    _ = y := by rw [hxyOne]; simp

private theorem
    II1Hering31AbelianExtensionData.layerCoordHom_range_eq_pow_ker
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (m : ℕ) (hm : 0 < m) (c1 c2 c3 : d.Q)
    (h1 : c1 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩)
    (h2 : c2 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (h3 : c3 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc1 : c1 ^ 2 ^ m = 1) (hc2 : c2 ^ 2 ^ m = 1)
    (hc3 : c3 ^ 2 ^ m = 1) (hc1Order : orderOf c1 = 2 ^ m) :
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    (ii1Hering31LayerCoordHom d.Q_commutative m c1 c2 c3
      hc1 hc2 hc3).range =
      (powMonoidHom (2 ^ m) : d.Q →* d.Q).ker := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let coord := ii1Hering31LayerCoordHom d.Q_commutative m c1 c2 c3
    hc1 hc2 hc3
  have hcoordInj : Function.Injective coord :=
    d.layerCoordHom_injective m hm c1 c2 c3 h1 h2 h3 hc1 hc2 hc3
  obtain ⟨e, _he, ⟨f⟩⟩ := d.Q_homocyclic
  have hmle : m ≤ e := by
    have hc1Exp : c1 ^ 2 ^ e = 1 :=
      External.Higman.lemma1_pow_eq_one_of_homocyclic f c1
    have hdiv : 2 ^ m ∣ 2 ^ e := by
      rw [← hc1Order]
      exact orderOf_dvd_iff_pow_eq_one.mpr hc1Exp
    exact (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
  have hle : coord.range ≤
      (powMonoidHom (2 ^ m) : d.Q →* d.Q).ker := by
    rintro _ ⟨x, rfl⟩
    change (coord x) ^ 2 ^ m = 1
    rw [← map_pow]
    rw [External.Higman.lemma1_pow_eq_one_of_homocyclic
      (MulEquiv.refl (Multiplicative (Fin 3 → ZMod (2 ^ m)))) x]
    exact map_one coord
  have hRangeCard : Nat.card coord.range = (2 ^ m) ^ 3 := by
    let eRange : Multiplicative (Fin 3 → ZMod (2 ^ m)) ≃* coord.range :=
      MulEquiv.ofBijective coord.rangeRestrict ⟨by
        intro x y hxy
        exact hcoordInj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective coord⟩
    calc
      Nat.card coord.range =
          Nat.card (Multiplicative (Fin 3 → ZMod (2 ^ m))) :=
        (Nat.card_congr eRange.toEquiv).symm
      _ = (2 ^ m) ^ 3 := by
        rw [Nat.card_eq_fintype_card]
        simp [ZMod.card]
  have hLayerCard :
      Nat.card ((powMonoidHom (2 ^ m) : d.Q →* d.Q).ker) =
        (2 ^ m) ^ 3 := by
    simpa only [MonoidHom.mem_ker, powMonoidHom_apply] using
      External.Higman.lemma1_powKernel_card_of_homocyclic hmle f
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hRangeCard, hLayerCard])

private theorem ii1Hering31_zmod_two_torsion_cases
    (m : ℕ) (hm : 0 < m)
    (x : ZMod (2 ^ m)) (hx : -x = x) :
    x.val = 0 ∨ x.val = 2 ^ (m - 1) := by
  have hcast : ((2 * x.val : ℕ) : ZMod (2 ^ m)) = 0 := by
    calc
      ((2 * x.val : ℕ) : ZMod (2 ^ m)) =
          (x.val : ZMod (2 ^ m)) + x.val := by push_cast; ring
      _ = x + x := by rw [ZMod.natCast_zmod_val]
      _ = -x + x := congrArg (fun y => y + x) hx.symm
      _ = 0 := neg_add_cancel x
  rw [ZMod.natCast_eq_zero_iff] at hcast
  obtain ⟨k, hk⟩ := hcast
  have hxlt := ZMod.val_lt x
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) _
  have hklt : k < 2 := by
    by_contra hklt
    have hkge : 2 ≤ k := by omega
    have hle : 2 * 2 ^ m ≤ 2 * x.val := by
      calc
        2 * 2 ^ m = 2 ^ m * 2 := Nat.mul_comm _ _
        _ ≤ 2 ^ m * k := Nat.mul_le_mul_left _ hkge
        _ = 2 * x.val := hk.symm
    have hlt : 2 * x.val < 2 * 2 ^ m := by omega
    omega
  interval_cases k <;> omega

private theorem ii1Hering31_order_eq_pow_two_of_top_ne_one
    {Q : Type*} [Group Q]
    (m : ℕ) (hm : 0 < m) (c : Q)
    (hcPow : c ^ 2 ^ m = 1) (hcTop : c ^ 2 ^ (m - 1) ≠ 1) :
    orderOf c = 2 ^ m := by
  have hordDvd : orderOf c ∣ 2 ^ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hcPow
  obtain ⟨r, hrle, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hordDvd
  have hrnot : ¬r ≤ m - 1 := by
    intro hrsmall
    apply hcTop
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hr]
    exact (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mpr hrsmall
  have hrm : r = m := by omega
  rw [hr, hrm]

private theorem ii1Hering31_eq_zero_or_half_of_pow_two_dvd_two_mul
    (m n : ℕ) (hm : 0 < m) (hn : n < 2 ^ m)
    (hdiv : 2 ^ m ∣ 2 * n) : n = 0 ∨ n = 2 ^ (m - 1) := by
  obtain ⟨k, hk⟩ := hdiv
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega
  have hklt : k < 2 := by
    by_contra hklt
    have hkge : 2 ≤ k := by omega
    have hle : 2 * 2 ^ m ≤ 2 * n := by
      calc
        2 * 2 ^ m = 2 ^ m * 2 := Nat.mul_comm _ _
        _ ≤ 2 ^ m * k := Nat.mul_le_mul_left _ hkge
        _ = 2 * n := hk.symm
    have hlt : 2 * n < 2 * 2 ^ m := by omega
    omega
  interval_cases k <;> omega

private theorem ii1Hering31_disjoint_zpowers_of_independent_top
    {Q : Type*} [Group Q]
    (m : ℕ) (hm : 0 < m) (c v : Q)
    (hcOrder : orderOf c = 2 ^ m) (hvOrder : orderOf v = 2)
    (hvSq : v ^ 2 = 1) (hvNe : v ≠ 1)
    (hTop : c ^ 2 ^ (m - 1) ≠ v) :
    Disjoint (Subgroup.zpowers c) (Subgroup.zpowers v) := by
  have hcFin : IsOfFinOrder c := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ m, pow_pos (by norm_num) _, by
      rw [← hcOrder, pow_orderOf_eq_one]⟩
  have hvFin : IsOfFinOrder v := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, hvSq⟩
  rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  let nc : Fin (orderOf c) :=
    (finEquivZPowers hcFin).symm ⟨q, hq.1⟩
  let nv : Fin (orderOf v) :=
    (finEquivZPowers hvFin).symm ⟨q, hq.2⟩
  have hcEq : c ^ (nc : ℕ) = q := by
    simpa [nc] using pow_finEquivZPowers_symm_apply hcFin ⟨q, hq.1⟩
  have hvEq : v ^ (nv : ℕ) = q := by
    simpa [nv] using pow_finEquivZPowers_symm_apply hvFin ⟨q, hq.2⟩
  have hnv : (nv : ℕ) < 2 := by simpa [hvOrder] using nv.isLt
  interval_cases hnvCase : (nv : ℕ)
  · simpa [hnvCase] using hvEq.symm
  · have hqv : q = v := by simpa [hnvCase] using hvEq.symm
    have hcSq : (c ^ (nc : ℕ)) ^ 2 = 1 := by
      rw [hcEq, hqv, hvSq]
    have hdiv : 2 ^ m ∣ 2 * (nc : ℕ) := by
      rw [← hcOrder]
      apply orderOf_dvd_iff_pow_eq_one.mpr
      rw [Nat.mul_comm, pow_mul]
      exact hcSq
    have hncLt : (nc : ℕ) < 2 ^ m := by
      simpa [hcOrder] using nc.isLt
    rcases ii1Hering31_eq_zero_or_half_of_pow_two_dvd_two_mul
      m (nc : ℕ) hm hncLt hdiv with hnc0 | hncTop
    · exfalso
      apply hvNe
      calc
        v = q := hqv.symm
        _ = c ^ (nc : ℕ) := hcEq.symm
        _ = 1 := by rw [hnc0]; simp
    · exfalso
      apply hTop
      calc
        c ^ 2 ^ (m - 1) = c ^ (nc : ℕ) := by rw [hncTop]
        _ = q := hcEq
        _ = v := hqv

private theorem ii1Hering31_card_sup_eq_mul_of_disjoint_of_commutative
    {Q : Type*} [Group Q] [Finite Q] [IsMulCommutative Q]
    (A B : Subgroup Q) (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup Q) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↑(A ⊔ B) := fun z =>
    ⟨(z.1 : Q) * (z.2 : Q),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro z
    have hz : (z : Q) ∈ (A : Set Q) * (B : Set Q) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B]
      · exact z.property
      · rw [Subgroup.normalizer_eq_top]
        exact le_top
    rcases hz with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup Q) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

/-- The normalized elements and cyclic generator produced by Peterfalvi
IV.3, steps 3--4. -/
private structure II1Hering31PeterfalviInitialData
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) where
  s : X
  t : X
  a : X
  b : X
  c1 : d.Q
  m : ℕ
  s_not_mem : s ∉ d.Q
  s_action : d.action s = ii1Hering31AbelianS
  s_sq : s ^ 2 = (d.V_coord.symm ii1Hering31AbelianV1 : d.V)
  t_not_mem : t ∉ d.Q
  t_action : d.action t = ii1Hering31AbelianT
  t_sq_mem : t ^ 2 ∈ d.Q
  a_eq : a = s * t
  a_action : d.action a = ii1Hering31AbelianA
  b_eq : b = a ^ 2
  b_not_mem : b ∉ d.Q
  b_action : d.action b = ii1Hering31AbelianB
  c1_eq : (c1 : X) = b ^ 2
  c1_ne_one : c1 ≠ 1
  c1_order : orderOf c1 = 2 ^ m
  m_ge_two : 2 ≤ m
  c1_top_eq : c1 ^ 2 ^ (m - 1) =
    ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
      d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩

/-- Peterfalvi IV.3, step 4, packaged for the layer calculations in the
remaining steps. -/
private theorem
    II1Hering31AbelianExtensionData.exists_peterfalvi_initial_data
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (ih : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ∀ dY : II1Hering31AbelianExtensionData Y,
        ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q) :
    Nonempty (II1Hering31PeterfalviInitialData d) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  obtain ⟨s, hsQ, hsAction, hs2⟩ :=
    d.exists_normalized_S_lift_of_induction hall ih
  obtain ⟨t, htAction⟩ := d.action_surjective ii1Hering31AbelianT
  have htQ : t ∉ d.Q := by
    intro htQ
    apply ii1Hering31AbelianT_ne_one
    rw [← htAction]
    exact MonoidHom.mem_ker.mp (by simpa [d.action_ker] using htQ)
  have ht2Q : t ^ 2 ∈ d.Q := by
    rw [← d.action_ker, MonoidHom.mem_ker, map_pow, htAction,
      ii1Hering31AbelianT_sq]
  let a : X := s * t
  have haAction : d.action a = ii1Hering31AbelianA := by
    simp [a, ii1Hering31AbelianA, map_mul, hsAction, htAction]
  let b : X := a ^ 2
  have hbAction : d.action b = ii1Hering31AbelianB := by
    simp [b, ii1Hering31AbelianB, map_pow, haAction]
  have hbQ : b ∉ d.Q := by
    intro hbQ
    have hbOne : d.action b = 1 :=
      MonoidHom.mem_ker.mp (by simpa [d.action_ker] using hbQ)
    exact ii1Hering31AbelianB_ne_one (hbAction.symm.trans hbOne)
  have hb2Q : b ^ 2 ∈ d.Q := by
    rw [← d.action_ker, MonoidHom.mem_ker, map_pow, hbAction,
      ii1Hering31AbelianB_sq]
  let c1 : d.Q := ⟨b ^ 2, hb2Q⟩
  have hc1ne : c1 ≠ 1 := by
    intro hc1
    have hb2 : b ^ 2 = 1 := by
      simpa [c1] using congrArg d.Q.subtype hc1
    have hbne : b ≠ 1 := by
      intro hb
      apply hbQ
      rw [hb]
      exact d.Q.one_mem
    exact hbQ (hall b ⟨hbne, hb2⟩)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmOrder⟩ := (IsPGroup.iff_orderOf.mp d.Q_isPGroup) c1
  have hmPos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    rw [hm0, pow_zero] at hmOrder
    exact hc1ne (orderOf_eq_one_iff.mp hmOrder)
  let topQ : d.Q := c1 ^ 2 ^ (m - 1)
  have htop2 : topQ ^ 2 = 1 := by
    change (c1 ^ 2 ^ (m - 1)) ^ 2 = 1
    rw [← pow_mul]
    have hpow : 2 ^ (m - 1) * 2 = 2 ^ m := by
      calc
        2 ^ (m - 1) * 2 = 2 ^ ((m - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ m := by congr 1; omega
    rw [hpow, ← hmOrder, pow_orderOf_eq_one]
  have htopV : (topQ : X) ∈ d.V :=
    (d.V_twoTorsion topQ).2 htop2
  let topV : d.V := ⟨(topQ : X), htopV⟩
  have htopNe : d.V_coord topV ≠ 1 := by
    intro htopOne
    have htopVOne : topV = 1 :=
      d.V_coord.injective (by simpa using htopOne)
    have htopQOne : topQ = 1 := by
      apply d.Q.subtype_injective
      simpa [topV] using congrArg d.V.subtype htopVOne
    have hdiv : 2 ^ m ∣ 2 ^ (m - 1) := by
      rw [← hmOrder]
      exact orderOf_dvd_iff_pow_eq_one.mpr htopQOne
    have : m ≤ m - 1 :=
      (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
    omega
  have hc1Coe : (c1 : X) = a ^ 4 := by
    change (a ^ 2) ^ 2 = a ^ 4
    rw [← pow_mul]
  have haCommTop : Commute a (topQ : X) := by
    change Commute a ((c1 : X) ^ 2 ^ (m - 1))
    exact (hc1Coe ▸ Commute.self_pow a 4).pow_right _
  have htopFix : ii1Hering31AbelianA (d.V_coord topV) =
      d.V_coord topV := by
    rw [← haAction]
    rw [d.action_on_V]
    apply congrArg d.V_coord
    apply Subtype.ext
    calc
      a * (topV : X) * a⁻¹ = (topV : X) * a * a⁻¹ := by
        rw [haCommTop.eq]
      _ = (topV : X) := by simp
  have htopCoord : d.V_coord topV = ii1Hering31AbelianV1 :=
    ii1Hering31AbelianA_fixed_nonzero_eq_v1
      (d.V_coord topV) htopFix htopNe
  let v1Q : d.Q :=
    ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
      d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩
  have htopEq : topQ = v1Q := by
    apply d.Q.subtype_injective
    have htopVEq : topV =
        d.V_coord.symm ii1Hering31AbelianV1 :=
      d.V_coord.injective
        (htopCoord.trans
          (d.V_coord.apply_symm_apply ii1Hering31AbelianV1).symm)
    simpa [topV, v1Q] using congrArg d.V.subtype htopVEq
  have hmTwo : 2 ≤ m := by
    by_contra hm
    have hm1 : m = 1 := by omega
    have hc1EqV1 : c1 = v1Q := by
      simpa [topQ, hm1] using htopEq
    have hnotNorm := ii1Hering31_square_not_mem_abelianNorm
      d.Q d.Q_commutative hall hbQ hb2Q
    apply hnotNorm
    let qV : d.V := d.V_coord.symm ii1Hering31AbelianV3
    let qQ : d.Q := ⟨(qV : X), d.V_le_Q qV.property⟩
    let conjV : d.V := ⟨b * (qV : X) * b⁻¹,
      d.V_normal.conj_mem (qV : X) qV.property b⟩
    have hconjV : d.V_coord conjV =
        ii1Hering31AbelianV1 * ii1Hering31AbelianV3 := by
      calc
        d.V_coord conjV = d.action b (d.V_coord qV) :=
          (d.action_on_V b qV).symm
        _ = ii1Hering31AbelianB ii1Hering31AbelianV3 := by
          simp [hbAction, qV]
        _ = ii1Hering31AbelianV1 * ii1Hering31AbelianV3 := by simp
    let normV : d.V := conjV * qV
    have hnormV : d.V_coord normV = ii1Hering31AbelianV1 := by
      rw [map_mul, hconjV]
      simp [qV]
      decide
    refine ⟨qQ, ?_⟩
    apply d.Q.subtype_injective
    change ((normV : d.V) : X) = b ^ 2
    have hnormEq : normV =
        d.V_coord.symm ii1Hering31AbelianV1 :=
      d.V_coord.injective
        (hnormV.trans
          (d.V_coord.apply_symm_apply ii1Hering31AbelianV1).symm)
    have hnormCoe := congrArg d.V.subtype hnormEq
    rw [← show (c1 : X) = b ^ 2 by rfl, hc1EqV1]
    simpa [v1Q] using hnormCoe
  exact ⟨{
    s := s
    t := t
    a := a
    b := b
    c1 := c1
    m := m
    s_not_mem := hsQ
    s_action := hsAction
    s_sq := hs2
    t_not_mem := htQ
    t_action := htAction
    t_sq_mem := ht2Q
    a_eq := rfl
    a_action := haAction
    b_eq := rfl
    b_not_mem := hbQ
    b_action := hbAction
    c1_eq := rfl
    c1_ne_one := hc1ne
    c1_order := hmOrder
    m_ge_two := hmTwo
    c1_top_eq := by simpa [topQ, v1Q] using htopEq }⟩

/-- Peterfalvi IV.3, step 5: both selected transvections invert the cyclic
generator `c₁`. -/
private theorem II1Hering31PeterfalviInitialData.c1_conj_s_t
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q) :
    z.s * (z.c1 : X) * z.s⁻¹ = (z.c1⁻¹ : d.Q) ∧
      z.t * (z.c1 : X) * z.t⁻¹ = (z.c1⁻¹ : d.Q) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
  have hs2Q : z.s ^ 2 ∈ d.Q := by
    rw [z.s_sq]
    exact d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property
  let s2Q : d.Q := ⟨z.s ^ 2, hs2Q⟩
  have ht2Q : z.t ^ 2 ∈ d.Q := z.t_sq_mem
  let t2Q : d.Q := ⟨z.t ^ 2, ht2Q⟩
  have hAlphaSq (q : d.Q) : alpha (alpha q) = q := by
    apply d.Q.subtype_injective
    change z.s * (z.s * (q : X) * z.s⁻¹) * z.s⁻¹ = (q : X)
    have hcomm : z.s ^ 2 * (q : X) = (q : X) * z.s ^ 2 := by
      simpa [s2Q] using congrArg d.Q.subtype (mul_comm s2Q q)
    calc
      z.s * (z.s * (q : X) * z.s⁻¹) * z.s⁻¹ =
          z.s ^ 2 * (q : X) * (z.s ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = (q : X) * z.s ^ 2 * (z.s ^ 2)⁻¹ := by rw [hcomm]
      _ = (q : X) := by simp
  have hBetaSq (q : d.Q) : beta (beta q) = q := by
    apply d.Q.subtype_injective
    change z.t * (z.t * (q : X) * z.t⁻¹) * z.t⁻¹ = (q : X)
    have hcomm : z.t ^ 2 * (q : X) = (q : X) * z.t ^ 2 := by
      simpa [t2Q] using congrArg d.Q.subtype (mul_comm t2Q q)
    calc
      z.t * (z.t * (q : X) * z.t⁻¹) * z.t⁻¹ =
          z.t ^ 2 * (q : X) * (z.t ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = (q : X) * z.t ^ 2 * (z.t ^ 2)⁻¹ := by rw [hcomm]
      _ = (q : X) := by simp
  have hc1Pow : (z.c1 : X) = z.a ^ 4 := by
    rw [z.c1_eq, z.b_eq]
    rw [← pow_mul]
  have haComm : Commute z.a (z.c1 : X) :=
    hc1Pow ▸ Commute.self_pow z.a 4
  have hAlphaBetaC1 : alpha (beta z.c1) = z.c1 := by
    apply d.Q.subtype_injective
    change z.s * (z.t * (z.c1 : X) * z.t⁻¹) * z.s⁻¹ = (z.c1 : X)
    calc
      z.s * (z.t * (z.c1 : X) * z.t⁻¹) * z.s⁻¹ =
          z.a * (z.c1 : X) * z.a⁻¹ := by
        rw [z.a_eq]
        group
      _ = (z.c1 : X) * z.a * z.a⁻¹ := by rw [haComm.eq]
      _ = (z.c1 : X) := by simp
  have hBetaC1 : beta z.c1 = alpha z.c1 := by
    calc
      beta z.c1 = alpha (alpha (beta z.c1)) :=
        (hAlphaSq (beta z.c1)).symm
      _ = alpha z.c1 := congrArg alpha hAlphaBetaC1
  let w : d.Q := alpha z.c1 * z.c1
  have hAlphaW : alpha w = w := by
    calc
      alpha w = alpha (alpha z.c1) * alpha z.c1 := by simp [w]
      _ = z.c1 * alpha z.c1 := by rw [hAlphaSq]
      _ = alpha z.c1 * z.c1 := mul_comm _ _
      _ = w := rfl
  have hBetaW : beta w = w := by
    calc
      beta w = beta (alpha z.c1) * beta z.c1 := by simp [w]
      _ = beta (beta z.c1) * beta z.c1 := by rw [hBetaC1]
      _ = z.c1 * beta z.c1 := by rw [hBetaSq]
      _ = z.c1 * alpha z.c1 := by rw [hBetaC1]
      _ = alpha z.c1 * z.c1 := mul_comm _ _
      _ = w := rfl
  have hwOne : w = 1 := by
    by_contra hw
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨r, hrOrder⟩ := (IsPGroup.iff_orderOf.mp d.Q_isPGroup) w
    have hrPos : 0 < r := by
      by_contra hr
      have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
      rw [hr0, pow_zero] at hrOrder
      exact hw (orderOf_eq_one_iff.mp hrOrder)
    let topQ : d.Q := w ^ 2 ^ (r - 1)
    have htop2 : topQ ^ 2 = 1 := by
      change (w ^ 2 ^ (r - 1)) ^ 2 = 1
      rw [← pow_mul]
      have hpow : 2 ^ (r - 1) * 2 = 2 ^ r := by
        calc
          2 ^ (r - 1) * 2 = 2 ^ ((r - 1) + 1) := by rw [pow_succ]
          _ = 2 ^ r := by congr 1; omega
      rw [hpow, ← hrOrder, pow_orderOf_eq_one]
    have htopV : (topQ : X) ∈ d.V :=
      (d.V_twoTorsion topQ).2 htop2
    let topV : d.V := ⟨(topQ : X), htopV⟩
    have htopNe : d.V_coord topV ≠ 1 := by
      intro htopOne
      have htopVOne : topV = 1 :=
        d.V_coord.injective (by simpa using htopOne)
      have htopQOne : topQ = 1 := by
        apply d.Q.subtype_injective
        simpa [topV] using congrArg d.V.subtype htopVOne
      have hdiv : 2 ^ r ∣ 2 ^ (r - 1) := by
        rw [← hrOrder]
        exact orderOf_dvd_iff_pow_eq_one.mpr htopQOne
      have : r ≤ r - 1 :=
        (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
      omega
    have hAlphaTop : alpha topQ = topQ := by
      calc
        alpha topQ = (alpha w) ^ 2 ^ (r - 1) := by simp [topQ]
        _ = w ^ 2 ^ (r - 1) := by rw [hAlphaW]
        _ = topQ := rfl
    have hBetaTop : beta topQ = topQ := by
      calc
        beta topQ = (beta w) ^ 2 ^ (r - 1) := by simp [topQ]
        _ = w ^ 2 ^ (r - 1) := by rw [hBetaW]
        _ = topQ := rfl
    have hSFix : ii1Hering31AbelianS (d.V_coord topV) =
        d.V_coord topV := by
      rw [← z.s_action]
      rw [d.action_on_V]
      apply congrArg d.V_coord
      apply Subtype.ext
      simpa [alpha, topV, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype hAlphaTop
    have hTFix : ii1Hering31AbelianT (d.V_coord topV) =
        d.V_coord topV := by
      rw [← z.t_action]
      rw [d.action_on_V]
      apply congrArg d.V_coord
      apply Subtype.ext
      simpa [beta, topV, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype hBetaTop
    have htopCoord : d.V_coord topV = ii1Hering31AbelianV1 :=
      ii1Hering31AbelianST_fixed_nonzero_eq_v1
        (d.V_coord topV) hSFix hTFix htopNe
    let squareQ : d.Q := ⟨z.s ^ 2, hs2Q⟩
    have htopSquare : topQ = squareQ := by
      apply d.Q.subtype_injective
      have htopVEq : topV =
          d.V_coord.symm ii1Hering31AbelianV1 :=
        d.V_coord.injective
          (htopCoord.trans
            (d.V_coord.apply_symm_apply ii1Hering31AbelianV1).symm)
      calc
        (topQ : X) =
            ((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X) := by
          simpa [topV] using congrArg d.V.subtype htopVEq
        _ = z.s ^ 2 := z.s_sq.symm
        _ = (squareQ : X) := rfl
    have hnotNorm := ii1Hering31_square_not_mem_abelianNorm
      d.Q d.Q_commutative hall z.s_not_mem hs2Q
    apply hnotNorm
    refine ⟨z.c1 ^ 2 ^ (r - 1), ?_⟩
    calc
      ii1Hering31AbelianNorm alpha (z.c1 ^ 2 ^ (r - 1)) =
          (ii1Hering31AbelianNorm alpha z.c1) ^ 2 ^ (r - 1) := by
            rw [map_pow]
      _ = w ^ 2 ^ (r - 1) := rfl
      _ = topQ := rfl
      _ = squareQ := htopSquare
  have hsInv : alpha z.c1 = z.c1⁻¹ := by
    calc
      alpha z.c1 = (alpha z.c1 * z.c1) * z.c1⁻¹ := by simp
      _ = w * z.c1⁻¹ := rfl
      _ = z.c1⁻¹ := by rw [hwOne]; simp
  have htInv : beta z.c1 = z.c1⁻¹ := by
    rw [hBetaC1]
    calc
      alpha z.c1 = (alpha z.c1 * z.c1) * z.c1⁻¹ := by simp
      _ = w * z.c1⁻¹ := rfl
      _ = z.c1⁻¹ := by rw [hwOne]; simp
  constructor
  · simpa [alpha, MulAut.conjNormal_apply] using
      congrArg d.Q.subtype hsInv
  · simpa [beta, MulAut.conjNormal_apply] using
      congrArg d.Q.subtype htInv

/-- The exponent-`2^m` basis and the action of `s` produced in Peterfalvi
IV.3, step 6. -/
private structure II1Hering31PeterfalviLayerData
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) where
  c2 : d.Q
  c3 : d.Q
  c2_top_eq : c2 ^ 2 ^ (z.m - 1) =
    ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
      d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩
  c3_top_eq : c3 ^ 2 ^ (z.m - 1) =
    ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
      d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩
  c1_pow_eq : z.c1 ^ 2 ^ z.m = 1
  c2_pow_eq : c2 ^ 2 ^ z.m = 1
  c3_pow_eq : c3 ^ 2 ^ z.m = 1
  coordinates : ∀ q : d.Q, q ^ 2 ^ z.m = 1 →
    ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ z.m)),
      z.c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
        c3 ^ (x.toAdd 2).val = q
  c2_conj_s : z.s * (c2 : X) * z.s⁻¹ = (c2 : X)
  c3_conj_s : z.s * (c3 : X) * z.s⁻¹ = ((c2 * c3⁻¹ : d.Q) : X)

/-- Peterfalvi IV.3, step 6: choose a lift of the third top involution,
obtain the second generator by the `s`-norm, and identify the full
exponent-`2^m` layer with the three cyclic coordinates. -/
private theorem
    II1Hering31PeterfalviInitialData.exists_peterfalvi_layer_data
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) :
    Nonempty (II1Hering31PeterfalviLayerData d z) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let v1 : d.V := d.V_coord.symm ii1Hering31AbelianV1
  let v2 : d.V := d.V_coord.symm ii1Hering31AbelianV2
  let v3 : d.V := d.V_coord.symm ii1Hering31AbelianV3
  have hv1ne : v1 ≠ 1 := by
    intro hv1
    have : ii1Hering31AbelianV1 = 1 := by
      simpa [v1] using congrArg d.V_coord hv1
    exact (show ii1Hering31AbelianV1 ≠ 1 by decide) this
  have hv3ne : v3 ≠ 1 := by
    intro hv3
    have : ii1Hering31AbelianV3 = 1 := by
      simpa [v3] using congrArg d.V_coord hv3
    exact (show ii1Hering31AbelianV3 ≠ 1 by decide) this
  obtain ⟨g, hg⟩ := d.V_action_transitive v1 v3 hv1ne hv3ne
  let gamma : MulAut d.Q := MulAut.conjNormal (H := d.Q) g
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  let v1Q : d.Q := ⟨(v1 : X), d.V_le_Q v1.property⟩
  let v2Q : d.Q := ⟨(v2 : X), d.V_le_Q v2.property⟩
  let v3Q : d.Q := ⟨(v3 : X), d.V_le_Q v3.property⟩
  let c3 : d.Q := gamma z.c1
  have hc3Top : c3 ^ 2 ^ (z.m - 1) = v3Q := by
    calc
      c3 ^ 2 ^ (z.m - 1) = gamma (z.c1 ^ 2 ^ (z.m - 1)) := by
        rw [map_pow]
      _ = gamma v1Q := by
        simpa [v1Q, v1] using congrArg gamma z.c1_top_eq
      _ = v3Q := by
        apply d.Q.subtype_injective
        simpa [gamma, v1Q, v3Q, v1, v3,
          MulAut.conjNormal_apply] using hg
  have hAlphaV3 : alpha v3Q = v2Q * v3Q := by
    let conjV : d.V := ⟨z.s * (v3 : X) * z.s⁻¹,
      d.V_normal.conj_mem (v3 : X) v3.property z.s⟩
    have hcoord : d.V_coord conjV =
        ii1Hering31AbelianV2 * ii1Hering31AbelianV3 := by
      calc
        d.V_coord conjV = d.action z.s (d.V_coord v3) :=
          (d.action_on_V z.s v3).symm
        _ = ii1Hering31AbelianS ii1Hering31AbelianV3 := by
          simp [z.s_action, v3]
        _ = ii1Hering31AbelianV2 * ii1Hering31AbelianV3 :=
          ii1Hering31AbelianS_v3
    have hconjV : conjV = v2 * v3 := by
      apply d.V_coord.injective
      simpa [v2, v3] using hcoord
    apply d.Q.subtype_injective
    simpa [alpha, v2Q, v3Q, conjV, MulAut.conjNormal_apply] using
      congrArg d.V.subtype hconjV
  let c2 : d.Q := alpha c3 * c3
  have hv3Qsq : v3Q ^ 2 = 1 :=
    (d.V_twoTorsion v3Q).1 v3.property
  have hc2Top : c2 ^ 2 ^ (z.m - 1) = v2Q := by
    calc
      c2 ^ 2 ^ (z.m - 1) =
          (alpha c3) ^ 2 ^ (z.m - 1) * c3 ^ 2 ^ (z.m - 1) := by
        change (alpha c3 * c3) ^ 2 ^ (z.m - 1) = _
        rw [mul_pow]
      _ = alpha (c3 ^ 2 ^ (z.m - 1)) * c3 ^ 2 ^ (z.m - 1) := by
        rw [map_pow]
      _ = alpha v3Q * v3Q := by rw [hc3Top]
      _ = (v2Q * v3Q) * v3Q := by rw [hAlphaV3]
      _ = v2Q * v3Q ^ 2 := by rw [pow_two]; ac_rfl
      _ = v2Q := by rw [hv3Qsq]; simp
  have hc1Pow : z.c1 ^ 2 ^ z.m = 1 := by
    rw [← z.c1_order, pow_orderOf_eq_one]
  have hc3Pow : c3 ^ 2 ^ z.m = 1 := by
    calc
      c3 ^ 2 ^ z.m = gamma (z.c1 ^ 2 ^ z.m) := by rw [map_pow]
      _ = 1 := by rw [hc1Pow]; simp
  have hc2Pow : c2 ^ 2 ^ z.m = 1 := by
    change (alpha c3 * c3) ^ 2 ^ z.m = 1
    rw [mul_pow, ← map_pow, hc3Pow]
    simp
  have hs2Q : z.s ^ 2 ∈ d.Q := by
    rw [z.s_sq]
    exact d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property
  let s2Q : d.Q := ⟨z.s ^ 2, hs2Q⟩
  have hAlphaSq (q : d.Q) : alpha (alpha q) = q := by
    apply d.Q.subtype_injective
    change z.s * (z.s * (q : X) * z.s⁻¹) * z.s⁻¹ = (q : X)
    have hcomm : z.s ^ 2 * (q : X) = (q : X) * z.s ^ 2 := by
      simpa [s2Q] using congrArg d.Q.subtype (mul_comm s2Q q)
    calc
      z.s * (z.s * (q : X) * z.s⁻¹) * z.s⁻¹ =
          z.s ^ 2 * (q : X) * (z.s ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = (q : X) * z.s ^ 2 * (z.s ^ 2)⁻¹ := by rw [hcomm]
      _ = (q : X) := by simp
  have hAlphaC2 : alpha c2 = c2 := by
    calc
      alpha c2 = alpha (alpha c3) * alpha c3 := by simp [c2]
      _ = c3 * alpha c3 := by rw [hAlphaSq]
      _ = alpha c3 * c3 := mul_comm _ _
      _ = c2 := rfl
  have hAlphaC3 : alpha c3 = c2 * c3⁻¹ := by
    simp [c2]
  have hRange := d.layerCoordHom_range_eq_pow_ker z.m
    (lt_of_lt_of_le (by norm_num) z.m_ge_two) z.c1 c2 c3 z.c1_top_eq
    (by simpa [v2Q, v2] using hc2Top)
    (by simpa [v3Q, v3] using hc3Top)
    hc1Pow hc2Pow hc3Pow z.c1_order
  refine ⟨{
    c2 := c2
    c3 := c3
    c2_top_eq := by simpa [v2Q, v2] using hc2Top
    c3_top_eq := by simpa [v3Q, v3] using hc3Top
    c1_pow_eq := hc1Pow
    c2_pow_eq := hc2Pow
    c3_pow_eq := hc3Pow
    coordinates := ?_
    c2_conj_s := by
      simpa [alpha, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype hAlphaC2
    c3_conj_s := by
      simpa [alpha, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype hAlphaC3 }⟩
  intro q hq
  have hmem : q ∈ (powMonoidHom (2 ^ z.m) : d.Q →* d.Q).ker := hq
  rw [← hRange] at hmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨x, ?_⟩
  rw [← hx]
  exact (ii1Hering31LayerCoordHom_apply d.Q_commutative z.m z.c1 c2 c3
    hc1Pow hc2Pow hc3Pow x).symm

private def ii1Hering31LayerFixedSubgroup
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (alpha : MulAut Q) : Subgroup Q where
  carrier := {q | q ^ 2 ^ m = 1 ∧ alpha q = q}
  one_mem' := by simp
  mul_mem' := by
    rintro q r ⟨hqPow, hqFix⟩ ⟨hrPow, hrFix⟩
    constructor
    · rw [mul_pow, hqPow, hrPow]
      simp
    · rw [map_mul, hqFix, hrFix]
  inv_mem' := by
    rintro q ⟨hqPow, hqFix⟩
    constructor
    · rw [inv_pow, hqPow]
      simp
    · rw [map_inv, hqFix]

private def ii1Hering31LayerNormSubgroup
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (alpha : MulAut Q) : Subgroup Q :=
  (powMonoidHom (2 ^ m) : Q →* Q).ker.map
    (ii1Hering31AbelianNorm alpha)

private theorem ii1Hering31_layer_norm_eq_zpowers
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (c1 c2 c3 : Q) (hc3 : c3 ^ 2 ^ m = 1)
    (alpha : MulAut Q)
    (ha1 : alpha c1 = c1⁻¹) (ha2 : alpha c2 = c2)
    (ha3 : alpha c3 = c2 * c3⁻¹)
    (hcoords : ∀ q : Q, q ^ 2 ^ m = 1 →
      ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ m)),
        c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
          c3 ^ (x.toAdd 2).val = q) :
    ii1Hering31LayerNormSubgroup m alpha = Subgroup.zpowers c2 := by
  apply le_antisymm
  · rintro y ⟨q, hq, rfl⟩
    obtain ⟨x, hx⟩ := hcoords q hq
    rw [← hx, map_mul, map_mul, map_pow, map_pow, map_pow]
    let H := Subgroup.zpowers c2
    apply H.mul_mem
    · apply H.mul_mem
      · apply H.pow_mem
        change alpha c1 * c1 ∈ H
        rw [ha1]
        simp
      · apply H.pow_mem
        change alpha c2 * c2 ∈ H
        rw [ha2]
        exact H.mul_mem (Subgroup.mem_zpowers c2)
          (Subgroup.mem_zpowers c2)
    · apply H.pow_mem
      change alpha c3 * c3 ∈ H
      rw [ha3]
      rw [show (c2 * c3⁻¹) * c3 = c2 by group]
      exact Subgroup.mem_zpowers c2
  · apply Subgroup.zpowers_le.mpr
    refine ⟨c3, hc3, ?_⟩
    change alpha c3 * c3 = c2
    rw [ha3]
    group

private theorem ii1Hering31_layer_fixed_eq_sup_zpowers
    {Q : Type*} [CommGroup Q]
    (hcomm : IsMulCommutative Q)
    (m : ℕ) (hm : 0 < m) (c1 c2 c3 : Q)
    (hc1 : c1 ^ 2 ^ m = 1) (hc2 : c2 ^ 2 ^ m = 1)
    (hc3 : c3 ^ 2 ^ m = 1)
    (alpha : MulAut Q)
    (ha1 : alpha c1 = c1⁻¹) (ha2 : alpha c2 = c2)
    (ha3 : alpha c3 = c2 * c3⁻¹)
    (hcoords : ∀ q : Q, q ^ 2 ^ m = 1 →
      ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ m)),
        c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
          c3 ^ (x.toAdd 2).val = q)
    (hinj : Function.Injective
      (ii1Hering31LayerCoordHom hcomm m c1 c2 c3 hc1 hc2 hc3)) :
    ii1Hering31LayerFixedSubgroup m alpha =
      Subgroup.zpowers c2 ⊔
        Subgroup.zpowers (c1 ^ 2 ^ (m - 1)) := by
  let coord := ii1Hering31LayerCoordHom hcomm m c1 c2 c3 hc1 hc2 hc3
  apply le_antisymm
  · rintro q ⟨hqPow, hqFix⟩
    obtain ⟨x, hx⟩ := hcoords q hqPow
    let yAdd : Fin 3 → ZMod (2 ^ m) :=
      ![-x.toAdd 0, x.toAdd 1 + x.toAdd 2, -x.toAdd 2]
    let y : Multiplicative (Fin 3 → ZMod (2 ^ m)) :=
      Multiplicative.ofAdd yAdd
    have hcoordY : coord y = alpha q := by
      rw [ii1Hering31LayerCoordHom_apply]
      change c1 ^ (-x.toAdd 0).val *
          c2 ^ (x.toAdd 1 + x.toAdd 2).val *
          c3 ^ (-x.toAdd 2).val = alpha q
      rw [ii1Hering31_pow_zmod_neg_val (2 ^ m) c1 hc1 (x.toAdd 0),
        ii1Hering31_pow_zmod_add_val (2 ^ m) c2 hc2
          (x.toAdd 1) (x.toAdd 2),
        ii1Hering31_pow_zmod_neg_val (2 ^ m) c3 hc3 (x.toAdd 2)]
      rw [← hx]
      simp only [map_mul, map_pow, ha1, ha2, ha3]
      rw [mul_pow]
      group
    have hcoordX : coord x = q := by
      rw [ii1Hering31LayerCoordHom_apply]
      exact hx
    have hyx : y = x := hinj (hcoordY.trans (hqFix.trans hcoordX.symm))
    have hyxAdd := congrArg Multiplicative.toAdd hyx
    have h0 : -x.toAdd 0 = x.toAdd 0 := by
      simpa [y, yAdd] using congrFun hyxAdd 0
    have h1 : x.toAdd 1 + x.toAdd 2 = x.toAdd 1 := by
      simpa [y, yAdd] using congrFun hyxAdd 1
    have h2zero : x.toAdd 2 = 0 := by
      linear_combination h1
    rcases ii1Hering31_zmod_two_torsion_cases m hm (x.toAdd 0) h0 with
      h00 | h0top
    · rw [← hx, h2zero, h00]
      simp only [ZMod.val_zero, pow_zero, mul_one, one_mul]
      exact (show Subgroup.zpowers c2 ≤
        Subgroup.zpowers c2 ⊔
          Subgroup.zpowers (c1 ^ 2 ^ (m - 1)) from le_sup_left)
        (Subgroup.npow_mem_zpowers c2 _)
    · rw [← hx, h2zero, h0top]
      simp only [ZMod.val_zero, pow_zero, mul_one]
      exact (Subgroup.zpowers c2 ⊔
        Subgroup.zpowers (c1 ^ 2 ^ (m - 1))).mul_mem
          ((show Subgroup.zpowers (c1 ^ 2 ^ (m - 1)) ≤
            Subgroup.zpowers c2 ⊔
              Subgroup.zpowers (c1 ^ 2 ^ (m - 1)) from le_sup_right)
            (Subgroup.mem_zpowers _))
          ((show Subgroup.zpowers c2 ≤
            Subgroup.zpowers c2 ⊔
              Subgroup.zpowers (c1 ^ 2 ^ (m - 1)) from le_sup_left)
            (Subgroup.npow_mem_zpowers c2 _))
  · apply sup_le
    · apply Subgroup.zpowers_le.mpr
      exact ⟨hc2, ha2⟩
    · apply Subgroup.zpowers_le.mpr
      let v1 := c1 ^ 2 ^ (m - 1)
      have hpow : 2 ^ (m - 1) * 2 = 2 ^ m := by
        calc
          2 ^ (m - 1) * 2 = 2 ^ ((m - 1) + 1) := by rw [pow_succ]
          _ = 2 ^ m := by congr 1; omega
      have hv1sq : v1 ^ 2 = 1 := by
        change (c1 ^ 2 ^ (m - 1)) ^ 2 = 1
        rw [← pow_mul, hpow, hc1]
      have hv1Pow : v1 ^ 2 ^ m = 1 := by
        rw [show 2 ^ m = 2 * 2 ^ (m - 1) by
          calc
            2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
            _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega]
        rw [pow_mul, hv1sq, one_pow]
      have hv1Inv : v1⁻¹ = v1 := by
        calc
          v1⁻¹ = v1⁻¹ * (v1 ^ 2) := by rw [hv1sq]; simp
          _ = v1 := by group
      refine ⟨hv1Pow, ?_⟩
      change alpha v1 = v1
      change alpha (c1 ^ 2 ^ (m - 1)) = c1 ^ 2 ^ (m - 1)
      rw [map_pow, ha1, inv_pow]
      exact hv1Inv

private theorem ii1Hering31LayerFixedSubgroup_map
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (alpha beta delta : MulAut Q)
    (hintertwine : ∀ q : Q, delta (alpha q) = beta (delta q)) :
    (ii1Hering31LayerFixedSubgroup m alpha).map delta =
      ii1Hering31LayerFixedSubgroup m beta := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    constructor
    · change (delta q) ^ 2 ^ m = 1
      rw [← map_pow, hq.1]
      simp
    · exact (hintertwine q).symm.trans (congrArg delta hq.2)
  · intro q hq
    refine ⟨delta.symm q, ?_, delta.apply_symm_apply q⟩
    constructor
    · apply delta.injective
      rw [map_pow, delta.apply_symm_apply, hq.1]
      simp
    · apply delta.injective
      calc
        delta (alpha (delta.symm q)) = beta (delta (delta.symm q)) :=
          hintertwine _
        _ = beta q := by rw [delta.apply_symm_apply]
        _ = q := hq.2
        _ = delta (delta.symm q) := (delta.apply_symm_apply q).symm

private theorem ii1Hering31LayerNormSubgroup_map
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (alpha beta delta : MulAut Q)
    (hintertwine : ∀ q : Q, delta (alpha q) = beta (delta q)) :
    (ii1Hering31LayerNormSubgroup m alpha).map delta =
      ii1Hering31LayerNormSubgroup m beta := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hqPow : q ^ 2 ^ m = 1 := MonoidHom.mem_ker.mp hq
    refine ⟨delta q, ?_, ?_⟩
    · change (delta q) ^ 2 ^ m = 1
      rw [← map_pow, hqPow]
      simp
    · change beta (delta q) * delta q = delta (alpha q * q)
      rw [map_mul, hintertwine]
  · rintro y ⟨q, hq, rfl⟩
    have hqPow : q ^ 2 ^ m = 1 := MonoidHom.mem_ker.mp hq
    refine ⟨ii1Hering31AbelianNorm alpha (delta.symm q), ?_, ?_⟩
    · refine ⟨delta.symm q, ?_, rfl⟩
      change (delta.symm q) ^ 2 ^ m = 1
      apply delta.injective
      rw [map_pow, delta.apply_symm_apply, hqPow]
      simp
    · change delta (alpha (delta.symm q) * delta.symm q) = beta q * q
      rw [map_mul, hintertwine, delta.apply_symm_apply]

private theorem ii1Hering31LayerNormSubgroup_le_fixed
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (alpha : MulAut Q)
    (hinvolutive : ∀ q : Q, alpha (alpha q) = q) :
    ii1Hering31LayerNormSubgroup m alpha ≤
      ii1Hering31LayerFixedSubgroup m alpha := by
  rintro _ ⟨q, hq, rfl⟩
  have hqPow : q ^ 2 ^ m = 1 := MonoidHom.mem_ker.mp hq
  constructor
  · change (alpha q * q) ^ 2 ^ m = 1
    rw [mul_pow, ← map_pow, hqPow]
    simp
  · change alpha (alpha q * q) = alpha q * q
    rw [map_mul, hinvolutive]
    exact mul_comm _ _

private theorem
    II1Hering31AbelianExtensionData.exists_layer_action_intertwiner
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    {x y : X} (hxQ : x ∉ d.Q) (hx2Q : x ^ 2 ∈ d.Q)
    (hyQ : y ∉ d.Q) (hy2Q : y ^ 2 ∈ d.Q) :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    ∃ delta : MulAut d.Q, ∀ q : d.Q,
      delta (MulAut.conjNormal (H := d.Q) x q) =
        MulAut.conjNormal (H := d.Q) y (delta q) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  obtain ⟨g, hg⟩ := d.quotient_involutions_conjugate hxQ hx2Q hyQ hy2Q
  let r : d.Q := ⟨g⁻¹ * x * g * y⁻¹, hg⟩
  have hxy : g⁻¹ * x * g = (r : X) * y := by
    simp [r]
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) x
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) y
  let delta : MulAut d.Q := MulAut.conjNormal (H := d.Q) g⁻¹
  refine ⟨delta, ?_⟩
  intro q
  let betaDelta : d.Q := beta (delta q)
  have hcomm : (r : X) * (betaDelta : X) =
      (betaDelta : X) * (r : X) := by
    simpa using congrArg d.Q.subtype (mul_comm r betaDelta)
  have hbetaDelta : (betaDelta : X) =
      y * (g⁻¹ * (q : X) * g) * y⁻¹ := by
    simp [betaDelta, beta, delta, MulAut.conjNormal_apply]
  apply d.Q.subtype_injective
  have hcalc : g⁻¹ * (x * (q : X) * x⁻¹) * g =
      y * (g⁻¹ * (q : X) * g) * y⁻¹ := by
    calc
      g⁻¹ * (x * (q : X) * x⁻¹) * g =
          (g⁻¹ * x * g) * (g⁻¹ * (q : X) * g) *
            (g⁻¹ * x * g)⁻¹ := by group
      _ = ((r : X) * y) * (g⁻¹ * (q : X) * g) *
            ((r : X) * y)⁻¹ := by rw [hxy]
      _ = (r : X) * (y * (g⁻¹ * (q : X) * g) * y⁻¹) *
            (r : X)⁻¹ := by group
      _ = (r : X) * (betaDelta : X) * (r : X)⁻¹ := by
        rw [hbetaDelta]
      _ = (betaDelta : X) * (r : X) * (r : X)⁻¹ := by
        rw [hcomm]
      _ = y * (g⁻¹ * (q : X) * g) * y⁻¹ := by
        rw [hbetaDelta]
        simp
  simpa [delta, MulAut.conjNormal_apply] using hcalc

private theorem ii1Hering31_cyclic_subgroup_in_cyclic_times_two
    {Q : Type*} [CommGroup Q]
    (m : ℕ) (hm : 2 ≤ m) (c v r : Q)
    (hcOrder : orderOf c = 2 ^ m) (hvOrder : orderOf v = 2)
    (hvSq : v ^ 2 = 1) (hrOrder : orderOf r = 2 ^ m)
    (hrMem : r ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers v) :
    Subgroup.zpowers r = Subgroup.zpowers c ∨
      Subgroup.zpowers r = Subgroup.zpowers (c * v) := by
  have hcFin : IsOfFinOrder c := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ m, pow_pos (by norm_num) _, by
      rw [← hcOrder, pow_orderOf_eq_one]⟩
  have hvFin : IsOfFinOrder v := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, hvSq⟩
  letI : (Subgroup.zpowers c).Normal := inferInstance
  rcases (Subgroup.mem_sup_of_normal_left (s := Subgroup.zpowers c)
    (t := Subgroup.zpowers v)).mp hrMem with ⟨a, ha, b, hb, hab⟩
  let ic : Fin (orderOf c) :=
    (finEquivZPowers hcFin).symm ⟨a, ha⟩
  let iv : Fin (orderOf v) :=
    (finEquivZPowers hvFin).symm ⟨b, hb⟩
  have haEq : c ^ (ic : ℕ) = a := by
    simpa [ic] using pow_finEquivZPowers_symm_apply hcFin ⟨a, ha⟩
  have hbEq : v ^ (iv : ℕ) = b := by
    simpa [iv] using pow_finEquivZPowers_symm_apply hvFin ⟨b, hb⟩
  have hiv : (iv : ℕ) < 2 := by simpa [hvOrder] using iv.isLt
  have hvHalf : v ^ 2 ^ (m - 1) = 1 := by
    rw [show 2 ^ (m - 1) = 2 * 2 ^ (m - 2) by
      calc
        2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (m - 2) := by rw [pow_succ]; omega]
    rw [pow_mul, hvSq, one_pow]
  interval_cases hivCase : (iv : ℕ)
  · have hrEq : r = c ^ (ic : ℕ) := by
      calc
        r = a * b := hab.symm
        _ = c ^ (ic : ℕ) * b := by rw [haEq]
        _ = c ^ (ic : ℕ) * v ^ 0 := by rw [hbEq]
        _ = c ^ (ic : ℕ) := by simp
    have hiOdd : Odd (ic : ℕ) := by
      rw [← Nat.not_even_iff_odd]
      intro hiEven
      obtain ⟨j, hj⟩ := hiEven
      have hrHalf : r ^ 2 ^ (m - 1) = 1 := by
        rw [hrEq, hj, ← pow_mul]
        have hN : 2 ^ m = 2 * 2 ^ (m - 1) := by
          calc
            2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
            _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega
        have hexp : (j + j) * 2 ^ (m - 1) = 2 ^ m * j := by
          calc
            (j + j) * 2 ^ (m - 1) = (2 * j) * 2 ^ (m - 1) := by
              rw [two_mul]
            _ = (2 * 2 ^ (m - 1)) * j := by ac_rfl
            _ = 2 ^ m * j := by rw [← hN]
        rw [hexp, pow_mul, ← hcOrder, pow_orderOf_eq_one, one_pow]
      have hdiv : 2 ^ m ∣ 2 ^ (m - 1) := by
        rw [← hrOrder]
        exact orderOf_dvd_iff_pow_eq_one.mpr hrHalf
      have : m ≤ m - 1 :=
        (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
      omega
    left
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      rw [hrEq]
      exact Subgroup.npow_mem_zpowers c _
    · apply Subgroup.zpowers_le.mpr
      rw [hrEq]
      apply mem_zpowers_pow_iff.mpr
      simpa only [hcOrder] using
        ((Odd.coprime_two_right hiOdd).pow_right m).gcd_eq_one
  · have hrEq : r = c ^ (ic : ℕ) * v := by
      calc
        r = a * b := hab.symm
        _ = c ^ (ic : ℕ) * b := by rw [haEq]
        _ = c ^ (ic : ℕ) * v ^ 1 := by rw [hbEq]
        _ = c ^ (ic : ℕ) * v := by simp
    have hiOdd : Odd (ic : ℕ) := by
      rw [← Nat.not_even_iff_odd]
      intro hiEven
      obtain ⟨j, hj⟩ := hiEven
      have hrHalf : r ^ 2 ^ (m - 1) = 1 := by
        rw [hrEq, mul_pow, hvHalf, mul_one, hj, ← pow_mul]
        have hN : 2 ^ m = 2 * 2 ^ (m - 1) := by
          calc
            2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
            _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega
        have hexp : (j + j) * 2 ^ (m - 1) = 2 ^ m * j := by
          calc
            (j + j) * 2 ^ (m - 1) = (2 * j) * 2 ^ (m - 1) := by
              rw [two_mul]
            _ = (2 * 2 ^ (m - 1)) * j := by ac_rfl
            _ = 2 ^ m * j := by rw [← hN]
        rw [hexp, pow_mul, ← hcOrder, pow_orderOf_eq_one, one_pow]
      have hdiv : 2 ^ m ∣ 2 ^ (m - 1) := by
        rw [← hrOrder]
        exact orderOf_dvd_iff_pow_eq_one.mpr hrHalf
      have : m ≤ m - 1 :=
        (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
      omega
    have hcvPow : (c * v) ^ 2 ^ m = 1 := by
      rw [mul_pow]
      have hcPow : c ^ 2 ^ m = 1 := by
        rw [← hcOrder, pow_orderOf_eq_one]
      have hvPow : v ^ 2 ^ m = 1 := by
        rw [show 2 ^ m = 2 * 2 ^ (m - 1) by
          calc
            2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
            _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; omega]
        rw [pow_mul, hvSq, one_pow]
      rw [hcPow, hvPow]
      simp
    have hcTopNe : c ^ 2 ^ (m - 1) ≠ 1 := by
      intro htop
      have hdiv : 2 ^ m ∣ 2 ^ (m - 1) := by
        rw [← hcOrder]
        exact orderOf_dvd_iff_pow_eq_one.mpr htop
      exact (by
        have : m ≤ m - 1 :=
          (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdiv
        omega)
    have hcvTop : (c * v) ^ 2 ^ (m - 1) ≠ 1 := by
      rw [mul_pow, hvHalf, mul_one]
      exact hcTopNe
    have hcvOrder : orderOf (c * v) = 2 ^ m :=
      ii1Hering31_order_eq_pow_two_of_top_ne_one m (by omega)
        (c * v) hcvPow hcvTop
    have hicop : Nat.Coprime (ic : ℕ) (2 ^ m) :=
      (Odd.coprime_two_right hiOdd).pow_right m
    obtain ⟨j, hj⟩ := hiOdd
    have hvOddPow : v ^ (ic : ℕ) = v := by
      rw [hj, pow_add, pow_mul, hvSq]
      simp
    have hrPow : r = (c * v) ^ (ic : ℕ) := by
      rw [hrEq, mul_pow, hvOddPow]
    right
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      rw [hrPow]
      exact Subgroup.npow_mem_zpowers (c * v) _
    · apply Subgroup.zpowers_le.mpr
      rw [hrPow]
      apply mem_zpowers_pow_iff.mpr
      simpa only [hcvOrder] using hicop.gcd_eq_one

/-- Peterfalvi IV.3, step 7: transfer the fixed and norm subgroups from `s`
to `b`, then use `b² = c₁` to select the nontrivial cyclic alternative. -/
private theorem ii1Hering31_peterfalvi_step7
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc1Pow : z.c1 ^ 2 ^ z.m = 1)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (hcoords : ∀ q : d.Q, q ^ 2 ^ z.m = 1 →
      ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ z.m)),
        z.c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
          c3 ^ (x.toAdd 2).val = q)
    (hc2s : z.s * (c2 : X) * z.s⁻¹ = (c2 : X))
    (hc3s : z.s * (c3 : X) * z.s⁻¹ = ((c2 * c3⁻¹ : d.Q) : X)) :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
    let v2Q : d.Q :=
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩
    ii1Hering31LayerFixedSubgroup z.m beta =
        Subgroup.zpowers z.c1 ⊔ Subgroup.zpowers v2Q ∧
      ii1Hering31LayerNormSubgroup z.m beta =
        Subgroup.zpowers (z.c1 * v2Q) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
  let v1 : d.V := d.V_coord.symm ii1Hering31AbelianV1
  let v2 : d.V := d.V_coord.symm ii1Hering31AbelianV2
  let v1Q : d.Q := ⟨(v1 : X), d.V_le_Q v1.property⟩
  let v2Q : d.Q := ⟨(v2 : X), d.V_le_Q v2.property⟩
  have hv1ne : v1Q ≠ 1 := by
    intro hv1
    have hv1V : v1 = 1 := by
      apply d.V.subtype_injective
      simpa [v1Q] using congrArg d.Q.subtype hv1
    have : ii1Hering31AbelianV1 = 1 := by
      simpa [v1] using congrArg d.V_coord hv1V
    exact (show ii1Hering31AbelianV1 ≠ 1 by decide) this
  have hv2ne : v2Q ≠ 1 := by
    intro hv2
    have hv2V : v2 = 1 := by
      apply d.V.subtype_injective
      simpa [v2Q] using congrArg d.Q.subtype hv2
    have : ii1Hering31AbelianV2 = 1 := by
      simpa [v2] using congrArg d.V_coord hv2V
    exact (show ii1Hering31AbelianV2 ≠ 1 by decide) this
  have hv12ne : v1Q ≠ v2Q := by
    intro hv12
    have hv12V : v1 = v2 := by
      apply d.V.subtype_injective
      simpa [v1Q, v2Q] using congrArg d.Q.subtype hv12
    have : ii1Hering31AbelianV1 = ii1Hering31AbelianV2 := by
      simpa [v1, v2] using congrArg d.V_coord hv12V
    exact (show ii1Hering31AbelianV1 ≠ ii1Hering31AbelianV2 by decide) this
  have hv1sq : v1Q ^ 2 = 1 :=
    (d.V_twoTorsion v1Q).1 v1.property
  have hv2sq : v2Q ^ 2 = 1 :=
    (d.V_twoTorsion v2Q).1 v2.property
  have hv1Order : orderOf v1Q = 2 :=
    orderOf_eq_prime hv1sq hv1ne
  have hv2Order : orderOf v2Q = 2 :=
    orderOf_eq_prime hv2sq hv2ne
  have hc2TopNe : c2 ^ 2 ^ (z.m - 1) ≠ 1 := by
    rw [hc2Top]
    exact hv2ne
  have hc2Order : orderOf c2 = 2 ^ z.m :=
    ii1Hering31_order_eq_pow_two_of_top_ne_one z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) c2 hc2Pow hc2TopNe
  have hsStep5 := z.c1_conj_s_t d hall
  have ha1 : alpha z.c1 = z.c1⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hsStep5.1
  have ha2 : alpha c2 = c2 := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hc2s
  have ha3 : alpha c3 = c2 * c3⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hc3s
  have hinj := d.layerCoordHom_injective z.m
    (lt_of_lt_of_le (by norm_num) z.m_ge_two) z.c1 c2 c3
    z.c1_top_eq hc2Top hc3Top hc1Pow hc2Pow hc3Pow
  have hNormS : ii1Hering31LayerNormSubgroup z.m alpha =
      Subgroup.zpowers c2 :=
    ii1Hering31_layer_norm_eq_zpowers z.m z.c1 c2 c3 hc3Pow
      alpha ha1 ha2 ha3 hcoords
  have hFixedS : ii1Hering31LayerFixedSubgroup z.m alpha =
      Subgroup.zpowers c2 ⊔
        Subgroup.zpowers (z.c1 ^ 2 ^ (z.m - 1)) :=
    ii1Hering31_layer_fixed_eq_sup_zpowers d.Q_commutative z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) z.c1 c2 c3
      hc1Pow hc2Pow hc3Pow alpha ha1 ha2 ha3 hcoords hinj
  have hc2TopV1Ne : c2 ^ 2 ^ (z.m - 1) ≠ v1Q := by
    rw [hc2Top]
    exact hv12ne.symm
  have hdisjS : Disjoint (Subgroup.zpowers c2)
      (Subgroup.zpowers v1Q) :=
    ii1Hering31_disjoint_zpowers_of_independent_top z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) c2 v1Q
      hc2Order hv1Order hv1sq hv1ne hc2TopV1Ne
  have hFixedSCard : Nat.card (ii1Hering31LayerFixedSubgroup z.m alpha) =
      (2 ^ z.m) * 2 := by
    rw [hFixedS, z.c1_top_eq]
    rw [ii1Hering31_card_sup_eq_mul_of_disjoint_of_commutative _ _ hdisjS,
      Nat.card_zpowers, Nat.card_zpowers, hc2Order, hv1Order]
  have hs2Q : z.s ^ 2 ∈ d.Q := by
    rw [z.s_sq]
    exact d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property
  have hb2Q : z.b ^ 2 ∈ d.Q := by
    rw [← z.c1_eq]
    exact z.c1.property
  obtain ⟨delta, hintertwine⟩ := d.exists_layer_action_intertwiner
    z.s_not_mem hs2Q z.b_not_mem hb2Q
  have hFixedMap :=
    ii1Hering31LayerFixedSubgroup_map z.m alpha beta delta hintertwine
  have hNormMap :=
    ii1Hering31LayerNormSubgroup_map z.m alpha beta delta hintertwine
  have hFixedBCard : Nat.card (ii1Hering31LayerFixedSubgroup z.m beta) =
      (2 ^ z.m) * 2 := by
    calc
      Nat.card (ii1Hering31LayerFixedSubgroup z.m beta) =
          Nat.card ((ii1Hering31LayerFixedSubgroup z.m alpha).map
            (delta : d.Q →* d.Q)) := by rw [hFixedMap]
      _ = Nat.card (ii1Hering31LayerFixedSubgroup z.m alpha) :=
        Subgroup.card_map_of_injective delta.injective
      _ = (2 ^ z.m) * 2 := hFixedSCard
  have hb1 : beta z.c1 = z.c1 := by
    apply d.Q.subtype_injective
    change z.b * (z.c1 : X) * z.b⁻¹ = (z.c1 : X)
    rw [z.c1_eq]
    group
  have hb2 : beta v2Q = v2Q := by
    let conjV : d.V := ⟨z.b * (v2 : X) * z.b⁻¹,
      d.V_normal.conj_mem (v2 : X) v2.property z.b⟩
    have hcoord : d.V_coord conjV = ii1Hering31AbelianV2 := by
      calc
        d.V_coord conjV = d.action z.b (d.V_coord v2) :=
          (d.action_on_V z.b v2).symm
        _ = ii1Hering31AbelianB ii1Hering31AbelianV2 := by
          simp [z.b_action, v2]
        _ = ii1Hering31AbelianV2 := ii1Hering31AbelianB_v2
    have hconj : conjV = v2 := by
      apply d.V_coord.injective
      simpa [v2] using hcoord
    apply d.Q.subtype_injective
    simpa [beta, v2Q, conjV, MulAut.conjNormal_apply] using
      congrArg d.V.subtype hconj
  have hv2Pow : v2Q ^ 2 ^ z.m = 1 := by
    rw [show 2 ^ z.m = 2 * 2 ^ (z.m - 1) by
      have hmOne : 1 ≤ z.m := le_trans (by norm_num) z.m_ge_two
      calc
        2 ^ z.m = 2 ^ ((z.m - 1) + 1) := by
          exact congrArg (fun n : ℕ => 2 ^ n)
            (Nat.sub_add_cancel hmOne).symm
        _ = 2 * 2 ^ (z.m - 1) := by rw [pow_succ, Nat.mul_comm]]
    rw [pow_mul, hv2sq, one_pow]
  let K : Subgroup d.Q :=
    Subgroup.zpowers z.c1 ⊔ Subgroup.zpowers v2Q
  have hKle : K ≤ ii1Hering31LayerFixedSubgroup z.m beta := by
    apply sup_le
    · apply Subgroup.zpowers_le.mpr
      exact ⟨hc1Pow, hb1⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨hv2Pow, hb2⟩
  have hc1TopV2Ne : z.c1 ^ 2 ^ (z.m - 1) ≠ v2Q := by
    rw [z.c1_top_eq]
    exact hv12ne
  have hdisjK : Disjoint (Subgroup.zpowers z.c1)
      (Subgroup.zpowers v2Q) :=
    ii1Hering31_disjoint_zpowers_of_independent_top z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) z.c1 v2Q
      z.c1_order hv2Order hv2sq hv2ne hc1TopV2Ne
  have hKCard : Nat.card K = (2 ^ z.m) * 2 := by
    dsimp [K]
    rw [ii1Hering31_card_sup_eq_mul_of_disjoint_of_commutative _ _ hdisjK,
      Nat.card_zpowers, Nat.card_zpowers, z.c1_order, hv2Order]
  have hFixedB : ii1Hering31LayerFixedSubgroup z.m beta = K :=
    (Subgroup.eq_of_le_of_card_ge hKle
      (by rw [hKCard, hFixedBCard])).symm
  have hNormBcyc : ii1Hering31LayerNormSubgroup z.m beta =
      Subgroup.zpowers (delta c2) := by
    calc
      ii1Hering31LayerNormSubgroup z.m beta =
          (ii1Hering31LayerNormSubgroup z.m alpha).map
            (delta : d.Q →* d.Q) := hNormMap.symm
      _ = (Subgroup.zpowers c2).map (delta : d.Q →* d.Q) := by
        rw [hNormS]
      _ = Subgroup.zpowers (delta c2) :=
        MonoidHom.map_zpowers (delta : d.Q →* d.Q) c2
  have hBetaSq (q : d.Q) : beta (beta q) = q := by
    apply d.Q.subtype_injective
    change z.b * (z.b * (q : X) * z.b⁻¹) * z.b⁻¹ = (q : X)
    have hcomm : z.b ^ 2 * (q : X) = (q : X) * z.b ^ 2 := by
      let b2Q : d.Q := ⟨z.b ^ 2, hb2Q⟩
      simpa [b2Q] using congrArg d.Q.subtype (mul_comm b2Q q)
    calc
      z.b * (z.b * (q : X) * z.b⁻¹) * z.b⁻¹ =
          z.b ^ 2 * (q : X) * (z.b ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = (q : X) * z.b ^ 2 * (z.b ^ 2)⁻¹ := by rw [hcomm]
      _ = (q : X) := by simp
  have hNormBLeK : ii1Hering31LayerNormSubgroup z.m beta ≤ K := by
    rw [← hFixedB]
    exact ii1Hering31LayerNormSubgroup_le_fixed z.m beta hBetaSq
  have hrMem : delta c2 ∈ K :=
    hNormBLeK (hNormBcyc ▸ Subgroup.mem_zpowers (delta c2))
  have hrOrder : orderOf (delta c2) = 2 ^ z.m := by
    rw [delta.orderOf_eq, hc2Order]
  rcases ii1Hering31_cyclic_subgroup_in_cyclic_times_two z.m z.m_ge_two
    z.c1 v2Q (delta c2) z.c1_order hv2Order hv2sq hrOrder hrMem with
    hNormFirst | hNormSecond
  · exfalso
    have hc1Norm : z.c1 ∈ ii1Hering31LayerNormSubgroup z.m beta := by
      rw [hNormBcyc, hNormFirst]
      exact Subgroup.mem_zpowers z.c1
    have hnotNorm := ii1Hering31_square_not_mem_abelianNorm
      d.Q d.Q_commutative hall z.b_not_mem hb2Q
    apply hnotNorm
    have hc1Square : (⟨z.b ^ 2, hb2Q⟩ : d.Q) = z.c1 := by
      apply d.Q.subtype_injective
      exact z.c1_eq.symm
    rw [hc1Square]
    rcases hc1Norm with ⟨q, _hq, hq⟩
    exact ⟨q, hq⟩
  · refine ⟨?_, ?_⟩
    · simpa [K, v2Q, v2] using hFixedB
    · calc
        ii1Hering31LayerNormSubgroup z.m beta =
            Subgroup.zpowers (delta c2) := hNormBcyc
        _ = Subgroup.zpowers (z.c1 * v2Q) := hNormSecond

private theorem ii1Hering31_layer_coordinate_parities_of_top_v1
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (m : ℕ) (c1 c2 c3 q : d.Q)
    (h1 : c1 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩)
    (h2 : c2 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (h3 : c3 ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (n1 n2 n3 : ℕ)
    (hrel : c1 ^ n1 * c2 ^ n2 * c3 ^ n3 = q)
    (hqTop : q ^ 2 ^ (m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩) :
    Odd n1 ∧ 2 ∣ n2 ∧ 2 ∣ n3 := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  let v1 : d.V := d.V_coord.symm ii1Hering31AbelianV1
  let v2 : d.V := d.V_coord.symm ii1Hering31AbelianV2
  let v3 : d.V := d.V_coord.symm ii1Hering31AbelianV3
  let v1Q : d.Q := ⟨(v1 : X), d.V_le_Q v1.property⟩
  have hpow (c : d.Q) (n : ℕ) :
      (c ^ n) ^ 2 ^ (m - 1) = (c ^ 2 ^ (m - 1)) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have htopRel :
      (c1 ^ 2 ^ (m - 1)) ^ n1 *
          (c2 ^ 2 ^ (m - 1)) ^ n2 *
          (c3 ^ 2 ^ (m - 1)) ^ n3 = v1Q := by
    calc
      (c1 ^ 2 ^ (m - 1)) ^ n1 *
            (c2 ^ 2 ^ (m - 1)) ^ n2 *
            (c3 ^ 2 ^ (m - 1)) ^ n3 =
          (c1 ^ n1 * c2 ^ n2 * c3 ^ n3) ^ 2 ^ (m - 1) := by
        rw [mul_pow, mul_pow, hpow, hpow, hpow]
      _ = q ^ 2 ^ (m - 1) :=
        congrArg (fun r => r ^ 2 ^ (m - 1)) hrel
      _ = v1Q := by simpa [v1Q, v1] using hqTop
  rw [h1, h2, h3] at htopRel
  have hvRel : v1 ^ n1 * v2 ^ n2 * v3 ^ n3 = v1 := by
    apply d.V.subtype_injective
    simpa [v1Q, v1, v2, v3] using congrArg d.Q.subtype htopRel
  have hcoordRel : ii1Hering31AbelianV1 ^ n1 *
      ii1Hering31AbelianV2 ^ n2 * ii1Hering31AbelianV3 ^ n3 =
        ii1Hering31AbelianV1 := by
    simpa [v1, v2, v3] using congrArg d.V_coord hvRel
  have hcoordOne : ii1Hering31AbelianV1 ^ (n1 + 1) *
      ii1Hering31AbelianV2 ^ n2 * ii1Hering31AbelianV3 ^ n3 = 1 := by
    calc
      ii1Hering31AbelianV1 ^ (n1 + 1) *
            ii1Hering31AbelianV2 ^ n2 * ii1Hering31AbelianV3 ^ n3 =
          (ii1Hering31AbelianV1 ^ n1 *
            ii1Hering31AbelianV2 ^ n2 *
            ii1Hering31AbelianV3 ^ n3) * ii1Hering31AbelianV1 := by
        rw [pow_succ]
        ac_rfl
      _ = ii1Hering31AbelianV1 * ii1Hering31AbelianV1 := by
        rw [hcoordRel]
      _ = 1 := by decide
  obtain ⟨h1div, h2div, h3div⟩ :=
    ii1Hering31Abelian_basis_relation_dvd_two (n1 + 1) n2 n3 hcoordOne
  obtain ⟨k, hk⟩ := h1div
  refine ⟨⟨k - 1, ?_⟩, h2div, h3div⟩
  omega

private structure II1Hering31PeterfalviStep8Data
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q) where
  c1 : d.Q
  d0 : d.Q
  k : ℕ
  k2 : ℕ
  k3 : ℕ
  k_lt : k < 2 ^ z.m
  k2_lt : k2 < 2 ^ (z.m - 1)
  k3_lt : k3 < 2 ^ (z.m - 1)
  c1_top_eq : c1 ^ 2 ^ (z.m - 1) =
    ⟨((d.V_coord.symm ii1Hering31AbelianV1 : d.V) : X),
      d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property⟩
  c1_pow_eq : c1 ^ 2 ^ z.m = 1
  c1_order : orderOf c1 = 2 ^ z.m
  coordinates : ∀ q : d.Q, q ^ 2 ^ z.m = 1 →
    ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ z.m)),
      c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
        c3 ^ (x.toAdd 2).val = q
  c1_conj_s : z.s * (c1 : X) * z.s⁻¹ = (c1⁻¹ : d.Q)
  c1_conj_t : z.t * (c1 : X) * z.t⁻¹ = (c1⁻¹ : d.Q)
  c1_conj_b : z.b * (c1 : X) * z.b⁻¹ = (c1 : X)
  c2_conj_s : z.s * (c2 : X) * z.s⁻¹ = (c2 : X)
  c3_conj_s : z.s * (c3 : X) * z.s⁻¹ = ((c2 * c3⁻¹ : d.Q) : X)
  c2_conj_t : z.t * (c2 : X) * z.t⁻¹ = ((c2⁻¹ * d0 : d.Q) : X)
  c3_conj_t : z.t * (c3 : X) * z.t⁻¹ =
    ((c3⁻¹ * d0 ^ k : d.Q) : X)
  d0_eq : d0 = c1 * c2 ^ (2 * k2) * c3 ^ (2 * k3)
  d0_conj_t : z.t * (d0 : X) * z.t⁻¹ = (d0 : X)
  b_norm_eq :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
    ii1Hering31LayerNormSubgroup z.m beta =
      Subgroup.zpowers
        (c1 * ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
          d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)

/-- Peterfalvi IV.3, step 8: normalize the odd `c₁` coordinate of the
`t`-norm of `c₂`, then describe the complete `t`-action on the layer basis. -/
private theorem ii1Hering31_peterfalvi_step8
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (hall : ∀ y : X, IsInvolution y → y ∈ d.Q)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc1Pow : z.c1 ^ 2 ^ z.m = 1)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (hcoords : ∀ q : d.Q, q ^ 2 ^ z.m = 1 →
      ∃ x : Multiplicative (Fin 3 → ZMod (2 ^ z.m)),
        z.c1 ^ (x.toAdd 0).val * c2 ^ (x.toAdd 1).val *
          c3 ^ (x.toAdd 2).val = q)
    (hc2s : z.s * (c2 : X) * z.s⁻¹ = (c2 : X))
    (hc3s : z.s * (c3 : X) * z.s⁻¹ = ((c2 * c3⁻¹ : d.Q) : X)) :
    Nonempty (II1Hering31PeterfalviStep8Data d z c2 c3) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  let tau : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
  let v1 : d.V := d.V_coord.symm ii1Hering31AbelianV1
  let v2 : d.V := d.V_coord.symm ii1Hering31AbelianV2
  let v1Q : d.Q := ⟨(v1 : X), d.V_le_Q v1.property⟩
  let v2Q : d.Q := ⟨(v2 : X), d.V_le_Q v2.property⟩
  have hv1ne : v1Q ≠ 1 := by
    intro hv1
    have hv1V : v1 = 1 := by
      apply d.V.subtype_injective
      simpa [v1Q] using congrArg d.Q.subtype hv1
    have : ii1Hering31AbelianV1 = 1 := by
      simpa [v1] using congrArg d.V_coord hv1V
    exact (show ii1Hering31AbelianV1 ≠ 1 by decide) this
  have hv1sq : v1Q ^ 2 = 1 :=
    (d.V_twoTorsion v1Q).1 v1.property
  have hv2sq : v2Q ^ 2 = 1 :=
    (d.V_twoTorsion v2Q).1 v2.property
  have hv2ne : v2Q ≠ 1 := by
    intro hv2
    have hv2V : v2 = 1 := by
      apply d.V.subtype_injective
      simpa [v2Q] using congrArg d.Q.subtype hv2
    have : ii1Hering31AbelianV2 = 1 := by
      simpa [v2] using congrArg d.V_coord hv2V
    exact (show ii1Hering31AbelianV2 ≠ 1 by decide) this
  have hc2TopNe : c2 ^ 2 ^ (z.m - 1) ≠ 1 := by
    rw [hc2Top]
    exact hv2ne
  have hc2Order : orderOf c2 = 2 ^ z.m :=
    ii1Hering31_order_eq_pow_two_of_top_ne_one z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) c2 hc2Pow hc2TopNe
  have hTauV2 : tau v2Q = v1Q * v2Q := by
    let conjV : d.V := ⟨z.t * (v2 : X) * z.t⁻¹,
      d.V_normal.conj_mem (v2 : X) v2.property z.t⟩
    have hcoord : d.V_coord conjV =
        ii1Hering31AbelianV1 * ii1Hering31AbelianV2 := by
      calc
        d.V_coord conjV = d.action z.t (d.V_coord v2) :=
          (d.action_on_V z.t v2).symm
        _ = ii1Hering31AbelianT ii1Hering31AbelianV2 := by
          simp [z.t_action, v2]
        _ = ii1Hering31AbelianV1 * ii1Hering31AbelianV2 :=
          ii1Hering31AbelianT_v2
    have hconj : conjV = v1 * v2 := by
      apply d.V_coord.injective
      simpa [v1, v2] using hcoord
    apply d.Q.subtype_injective
    simpa [tau, v1Q, v2Q, conjV, MulAut.conjNormal_apply] using
      congrArg d.V.subtype hconj
  let d0 : d.Q := tau c2 * c2
  have hdTop : d0 ^ 2 ^ (z.m - 1) = v1Q := by
    calc
      d0 ^ 2 ^ (z.m - 1) =
          (tau c2) ^ 2 ^ (z.m - 1) * c2 ^ 2 ^ (z.m - 1) := by
        simp [d0, mul_pow]
      _ = tau (c2 ^ 2 ^ (z.m - 1)) * c2 ^ 2 ^ (z.m - 1) := by
        rw [map_pow]
      _ = tau v2Q * v2Q := by rw [hc2Top]
      _ = (v1Q * v2Q) * v2Q := by rw [hTauV2]
      _ = v1Q * v2Q ^ 2 := by rw [pow_two]; ac_rfl
      _ = v1Q := by rw [hv2sq]; simp
  have hdPow : d0 ^ 2 ^ z.m = 1 := by
    change (tau c2 * c2) ^ 2 ^ z.m = 1
    rw [mul_pow, ← map_pow, hc2Pow]
    simp
  have hdTopNe : d0 ^ 2 ^ (z.m - 1) ≠ 1 := by
    rw [hdTop]
    exact hv1ne
  have hdOrder : orderOf d0 = 2 ^ z.m :=
    ii1Hering31_order_eq_pow_two_of_top_ne_one z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) d0 hdPow hdTopNe
  have hTauSq (q : d.Q) : tau (tau q) = q := by
    apply d.Q.subtype_injective
    change z.t * (z.t * (q : X) * z.t⁻¹) * z.t⁻¹ = (q : X)
    let t2Q : d.Q := ⟨z.t ^ 2, z.t_sq_mem⟩
    have hcomm : z.t ^ 2 * (q : X) = (q : X) * z.t ^ 2 := by
      simpa [t2Q] using congrArg d.Q.subtype (mul_comm t2Q q)
    calc
      z.t * (z.t * (q : X) * z.t⁻¹) * z.t⁻¹ =
          z.t ^ 2 * (q : X) * (z.t ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = (q : X) * z.t ^ 2 * (z.t ^ 2)⁻¹ := by rw [hcomm]
      _ = (q : X) := by simp
  have hsStep5 := z.c1_conj_s_t d hall
  have ha1 : alpha z.c1 = z.c1⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hsStep5.1
  have ha2 : alpha c2 = c2 := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hc2s
  have ha3 : alpha c3 = c2 * c3⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using hc3s
  have hNormS : ii1Hering31LayerNormSubgroup z.m alpha =
      Subgroup.zpowers c2 :=
    ii1Hering31_layer_norm_eq_zpowers z.m z.c1 c2 c3 hc3Pow
      alpha ha1 ha2 ha3 hcoords
  have hs2Q : z.s ^ 2 ∈ d.Q := by
    rw [z.s_sq]
    exact d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV1).property
  obtain ⟨delta, hintertwine⟩ := d.exists_layer_action_intertwiner
    z.s_not_mem hs2Q z.t_not_mem z.t_sq_mem
  have hNormMap :=
    ii1Hering31LayerNormSubgroup_map z.m alpha tau delta hintertwine
  have hNormTCard : Nat.card (ii1Hering31LayerNormSubgroup z.m tau) =
      2 ^ z.m := by
    calc
      Nat.card (ii1Hering31LayerNormSubgroup z.m tau) =
          Nat.card ((ii1Hering31LayerNormSubgroup z.m alpha).map
            (delta : d.Q →* d.Q)) := by rw [hNormMap]
      _ = Nat.card (ii1Hering31LayerNormSubgroup z.m alpha) :=
        Subgroup.card_map_of_injective delta.injective
      _ = Nat.card (Subgroup.zpowers c2) := by rw [hNormS]
      _ = 2 ^ z.m := by rw [Nat.card_zpowers, hc2Order]
  have hdMem : d0 ∈ ii1Hering31LayerNormSubgroup z.m tau := by
    exact ⟨c2, hc2Pow, rfl⟩
  have hdLe : Subgroup.zpowers d0 ≤
      ii1Hering31LayerNormSubgroup z.m tau :=
    Subgroup.zpowers_le.mpr hdMem
  have hdCard : Nat.card (Subgroup.zpowers d0) = 2 ^ z.m := by
    rw [Nat.card_zpowers, hdOrder]
  have hNormT : ii1Hering31LayerNormSubgroup z.m tau =
      Subgroup.zpowers d0 :=
    (Subgroup.eq_of_le_of_card_ge hdLe
      (by rw [hdCard, hNormTCard])).symm
  have hNormC3 : ii1Hering31AbelianNorm tau c3 ∈
      ii1Hering31LayerNormSubgroup z.m tau := by
    exact ⟨c3, hc3Pow, rfl⟩
  have hNormC3Z : ii1Hering31AbelianNorm tau c3 ∈
      Subgroup.zpowers d0 := by
    rw [← hNormT]
    exact hNormC3
  have hdFin : IsOfFinOrder d0 := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ z.m, pow_pos (by norm_num) _, hdPow⟩
  let ik : Fin (orderOf d0) :=
    (finEquivZPowers hdFin).symm
      ⟨ii1Hering31AbelianNorm tau c3, hNormC3Z⟩
  let k : ℕ := (ik : ℕ)
  have hkLt : k < 2 ^ z.m := by
    simpa [k, hdOrder] using ik.isLt
  have hkNorm : d0 ^ k = ii1Hering31AbelianNorm tau c3 := by
    simpa [ik, k] using pow_finEquivZPowers_symm_apply hdFin
      ⟨ii1Hering31AbelianNorm tau c3, hNormC3Z⟩
  have ht2 : tau c2 = c2⁻¹ * d0 := by
    simp [d0]
  have ht3 : tau c3 = c3⁻¹ * d0 ^ k := by
    rw [hkNorm]
    simp [ii1Hering31AbelianNorm]
  have hdTau : tau d0 = d0 := by
    simp [d0, map_mul, hTauSq]
    exact mul_comm c2 (tau c2)
  obtain ⟨x, hx⟩ := hcoords d0 hdPow
  let n1 := (x.toAdd 0).val
  let n2 := (x.toAdd 1).val
  let n3 := (x.toAdd 2).val
  have hparity := ii1Hering31_layer_coordinate_parities_of_top_v1 d z.m
    z.c1 c2 c3 d0 z.c1_top_eq hc2Top hc3Top n1 n2 n3
    (by simpa [n1, n2, n3] using hx)
    (by simpa [v1Q, v1] using hdTop)
  obtain ⟨⟨k1, hk1⟩, hk2div, hk3div⟩ := hparity
  obtain ⟨k2, hk2⟩ := hk2div
  obtain ⟨k3, hk3⟩ := hk3div
  let c1 : d.Q := z.c1 ^ (2 * k1 + 1)
  have hdEq : d0 = c1 * c2 ^ (2 * k2) * c3 ^ (2 * k3) := by
    rw [← hx]
    have hk1' : (x.toAdd 0).val = 2 * k1 + 1 := by
      simpa [n1] using hk1
    have hk2' : (x.toAdd 1).val = 2 * k2 := by
      simpa [n2] using hk2
    have hk3' : (x.toAdd 2).val = 2 * k3 := by
      simpa [n3] using hk3
    rw [hk1', hk2', hk3']
  have hN : 2 ^ z.m = 2 * 2 ^ (z.m - 1) := by
    have hmOne : 1 ≤ z.m := le_trans (by norm_num) z.m_ge_two
    calc
      2 ^ z.m = 2 ^ ((z.m - 1) + 1) := by
        exact congrArg (fun n : ℕ => 2 ^ n)
          (Nat.sub_add_cancel hmOne).symm
      _ = 2 * 2 ^ (z.m - 1) := by rw [pow_succ, Nat.mul_comm]
  have hk2Lt : k2 < 2 ^ (z.m - 1) := by
    have hn2Lt := ZMod.val_lt (x.toAdd 1)
    have hk2' : (x.toAdd 1).val = 2 * k2 := by
      simpa [n2] using hk2
    omega
  have hk3Lt : k3 < 2 ^ (z.m - 1) := by
    have hn3Lt := ZMod.val_lt (x.toAdd 2)
    have hk3' : (x.toAdd 2).val = 2 * k3 := by
      simpa [n3] using hk3
    omega
  have hc1Top : c1 ^ 2 ^ (z.m - 1) = v1Q := by
    change (z.c1 ^ (2 * k1 + 1)) ^ 2 ^ (z.m - 1) = v1Q
    rw [← pow_mul, Nat.mul_comm, pow_mul, z.c1_top_eq]
    rw [pow_add, pow_mul, hv1sq]
    simp [v1Q, v1]
  have hc1NewPow : c1 ^ 2 ^ z.m = 1 := by
    change (z.c1 ^ (2 * k1 + 1)) ^ 2 ^ z.m = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hc1Pow, one_pow]
  have hc1NewOrder : orderOf c1 = 2 ^ z.m :=
    ii1Hering31_order_eq_pow_two_of_top_ne_one z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) c1 hc1NewPow (by
        rw [hc1Top]
        exact hv1ne)
  have hRangeNew := d.layerCoordHom_range_eq_pow_ker z.m
    (lt_of_lt_of_le (by norm_num) z.m_ge_two) c1 c2 c3
    (by simpa [v1Q, v1] using hc1Top) hc2Top hc3Top
    hc1NewPow hc2Pow hc3Pow hc1NewOrder
  have ht1 : tau z.c1 = z.c1⁻¹ := by
    apply d.Q.subtype_injective
    simpa [tau, MulAut.conjNormal_apply] using hsStep5.2
  have ha1New : alpha c1 = c1⁻¹ := by
    calc
      alpha c1 = (alpha z.c1) ^ (2 * k1 + 1) := by simp [c1]
      _ = (z.c1⁻¹) ^ (2 * k1 + 1) := by rw [ha1]
      _ = c1⁻¹ := by simp [c1, inv_pow]
  have ht1New : tau c1 = c1⁻¹ := by
    calc
      tau c1 = (tau z.c1) ^ (2 * k1 + 1) := by simp [c1]
      _ = (z.c1⁻¹) ^ (2 * k1 + 1) := by rw [ht1]
      _ = c1⁻¹ := by simp [c1, inv_pow]
  have hb1 : beta z.c1 = z.c1 := by
    apply d.Q.subtype_injective
    change z.b * (z.c1 : X) * z.b⁻¹ = (z.c1 : X)
    rw [z.c1_eq]
    group
  have hb1New : beta c1 = c1 := by
    calc
      beta c1 = (beta z.c1) ^ (2 * k1 + 1) := by simp [c1]
      _ = c1 := by rw [hb1]
  have hStep7 := ii1Hering31_peterfalvi_step7 d hall z c2 c3
    hc2Top hc3Top hc1Pow hc2Pow hc3Pow hcoords hc2s hc3s
  have hNormB0 : ii1Hering31LayerNormSubgroup z.m beta =
      Subgroup.zpowers (z.c1 * v2Q) := by
    simpa [beta, v2Q, v2] using hStep7.2
  have hv2Half : v2Q ^ 2 ^ (z.m - 1) = 1 := by
    rw [show 2 ^ (z.m - 1) = 2 * 2 ^ (z.m - 2) by
      have hmTwo : 2 ≤ z.m := z.m_ge_two
      calc
        2 ^ (z.m - 1) = 2 ^ ((z.m - 2) + 1) := by
          exact congrArg (fun n : ℕ => 2 ^ n) (by omega)
        _ = 2 * 2 ^ (z.m - 2) := by rw [pow_succ]; omega]
    rw [pow_mul, hv2sq, one_pow]
  have hv2Pow : v2Q ^ 2 ^ z.m = 1 := by
    rw [hN, pow_mul, hv2sq, one_pow]
  have hcvPow : (z.c1 * v2Q) ^ 2 ^ z.m = 1 := by
    rw [mul_pow, hc1Pow, hv2Pow]
    simp
  have hcvTopNe : (z.c1 * v2Q) ^ 2 ^ (z.m - 1) ≠ 1 := by
    rw [mul_pow, z.c1_top_eq, hv2Half, mul_one]
    simpa [v1Q, v1] using hv1ne
  have hcvOrder : orderOf (z.c1 * v2Q) = 2 ^ z.m :=
    ii1Hering31_order_eq_pow_two_of_top_ne_one z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two)
      (z.c1 * v2Q) hcvPow hcvTopNe
  have hiOdd : Odd (2 * k1 + 1) := ⟨k1, rfl⟩
  have hicop : Nat.Coprime (2 * k1 + 1) (2 ^ z.m) :=
    (Odd.coprime_two_right hiOdd).pow_right z.m
  have hv2Odd : v2Q ^ (2 * k1 + 1) = v2Q := by
    rw [pow_add, pow_mul, hv2sq]
    simp
  have hcvPower : (z.c1 * v2Q) ^ (2 * k1 + 1) = c1 * v2Q := by
    rw [mul_pow, hv2Odd]
  have hcvZ : Subgroup.zpowers (c1 * v2Q) =
      Subgroup.zpowers (z.c1 * v2Q) := by
    rw [← hcvPower]
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.npow_mem_zpowers (z.c1 * v2Q) _
    · apply Subgroup.zpowers_le.mpr
      apply mem_zpowers_pow_iff.mpr
      simpa only [hcvOrder] using hicop.gcd_eq_one
  have hNormB : ii1Hering31LayerNormSubgroup z.m beta =
      Subgroup.zpowers (c1 * v2Q) := hNormB0.trans hcvZ.symm
  refine ⟨{
    c1 := c1
    d0 := d0
    k := k
    k2 := k2
    k3 := k3
    k_lt := hkLt
    k2_lt := hk2Lt
    k3_lt := hk3Lt
    c1_top_eq := by simpa [v1Q, v1] using hc1Top
    c1_pow_eq := hc1NewPow
    c1_order := hc1NewOrder
    coordinates := ?_
    c1_conj_s := by
      simpa [alpha, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype ha1New
    c1_conj_t := by
      simpa [tau, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype ht1New
    c1_conj_b := by
      simpa [beta, MulAut.conjNormal_apply] using
        congrArg d.Q.subtype hb1New
    c2_conj_s := hc2s
    c3_conj_s := hc3s
    c2_conj_t := by
      simpa [tau, MulAut.conjNormal_apply] using congrArg d.Q.subtype ht2
    c3_conj_t := by
      simpa [tau, MulAut.conjNormal_apply] using congrArg d.Q.subtype ht3
    d0_eq := hdEq
    d0_conj_t := by
      simpa [tau, MulAut.conjNormal_apply] using congrArg d.Q.subtype hdTau
    b_norm_eq := by
      simpa [beta, v2Q, v2] using hNormB }⟩
  intro q hq
  have hmem : q ∈ (powMonoidHom (2 ^ z.m) : d.Q →* d.Q).ker := hq
  rw [← hRangeNew] at hmem
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨y, ?_⟩
  rw [← hy]
  exact (ii1Hering31LayerCoordHom_apply d.Q_commutative z.m c1 c2 c3
    hc1NewPow hc2Pow hc3Pow y).symm

private def ii1Hering31PeterfalviSCoord {n : ℕ} (x : Fin 3 → ZMod n) :
    Fin 3 → ZMod n :=
  ![-x 0, x 1 + x 2, -x 2]

private def ii1Hering31PeterfalviTCoord {n : ℕ} (k k2 k3 : ℕ)
    (x : Fin 3 → ZMod n) : Fin 3 → ZMod n :=
  ![-x 0 + x 1 + (k : ZMod n) * x 2,
    ((2 * k2 : ℕ) : ZMod n) * x 1 - x 1 +
      ((2 * k * k2 : ℕ) : ZMod n) * x 2,
    ((2 * k3 : ℕ) : ZMod n) * x 1 +
      ((2 * k * k3 : ℕ) : ZMod n) * x 2 - x 2]

private def ii1Hering31PeterfalviDCoord {n : ℕ} (k2 k3 : ℕ) :
    Fin 3 → ZMod n :=
  ![1, ((2 * k2 : ℕ) : ZMod n), ((2 * k3 : ℕ) : ZMod n)]

private def ii1Hering31PeterfalviBCoord {n : ℕ} (k k2 k3 : ℕ)
    (x : Fin 3 → ZMod n) : Fin 3 → ZMod n :=
  ii1Hering31PeterfalviSCoord
    (ii1Hering31PeterfalviTCoord k k2 k3
      (ii1Hering31PeterfalviSCoord (ii1Hering31PeterfalviTCoord k k2 k3 x)))

private theorem ii1Hering31_peterfalvi_s_coord_intertwine
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (x : Fin 3 → ZMod (2 ^ z.m)) :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
    alpha (ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
      w.c1_pow_eq hc2Pow hc3Pow (Multiplicative.ofAdd x)) =
      ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
        w.c1_pow_eq hc2Pow hc3Pow
        (Multiplicative.ofAdd (ii1Hering31PeterfalviSCoord x)) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  have ha1 : alpha w.c1 = w.c1⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using w.c1_conj_s
  have ha2 : alpha c2 = c2 := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using w.c2_conj_s
  have ha3 : alpha c3 = c2 * c3⁻¹ := by
    apply d.Q.subtype_injective
    simpa [alpha, MulAut.conjNormal_apply] using w.c3_conj_s
  rw [ii1Hering31LayerCoordHom_apply, ii1Hering31LayerCoordHom_apply]
  change alpha (w.c1 ^ (x 0).val * c2 ^ (x 1).val * c3 ^ (x 2).val) =
    w.c1 ^ (-x 0).val * c2 ^ (x 1 + x 2).val * c3 ^ (-x 2).val
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, ha1, ha2, ha3]
  rw [ii1Hering31_pow_zmod_neg_val (2 ^ z.m) w.c1 w.c1_pow_eq (x 0),
    ii1Hering31_pow_zmod_add_val (2 ^ z.m) c2 hc2Pow (x 1) (x 2),
    ii1Hering31_pow_zmod_neg_val (2 ^ z.m) c3 hc3Pow (x 2)]
  rw [mul_pow]
  group

private theorem ii1Hering31_mul_reorder_nine {Q : Type*} [Group Q] [IsMulCommutative Q]
    (a b c d e f g h i : Q) :
    a * b * c * d * (e * f) * g * h * i =
      a * c * g * (b * d * h) * (e * (i * f)) := by
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  apply Additive.ofMul.injective
  change (Additive.ofMul a + Additive.ofMul b + Additive.ofMul c +
      Additive.ofMul d + (Additive.ofMul e + Additive.ofMul f) +
      Additive.ofMul g + Additive.ofMul h + Additive.ofMul i) =
    Additive.ofMul a + Additive.ofMul c + Additive.ofMul g +
      (Additive.ofMul b + Additive.ofMul d + Additive.ofMul h) +
      (Additive.ofMul e + (Additive.ofMul i + Additive.ofMul f))
  abel

private theorem ii1Hering31_peterfalvi_d_coord_apply
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1) :
    letI : IsMulCommutative d.Q := d.Q_commutative
    ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
      w.c1_pow_eq hc2Pow hc3Pow
      (Multiplicative.ofAdd (ii1Hering31PeterfalviDCoord w.k2 w.k3)) = w.d0 := by
  letI : IsMulCommutative d.Q := d.Q_commutative
  rw [ii1Hering31LayerCoordHom_apply]
  change w.c1 ^ (1 : ZMod (2 ^ z.m)).val *
      c2 ^ ((((2 * w.k2 : ℕ) : ZMod (2 ^ z.m))).val) *
      c3 ^ ((((2 * w.k3 : ℕ) : ZMod (2 ^ z.m))).val) = w.d0
  have hOne : w.c1 ^ (1 : ZMod (2 ^ z.m)).val = w.c1 := by
    rw [← ii1Hering31CyclicZModHom_apply (2 ^ z.m) w.c1 w.c1_pow_eq
      (1 : ZMod (2 ^ z.m))]
    exact congrArg Additive.toMul
      (ii1Hering31ZModPowerHom_one (2 ^ z.m) w.c1 w.c1_pow_eq)
  rw [hOne,
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c2 hc2Pow (2 * w.k2),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c3 hc3Pow (2 * w.k3)]
  simpa using w.d0_eq.symm

private theorem ii1Hering31_peterfalvi_t_coord_intertwine
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (x : Fin 3 → ZMod (2 ^ z.m)) :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let tau : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
    tau (ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
      w.c1_pow_eq hc2Pow hc3Pow (Multiplicative.ofAdd x)) =
      ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
        w.c1_pow_eq hc2Pow hc3Pow
        (Multiplicative.ofAdd
          (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3 x)) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let tau : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
  have ht1 : tau w.c1 = w.c1⁻¹ := by
    apply d.Q.subtype_injective
    simpa [tau, MulAut.conjNormal_apply] using w.c1_conj_t
  have ht2 : tau c2 = c2⁻¹ * w.d0 := by
    apply d.Q.subtype_injective
    simpa [tau, MulAut.conjNormal_apply] using w.c2_conj_t
  have ht3 : tau c3 = c3⁻¹ * w.d0 ^ w.k := by
    apply d.Q.subtype_injective
    simpa [tau, MulAut.conjNormal_apply] using w.c3_conj_t
  rw [ii1Hering31LayerCoordHom_apply, ii1Hering31LayerCoordHom_apply]
  change tau (w.c1 ^ (x 0).val * c2 ^ (x 1).val * c3 ^ (x 2).val) =
    w.c1 ^ (-x 0 + x 1 + (w.k : ZMod (2 ^ z.m)) * x 2).val *
      c2 ^ ((((2 * w.k2 : ℕ) : ZMod (2 ^ z.m)) * x 1 - x 1 +
        ((2 * w.k * w.k2 : ℕ) : ZMod (2 ^ z.m)) * x 2).val) *
      c3 ^ ((((2 * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 1 +
        ((2 * w.k * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 2 - x 2).val)
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, ht1, ht2, ht3]
  simp only [sub_eq_add_neg]
  rw [ii1Hering31_pow_zmod_add_val (2 ^ z.m) w.c1 w.c1_pow_eq
      (-x 0 + x 1) ((w.k : ZMod (2 ^ z.m)) * x 2),
    ii1Hering31_pow_zmod_add_val (2 ^ z.m) w.c1 w.c1_pow_eq (-x 0) (x 1),
    ii1Hering31_pow_zmod_neg_val (2 ^ z.m) w.c1 w.c1_pow_eq (x 0),
    ii1Hering31_pow_zmod_mul_val (2 ^ z.m) w.c1 w.c1_pow_eq
      (w.k : ZMod (2 ^ z.m)) (x 2),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) w.c1 w.c1_pow_eq w.k]
  rw [ii1Hering31_pow_zmod_add_val (2 ^ z.m) c2 hc2Pow
      (((2 * w.k2 : ℕ) : ZMod (2 ^ z.m)) * x 1 + -x 1)
      (((2 * w.k * w.k2 : ℕ) : ZMod (2 ^ z.m)) * x 2),
    ii1Hering31_pow_zmod_add_val (2 ^ z.m) c2 hc2Pow
      (((2 * w.k2 : ℕ) : ZMod (2 ^ z.m)) * x 1) (-x 1),
    ii1Hering31_pow_zmod_mul_val (2 ^ z.m) c2 hc2Pow
      ((2 * w.k2 : ℕ) : ZMod (2 ^ z.m)) (x 1),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c2 hc2Pow (2 * w.k2),
    ii1Hering31_pow_zmod_neg_val (2 ^ z.m) c2 hc2Pow (x 1),
    ii1Hering31_pow_zmod_mul_val (2 ^ z.m) c2 hc2Pow
      ((2 * w.k * w.k2 : ℕ) : ZMod (2 ^ z.m)) (x 2),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c2 hc2Pow (2 * w.k * w.k2)]
  rw [ii1Hering31_pow_zmod_add_val (2 ^ z.m) c3 hc3Pow
      (((2 * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 1 +
        ((2 * w.k * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 2) (-x 2),
    ii1Hering31_pow_zmod_add_val (2 ^ z.m) c3 hc3Pow
      (((2 * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 1)
      (((2 * w.k * w.k3 : ℕ) : ZMod (2 ^ z.m)) * x 2),
    ii1Hering31_pow_zmod_mul_val (2 ^ z.m) c3 hc3Pow
      ((2 * w.k3 : ℕ) : ZMod (2 ^ z.m)) (x 1),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c3 hc3Pow (2 * w.k3),
    ii1Hering31_pow_zmod_mul_val (2 ^ z.m) c3 hc3Pow
      ((2 * w.k * w.k3 : ℕ) : ZMod (2 ^ z.m)) (x 2),
    ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c3 hc3Pow (2 * w.k * w.k3),
    ii1Hering31_pow_zmod_neg_val (2 ^ z.m) c3 hc3Pow (x 2)]
  rw [w.d0_eq]
  simp_rw [mul_pow]
  group
  simp_rw [zpow_add]
  simp_rw [zpow_sub]
  rw [zpow_add]
  simpa only [mul_assoc] using
    (ii1Hering31_mul_reorder_nine (Q := d.Q)
      (w.c1 ^ (-((x 0).val : ℤ)))
      (c2 ^ (-((x 1).val : ℤ)))
      (w.c1 ^ ((x 1).val : ℤ))
      (c2 ^ (((x 1).val : ℤ) * w.k2 * 2))
      (c3 ^ (((x 1).val : ℤ) * w.k3 * 2))
      ((c3 ^ ((x 2).val : ℤ))⁻¹)
      (w.c1 ^ (((x 2).val : ℤ) * w.k))
      (c2 ^ (w.k2 * (x 2).val * (w.k : ℤ) * 2))
      (c3 ^ (w.k3 * (x 2).val * (w.k : ℤ) * 2)))

private theorem ii1Hering31_peterfalvi_b_coord_intertwine
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (x : Fin 3 → ZMod (2 ^ z.m)) :
    letI : d.Q.Normal := d.Q_normal
    letI : IsMulCommutative d.Q := d.Q_commutative
    letI : CommGroup d.Q := IsMulCommutative.instCommGroup
    let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
    beta (ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
      w.c1_pow_eq hc2Pow hc3Pow (Multiplicative.ofAdd x)) =
      ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
        w.c1_pow_eq hc2Pow hc3Pow
        (Multiplicative.ofAdd
          (ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 x)) := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let alpha : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.s
  let tau : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
  let coord := ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
    w.c1_pow_eq hc2Pow hc3Pow
  have hbeta (q : d.Q) : beta q = alpha (tau (alpha (tau q))) := by
    apply d.Q.subtype_injective
    change z.b * (q : X) * z.b⁻¹ =
      z.s * (z.t * (z.s * (z.t * (q : X) * z.t⁻¹) * z.s⁻¹) * z.t⁻¹) * z.s⁻¹
    rw [z.b_eq, z.a_eq]
    simp only [pow_two]
    group
  change beta (coord (Multiplicative.ofAdd x)) =
    coord (Multiplicative.ofAdd
      (ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 x))
  rw [hbeta]
  calc
    alpha (tau (alpha (tau (coord (Multiplicative.ofAdd x))))) =
        alpha (tau (alpha (coord
          (Multiplicative.ofAdd (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3 x))))) := by
      rw [ii1Hering31_peterfalvi_t_coord_intertwine]
    _ = alpha (tau (coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviSCoord
            (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3 x))))) := by
      rw [ii1Hering31_peterfalvi_s_coord_intertwine]
    _ = alpha (coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3
            (ii1Hering31PeterfalviSCoord
              (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3 x))))) := by
      rw [ii1Hering31_peterfalvi_t_coord_intertwine]
    _ = coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviSCoord
            (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3
              (ii1Hering31PeterfalviSCoord
                (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3 x))))) := by
      rw [ii1Hering31_peterfalvi_s_coord_intertwine]
    _ = coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 x)) := rfl

private theorem ii1Hering31_peterfalvi_b_norm_coordinate_relation
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (x : Fin 3 → ZMod (2 ^ z.m)) :
    let y := fun i => ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 x i + x i
    y 1 = ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0 := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let beta : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.b
  let coord := ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
    w.c1_pow_eq hc2Pow hc3Pow
  let y : Fin 3 → ZMod (2 ^ z.m) := fun i =>
    ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 x i + x i
  let g : Fin 3 → ZMod (2 ^ z.m) :=
    ![1, ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)), 0]
  have hinj : Function.Injective coord :=
    II1Hering31AbelianExtensionData.layerCoordHom_injective d z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) w.c1 c2 c3
      w.c1_top_eq hc2Top hc3Top w.c1_pow_eq hc2Pow hc3Pow
  have hqPow : (coord (Multiplicative.ofAdd x)) ^ 2 ^ z.m = 1 := by
    rw [ii1Hering31LayerCoordHom_apply]
    rw [mul_pow, mul_pow]
    have hpow (c : d.Q) (hc : c ^ 2 ^ z.m = 1) (a : ℕ) :
        (c ^ a) ^ 2 ^ z.m = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hc, one_pow]
    rw [hpow w.c1 w.c1_pow_eq, hpow c2 hc2Pow, hpow c3 hc3Pow]
    simp
  have hmem : beta (coord (Multiplicative.ofAdd x)) *
      coord (Multiplicative.ofAdd x) ∈
      ii1Hering31LayerNormSubgroup z.m beta := by
    exact ⟨coord (Multiplicative.ofAdd x), hqPow, rfl⟩
  have hmemZ : beta (coord (Multiplicative.ofAdd x)) *
      coord (Multiplicative.ofAdd x) ∈
      Subgroup.zpowers
        (w.c1 * ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
          d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩) := by
    rw [← w.b_norm_eq]
    exact hmem
  have hOne : w.c1 ^ (1 : ZMod (2 ^ z.m)).val = w.c1 := by
    rw [← ii1Hering31CyclicZModHom_apply (2 ^ z.m) w.c1 w.c1_pow_eq
      (1 : ZMod (2 ^ z.m))]
    exact congrArg Additive.toMul
      (ii1Hering31ZModPowerHom_one (2 ^ z.m) w.c1 w.c1_pow_eq)
  have hgen : coord (Multiplicative.ofAdd g) =
      w.c1 * ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩ := by
    rw [ii1Hering31LayerCoordHom_apply]
    change w.c1 ^ (1 : ZMod (2 ^ z.m)).val *
      c2 ^ ((((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m))).val) *
      c3 ^ (0 : ZMod (2 ^ z.m)).val = _
    rw [hOne,
      ii1Hering31_pow_zmod_natCast_val (2 ^ z.m) c2 hc2Pow (2 ^ (z.m - 1)),
      ZMod.val_zero, pow_zero, mul_one, hc2Top]
  have hnormCoord : beta (coord (Multiplicative.ofAdd x)) *
      coord (Multiplicative.ofAdd x) = coord (Multiplicative.ofAdd y) := by
    rw [ii1Hering31_peterfalvi_b_coord_intertwine]
    rw [← map_mul]
    rfl
  rw [← hgen] at hmemZ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmemZ
  rw [hnormCoord] at hj
  have hmap : coord ((Multiplicative.ofAdd g) ^ j) =
      coord (Multiplicative.ofAdd y) := by
    rw [map_zpow]
    exact hj
  have hvecMul : (Multiplicative.ofAdd g) ^ j =
      Multiplicative.ofAdd y := hinj hmap
  have hvec : j • g = y := by
    simpa using congrArg Multiplicative.toAdd hvecMul
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  have h0' : (j : ZMod (2 ^ z.m)) * 1 = y 0 := by
    simpa [g] using h0
  have h1' : (j : ZMod (2 ^ z.m)) *
      ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) = y 1 := by
    simpa [g] using h1
  change y 1 = ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0
  rw [← h1', ← h0']
  ring

private theorem ii1Hering31_zmod_two_mul_eq_zero_to_half
    (m : ℕ) (hm : 0 < m) (a : ℤ)
    (h : ((2 * a : ℤ) : ZMod (2 ^ m)) = 0) :
    (a : ZMod (2 ^ (m - 1))) = 0 := by
  have hmOne : 1 ≤ m := hm
  have hPowNat : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by
        exact congrArg (fun n : ℕ => 2 ^ n) (Nat.sub_add_cancel hmOne).symm
      _ = 2 * 2 ^ (m - 1) := by rw [pow_succ, Nat.mul_comm]
  have hPowInt : (2 ^ m : ℤ) = 2 * (2 ^ (m - 1) : ℤ) := by
    exact_mod_cast hPowNat
  have hdiv : (2 ^ m : ℤ) ∣ 2 * a :=
    (CharP.intCast_eq_zero_iff (ZMod (2 ^ m)) (2 ^ m) (2 * a)).mp h
  rw [hPowInt] at hdiv
  have haDiv : (2 ^ (m - 1) : ℤ) ∣ a :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hdiv
  exact (CharP.intCast_eq_zero_iff
    (ZMod (2 ^ (m - 1))) (2 ^ (m - 1)) a).mpr haDiv

private theorem ii1Hering31_peterfalvi_91
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1) :
    (w.k2 : ZMod (2 ^ (z.m - 1))) +
        (w.k : ZMod (2 ^ (z.m - 1))) *
          (w.k3 : ZMod (2 ^ (z.m - 1))) - 1 = 0 := by
  letI : d.Q.Normal := d.Q_normal
  letI : IsMulCommutative d.Q := d.Q_commutative
  letI : CommGroup d.Q := IsMulCommutative.instCommGroup
  let tau : MulAut d.Q := MulAut.conjNormal (H := d.Q) z.t
  let coord := ii1Hering31LayerCoordHom d.Q_commutative z.m w.c1 c2 c3
    w.c1_pow_eq hc2Pow hc3Pow
  have hinj : Function.Injective coord :=
    II1Hering31AbelianExtensionData.layerCoordHom_injective d z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) w.c1 c2 c3
      w.c1_top_eq hc2Top hc3Top w.c1_pow_eq hc2Pow hc3Pow
  have htauD : tau w.d0 = w.d0 := by
    apply d.Q.subtype_injective
    simpa [tau, MulAut.conjNormal_apply] using w.d0_conj_t
  have hcoord :
      coord (Multiplicative.ofAdd
        (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3
          (ii1Hering31PeterfalviDCoord w.k2 w.k3))) =
        coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviDCoord w.k2 w.k3)) := by
    calc
      coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviTCoord w.k w.k2 w.k3
            (ii1Hering31PeterfalviDCoord w.k2 w.k3))) =
          tau (coord (Multiplicative.ofAdd
            (ii1Hering31PeterfalviDCoord w.k2 w.k3))) := by
        symm
        exact ii1Hering31_peterfalvi_t_coord_intertwine d z c2 c3 w
          hc2Pow hc3Pow (ii1Hering31PeterfalviDCoord w.k2 w.k3)
      _ = tau w.d0 := congrArg tau
        (ii1Hering31_peterfalvi_d_coord_apply d z c2 c3 w hc2Pow hc3Pow)
      _ = w.d0 := htauD
      _ = coord (Multiplicative.ofAdd
          (ii1Hering31PeterfalviDCoord w.k2 w.k3)) :=
        (ii1Hering31_peterfalvi_d_coord_apply d z c2 c3 w hc2Pow hc3Pow).symm
  have hvec := congrArg Multiplicative.toAdd (hinj hcoord)
  have h0 := congrFun hvec 0
  have hdouble' :
      (2 : ZMod (2 ^ z.m)) *
        ((w.k2 : ZMod (2 ^ z.m)) +
          (w.k : ZMod (2 ^ z.m)) * (w.k3 : ZMod (2 ^ z.m)) - 1) = 0 := by
    simp [ii1Hering31PeterfalviTCoord, ii1Hering31PeterfalviDCoord] at h0
    linear_combination h0
  have hdouble :
      (((2 : ℤ) * ((w.k2 : ℤ) + w.k * w.k3 - 1) : ℤ) :
        ZMod (2 ^ z.m)) = 0 := by
    push_cast
    exact hdouble'
  have hhalf := ii1Hering31_zmod_two_mul_eq_zero_to_half z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two)
      ((w.k2 : ℤ) + w.k * w.k3 - 1) hdouble
  simpa using hhalf

private def ii1Hering31PeterfalviE2 {n : ℕ} : Fin 3 → ZMod n := ![0, 1, 0]

private def ii1Hering31PeterfalviE3 {n : ℕ} : Fin 3 → ZMod n := ![0, 0, 1]

private theorem ii1Hering31_peterfalvi_e2_norm_coords
    (n k k2 k3 : ℕ) :
    let y := fun i =>
      ii1Hering31PeterfalviBCoord (n := n) k k2 k3 ii1Hering31PeterfalviE2 i +
        ii1Hering31PeterfalviE2 i
    y 0 = 2 * ((k : ZMod n) * k3 - k2 - k3) ∧
    y 1 = 2 *
      (((2 : ZMod n) * (k2 + k3) - 1) * (2 * k2 + k3 - 1) -
        2 * (k2 + k3) * (k2 + (k : ZMod n) * k3 - 1)) := by
  dsimp
  constructor <;>
    simp [ii1Hering31PeterfalviE2, ii1Hering31PeterfalviBCoord,
      ii1Hering31PeterfalviSCoord, ii1Hering31PeterfalviTCoord] <;>
    ring

private theorem ii1Hering31_peterfalvi_e3_norm_coords
    (n k k2 k3 : ℕ) :
    let y := fun i =>
      ii1Hering31PeterfalviBCoord (n := n) k k2 k3 ii1Hering31PeterfalviE3 i +
        ii1Hering31PeterfalviE3 i
    y 0 = 1 + 2 *
      ((k : ZMod n) * k * k3 - (k : ZMod n) * k2 -
        (k : ZMod n) * k3 - k) ∧
    y 1 = 2 *
      (2 * (k : ZMod n) * (k2 + k3) - 1) *
        (k2 + k3 - (k : ZMod n) * k3) := by
  dsimp
  constructor <;>
    simp [ii1Hering31PeterfalviE3, ii1Hering31PeterfalviBCoord,
      ii1Hering31PeterfalviSCoord, ii1Hering31PeterfalviTCoord] <;>
    ring

private theorem ii1Hering31_zmod_two_mul_sub_one_isUnit
    (m : ℕ) (a : ZMod (2 ^ m)) : IsUnit (2 * a - 1) := by
  apply IsNilpotent.isUnit_sub_one
  refine ⟨m, ?_⟩
  rw [mul_pow]
  change (((2 : ℕ) : ZMod (2 ^ m)) ^ m) * a ^ m = 0
  rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private theorem ii1Hering31_zmod_top_mul_two_eq_zero
    (m : ℕ) (hm : 0 < m) (a : ZMod (2 ^ m)) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * (2 * a) = 0 := by
  have hmOne : 1 ≤ m := hm
  have hpow : 2 ^ (m - 1) * 2 = 2 ^ m := by
    calc
      2 ^ (m - 1) * 2 = 2 ^ ((m - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ m := by rw [Nat.sub_add_cancel hmOne]
  calc
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * (2 * a) =
        ((2 ^ (m - 1) * 2 : ℕ) : ZMod (2 ^ m)) * a := by
      push_cast
      ring
    _ = ((2 ^ m : ℕ) : ZMod (2 ^ m)) * a := by rw [hpow]
    _ = 0 := by rw [ZMod.natCast_self, zero_mul]

private theorem ii1Hering31_zmod_odd_factor_fix_half
    (m : ℕ) (hm : 2 ≤ m) (a : ZMod (2 ^ (m - 1))) :
    (2 * a - 1) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m - 1))) =
      ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m - 1))) := by
  have hzero := ii1Hering31_zmod_top_mul_two_eq_zero (m - 1) (by omega)
    (1 : ZMod (2 ^ (m - 1)))
  have hzero' :
      ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m - 1))) * 2 = 0 := by
    simpa [Nat.sub_sub] using hzero
  linear_combination (a - 1) * hzero'

private theorem ii1Hering31_zmod_two_mul_quarter_eq_top
    (m : ℕ) (hm : 2 ≤ m) :
    (2 : ZMod (2 ^ m)) *
        ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have hpow : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    calc
      2 * 2 ^ (m - 2) = 2 ^ ((m - 2) + 1) := by
        rw [pow_succ, Nat.mul_comm]
      _ = 2 ^ (m - 1) := by
        congr 1
        omega
  change (((2 : ℕ) : ZMod (2 ^ m)) *
      ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) = _
  rw [← Nat.cast_mul, hpow]

private theorem ii1Hering31_peterfalvi_92
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1)
    (h91 : (w.k2 : ZMod (2 ^ (z.m - 1))) +
      (w.k : ZMod (2 ^ (z.m - 1))) *
        (w.k3 : ZMod (2 ^ (z.m - 1))) - 1 = 0) :
    (w.k3 : ZMod (2 ^ (z.m - 1))) =
      1 - 2 * (w.k2 : ZMod (2 ^ (z.m - 1))) := by
  let y : Fin 3 → ZMod (2 ^ z.m) := fun i =>
    ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 ii1Hering31PeterfalviE2 i +
      ii1Hering31PeterfalviE2 i
  have hnorm := ii1Hering31_peterfalvi_b_norm_coordinate_relation d z c2 c3 w
    hc2Top hc3Top hc2Pow hc3Pow ii1Hering31PeterfalviE2
  change y 1 = ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0 at hnorm
  have hcoords := ii1Hering31_peterfalvi_e2_norm_coords
    (2 ^ z.m) w.k w.k2 w.k3
  change y 0 = _ ∧ y 1 = _ at hcoords
  have hrhs :
      ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0 = 0 := by
    rw [hcoords.1]
    exact ii1Hering31_zmod_top_mul_two_eq_zero z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two) _
  have hy1 : y 1 = 0 := hnorm.trans hrhs
  rw [hcoords.2] at hy1
  let e : ℤ :=
    (2 * ((w.k2 : ℤ) + w.k3) - 1) *
        (2 * (w.k2 : ℤ) + w.k3 - 1) -
      2 * ((w.k2 : ℤ) + w.k3) *
        ((w.k2 : ℤ) + w.k * w.k3 - 1)
  have hdouble : (((2 * e : ℤ) : ZMod (2 ^ z.m))) = 0 := by
    push_cast
    simpa [e] using hy1
  have he := ii1Hering31_zmod_two_mul_eq_zero_to_half z.m
    (lt_of_lt_of_le (by norm_num) z.m_ge_two) e hdouble
  have he' :
      ((2 : ZMod (2 ^ (z.m - 1))) * (w.k2 + w.k3) - 1) *
          (2 * w.k2 + w.k3 - 1) -
        2 * (w.k2 + w.k3) * (w.k2 + w.k * w.k3 - 1) = 0 := by
    simpa [e] using he
  have hprod :
      ((2 : ZMod (2 ^ (z.m - 1))) * (w.k2 + w.k3) - 1) *
        (2 * w.k2 + w.k3 - 1) = 0 := by
    linear_combination he' + 2 * (w.k2 + w.k3) * h91
  have hu : IsUnit
      ((2 : ZMod (2 ^ (z.m - 1))) * (w.k2 + w.k3) - 1) := by
    exact ii1Hering31_zmod_two_mul_sub_one_isUnit (z.m - 1) (w.k2 + w.k3)
  have hfactor :
      (2 : ZMod (2 ^ (z.m - 1))) * w.k2 + w.k3 - 1 = 0 :=
    hu.mul_right_eq_zero.mp hprod
  linear_combination hfactor

private theorem ii1Hering31_peterfalvi_93
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1) :
    (w.k2 : ZMod (2 ^ (z.m - 1))) + w.k3 - w.k * w.k3 =
      ((2 ^ (z.m - 2) : ℕ) : ZMod (2 ^ (z.m - 1))) := by
  let y : Fin 3 → ZMod (2 ^ z.m) := fun i =>
    ii1Hering31PeterfalviBCoord w.k w.k2 w.k3 ii1Hering31PeterfalviE3 i +
      ii1Hering31PeterfalviE3 i
  have hnorm := ii1Hering31_peterfalvi_b_norm_coordinate_relation d z c2 c3 w
    hc2Top hc3Top hc2Pow hc3Pow ii1Hering31PeterfalviE3
  change y 1 = ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0 at hnorm
  have hcoords := ii1Hering31_peterfalvi_e3_norm_coords
    (2 ^ z.m) w.k w.k2 w.k3
  change y 0 = _ ∧ y 1 = _ at hcoords
  have hrhs :
      ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) * y 0 =
        ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) := by
    rw [hcoords.1]
    have hzero := ii1Hering31_zmod_top_mul_two_eq_zero z.m
      (lt_of_lt_of_le (by norm_num) z.m_ge_two)
      ((w.k : ZMod (2 ^ z.m)) * w.k * w.k3 - w.k * w.k2 -
        w.k * w.k3 - w.k)
    linear_combination hzero
  have hy1 : y 1 =
      ((2 ^ (z.m - 1) : ℕ) : ZMod (2 ^ z.m)) := hnorm.trans hrhs
  rw [hcoords.2] at hy1
  let e : ℤ :=
    (2 * (w.k : ℤ) * ((w.k2 : ℤ) + w.k3) - 1) *
      ((w.k2 : ℤ) + w.k3 - w.k * w.k3)
  have hzero :
      (((2 * (e - (2 ^ (z.m - 2) : ℕ)) : ℤ) :
        ZMod (2 ^ z.m))) = 0 := by
    have hquarter := ii1Hering31_zmod_two_mul_quarter_eq_top z.m z.m_ge_two
    dsimp [e]
    push_cast at hy1 hquarter ⊢
    linear_combination hy1 - hquarter
  have he := ii1Hering31_zmod_two_mul_eq_zero_to_half z.m
    (lt_of_lt_of_le (by norm_num) z.m_ge_two)
    (e - (2 ^ (z.m - 2) : ℕ)) hzero
  have hfactor :
      (2 * w.k * (w.k2 + w.k3) - 1) *
          (w.k2 + w.k3 - w.k * w.k3) =
        ((2 ^ (z.m - 2) : ℕ) : ZMod (2 ^ (z.m - 1))) := by
    have he' :
        (2 * w.k * (w.k2 + w.k3) - 1) *
            (w.k2 + w.k3 - w.k * w.k3) -
          ((2 ^ (z.m - 2) : ℕ) : ZMod (2 ^ (z.m - 1))) = 0 := by
      simpa [e] using he
    exact sub_eq_zero.mp he'
  have hu : IsUnit
      ((2 : ZMod (2 ^ (z.m - 1))) * w.k * (w.k2 + w.k3) - 1) := by
    simpa [mul_assoc] using ii1Hering31_zmod_two_mul_sub_one_isUnit (z.m - 1)
      ((w.k : ZMod (2 ^ (z.m - 1))) * (w.k2 + w.k3))
  apply hu.mul_right_inj.mp
  calc
    ((2 : ZMod (2 ^ (z.m - 1))) * w.k * (w.k2 + w.k3) - 1) *
          (w.k2 + w.k3 - w.k * w.k3) =
        ((2 ^ (z.m - 2) : ℕ) : ZMod (2 ^ (z.m - 1))) := hfactor
    _ = ((2 : ZMod (2 ^ (z.m - 1))) * w.k * (w.k2 + w.k3) - 1) *
        ((2 ^ (z.m - 2) : ℕ) : ZMod (2 ^ (z.m - 1))) := by
      symm
      simpa [mul_assoc] using ii1Hering31_zmod_odd_factor_fix_half z.m z.m_ge_two
        ((w.k : ZMod (2 ^ (z.m - 1))) * (w.k2 + w.k3))


/-- The final arithmetic contradiction in Peterfalvi IV.3, equations
`(9.1)`--`(9.3)`. -/
public theorem ii1Hering31_peterfalvi_final_congruence
    (m : ℕ) (hm : 2 ≤ m)
    (k k2 k3 : ZMod (2 ^ (m - 1)))
    (h91 : k2 + k * k3 - 1 = 0)
    (h92 : k3 = 1 - 2 * k2)
    (h93 : k2 + k3 - k * k3 = (2 ^ (m - 2) : ℕ)) : False := by
  have hkk3 : k * k3 = 1 - k2 := by
    linear_combination h91
  have hzero : k2 + k3 - k * k3 = 0 := by
    rw [hkk3, h92]
    ring
  have hcast : ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ (m - 1))) = 0 := by
    rw [← h93, hzero]
  rw [ZMod.natCast_eq_zero_iff] at hcast
  have hle : m - 1 ≤ m - 2 :=
    (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hcast
  omega

/-- Peterfalvi IV.3, step 9: the normalized layer relations force the
three incompatible congruences `(9.1)`--`(9.3)`. -/
private theorem ii1Hering31_peterfalvi_step9_false
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X)
    (z : II1Hering31PeterfalviInitialData d) (c2 c3 : d.Q)
    (w : II1Hering31PeterfalviStep8Data d z c2 c3)
    (hc2Top : c2 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV2 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV2).property⟩)
    (hc3Top : c3 ^ 2 ^ (z.m - 1) =
      ⟨((d.V_coord.symm ii1Hering31AbelianV3 : d.V) : X),
        d.V_le_Q (d.V_coord.symm ii1Hering31AbelianV3).property⟩)
    (hc2Pow : c2 ^ 2 ^ z.m = 1) (hc3Pow : c3 ^ 2 ^ z.m = 1) : False := by
  have h91 := ii1Hering31_peterfalvi_91 d z c2 c3 w
    hc2Top hc3Top hc2Pow hc3Pow
  have h92 := ii1Hering31_peterfalvi_92 d z c2 c3 w
    hc2Top hc3Top hc2Pow hc3Pow h91
  have h93 := ii1Hering31_peterfalvi_93 d z c2 c3 w
    hc2Top hc3Top hc2Pow hc3Pow
  exact ii1Hering31_peterfalvi_final_congruence z.m z.m_ge_two
    w.k w.k2 w.k3 h91 h92 h93

/-- Peterfalvi IV.3: every finite abelian Hering extension contains an
involution outside its abelian kernel. -/
public theorem II1Hering31AbelianExtensionData.exists_involution_not_mem
    {X : Type u} [Group X] [Finite X]
    (d : II1Hering31AbelianExtensionData X) :
    ∃ y : X, IsInvolution y ∧ y ∉ d.Q := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ {Y : Type u} [Group Y] [Finite Y], Nat.card Y = n →
      ∀ dY : II1Hering31AbelianExtensionData Y,
        ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y _ _ hcard dY
        by_cases hex : ∃ y : Y, IsInvolution y ∧ y ∉ dY.Q
        · exact hex
        · have hall : ∀ y : Y, IsInvolution y → y ∈ dY.Q := by
            intro y hy
            by_contra hyQ
            exact hex ⟨y, hy, hyQ⟩
          have ihY : ∀ {Z : Type u} [Group Z] [Finite Z],
              Nat.card Z < Nat.card Y →
              ∀ dZ : II1Hering31AbelianExtensionData Z,
                ∃ z : Z, IsInvolution z ∧ z ∉ dZ.Q := by
            intro Z _ _ hZY dZ
            have hZn : Nat.card Z < n := by simpa [hcard] using hZY
            exact ih (Nat.card Z) hZn rfl dZ
          obtain ⟨z⟩ := dY.exists_peterfalvi_initial_data hall ihY
          obtain ⟨l⟩ := z.exists_peterfalvi_layer_data dY
          obtain ⟨w⟩ := ii1Hering31_peterfalvi_step8 dY hall z l.c2 l.c3
            l.c2_top_eq l.c3_top_eq l.c1_pow_eq l.c2_pow_eq l.c3_pow_eq
            l.coordinates l.c2_conj_s l.c3_conj_s
          exact (ii1Hering31_peterfalvi_step9_false dY z l.c2 l.c3 w
            l.c2_top_eq l.c3_top_eq l.c2_pow_eq l.c3_pow_eq).elim
  exact hP (Nat.card X) rfl d

end CFSG.BenderSuzuki
