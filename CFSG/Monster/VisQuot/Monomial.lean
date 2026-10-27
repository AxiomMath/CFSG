module

public import CFSG.Monster.Visible.FrameStab
public import CFSG.Monster.VisCert.FrameData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert Matrix
open scoped commutatorElement

theorem modTwoHom_eq_op (g : latticeO) : modTwoHom g = MulOpposite.op (modTwoUnit g) := rfl

theorem modTwoUnit_mul (g k : latticeO) : modTwoUnit (g * k) = modTwoUnit k * modTwoUnit g :=
  Units.ext (modTwoEnd_mul g k)

theorem modTwoUnit_one : modTwoUnit 1 = 1 := Units.ext modTwoEnd_one

theorem modTwoUnit_inv (g : latticeO) : modTwoUnit g⁻¹ = (modTwoUnit g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← modTwoUnit_mul, mul_inv_cancel, modTwoUnit_one])

theorem mem_zpowers_negOneO_iff (g : latticeO) :
    g ∈ Subgroup.zpowers negOneO ↔ g = 1 ∨ g = negOneO := by
  rw [zpowers_negOneO_eq_ker, ← SetLike.mem_coe, coe_ker_modTwoHom, Set.mem_insert_iff,
    Set.mem_singleton_iff]

theorem modTwoUnit_eq_one_iff (g : latticeO) : modTwoUnit g = 1 ↔ g = 1 ∨ g = negOneO := by
  rw [← mem_zpowers_negOneO_iff, zpowers_negOneO_eq_ker, MonoidHom.mem_ker, modTwoHom_eq_op,
    MulOpposite.op_eq_one_iff]

theorem modTwoUnit_eq_modTwoUnit_iff (g k : latticeO) :
    modTwoUnit g = modTwoUnit k ↔ g = k ∨ g = negOneO * k := by
  have e : modTwoUnit g = modTwoUnit k ↔ modTwoUnit (g * k⁻¹) = 1 := by
    rw [modTwoUnit_mul, modTwoUnit_inv, inv_mul_eq_one, eq_comm]
  rw [e, modTwoUnit_eq_one_iff, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

@[expose] def ΩC : C := ⟨Ω, Ω_mem_C⟩

theorem PO_mul (p q : AutPerm) : PO (p * q) = PO q * PO p :=
  mat_injective (Pmat_mul (q : Equiv.Perm (Fin 24)) p)

theorem PO_one : PO 1 = 1 := mat_injective (Matrix.permMatrix_one (n := Fin 24) (R := ℚ))

theorem PO_inv (p : AutPerm) : PO p⁻¹ = (PO p)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← PO_mul, mul_inv_cancel, PO_one])

theorem gmat_ΩC : gmat ΩC = -1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [gmat, ΩC, Ω, sgn]
  · simp [gmat, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem gO_ΩC : gO ΩC = negOneO := mat_injective (by rw [mat_gO, mat_negOneO, gmat_ΩC])

theorem negOneO_mul_comm (g : latticeO) : negOneO * g = g * negOneO :=
  mat_injective (by rw [mat_mul, mat_mul, mat_negOneO, neg_one_mul, mul_neg_one])

theorem single_vecMul_gmat_Pmat (a : C) (p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    Pi.single i 1 ᵥ* (gmat a * Pmat p) = sgn ((a : Fin 24 → ZMod 2) i) • Pi.single (p i) 1 := by
  rw [← vecMul_vecMul, single_vecMul_gmat, smul_vecMul, single_vecMul_Pmat]

private theorem sgn_inj {s t : ZMod 2} (h : sgn s = sgn t) : s = t := by
  have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
  · rfl
  · norm_num [sgn] at h
  · norm_num [sgn] at h
  · rfl

theorem gmat_mul_Pmat_inj {a b : C} {p q : Equiv.Perm (Fin 24)}
    (h : gmat a * Pmat p = gmat b * Pmat q) : a = b ∧ p = q := by
  have hrow : ∀ i, sgn ((a : Fin 24 → ZMod 2) i) • (Pi.single (p i) 1 : Fin 24 → ℚ) =
      sgn ((b : Fin 24 → ZMod 2) i) • Pi.single (q i) 1 := fun i => by
    rw [← single_vecMul_gmat_Pmat, ← single_vecMul_gmat_Pmat, h]
  have hpq : ∀ i, p i = q i := by
    intro i
    by_contra hne
    have := congrFun (hrow i) (p i)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Pi.single_eq_of_ne hne, mul_zero] at this
    exact sgn_ne_zero' _ this
  have hab : ∀ i, (a : Fin 24 → ZMod 2) i = (b : Fin 24 → ZMod 2) i := by
    intro i
    have := congrFun (hrow i) (p i)
    rw [hpq i] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    exact sgn_inj this
  exact ⟨Subtype.ext (funext hab), Equiv.ext hpq⟩

theorem gO_mul_PO_inj {a b : C} {p q : AutPerm} (h : gO a * PO p = gO b * PO q) :
    a = b ∧ p = q := by
  have h' := gmat_mul_Pmat_inj (a := a) (b := b) (p := p) (q := q) (congrArg mat h)
  exact ⟨h'.1, Subtype.ext h'.2⟩

theorem gO_mul_PO (a : C) (p : AutPerm) : gO a * PO p = PO p * gO (permC p a) := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_gO, mat_gO, mat_PO]
  refine Matrix.ext_of_single_vecMul fun i => ?_
  rw [single_vecMul_gmat_Pmat, ← vecMul_vecMul, single_vecMul_Pmat, single_vecMul_gmat, coe_permC,
    permWord_apply]

theorem PO_mul_gO (p : AutPerm) (a : C) : PO p * gO a = gO ((permC p).symm a) * PO p := by
  rw [gO_mul_PO, LinearEquiv.apply_symm_apply]

theorem PO_inv_mul_gO_mul_PO (p : AutPerm) (a : C) : (PO p)⁻¹ * gO a * PO p = gO (permC p a) := by
  rw [mul_assoc, gO_mul_PO, inv_mul_cancel_left]

theorem permC_ΩC (p : AutPerm) : permC p ΩC = ΩC := Subtype.ext rfl

theorem eq_of_gO_mul_PO_scalar {a : C} {p : AutPerm} (h : gO a * PO p = 1 ∨ gO a * PO p = negOneO) :
    p = 1 ∧ (a = 0 ∨ a = ΩC) := by
  rcases h with h | h
  · have h1 : gO a * PO p = gO 0 * PO 1 := by rw [h, gO_zero, PO_one, mul_one]
    obtain ⟨ha, hp⟩ := gO_mul_PO_inj h1
    exact ⟨hp, .inl ha⟩
  · have h1 : gO a * PO p = gO ΩC * PO 1 := by rw [h, gO_ΩC, PO_one, mul_one]
    obtain ⟨ha, hp⟩ := gO_mul_PO_inj h1
    exact ⟨hp, .inr ha⟩

@[expose] def permHom : AutPerm →* GLV where
  toFun p := modTwoUnit (PO p)
  map_one' := by rw [PO_one, modTwoUnit_one]
  map_mul' p q := by rw [PO_mul, modTwoUnit_mul]

theorem permHom_apply (p : AutPerm) : permHom p = modTwoUnit (PO p) := rfl

@[expose] def ΩLine : Submodule (ZMod 2) C := Submodule.span (ZMod 2) {ΩC}

theorem mem_ΩLine_iff {a : C} : a ∈ ΩLine ↔ a = 0 ∨ a = ΩC := by
  rw [ΩLine, Submodule.mem_span_singleton]
  have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  constructor
  · rintro ⟨s, rfl⟩
    rcases hs s with rfl | rfl
    · exact .inl (zero_smul _ _)
    · exact .inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem ΩC_mem_ΩLine : ΩC ∈ ΩLine := mem_ΩLine_iff.2 (.inr rfl)

theorem map_permC_ΩLine (p : AutPerm) : ΩLine.map (permC p : C →ₗ[ZMod 2] C) = ΩLine := by
  rw [ΩLine, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun x => Submodule.span (ZMod 2) {x}) (permC_ΩC p)

@[expose] def permQ (p : AutPerm) : (C ⧸ ΩLine) ≃ₗ[ZMod 2] (C ⧸ ΩLine) :=
  Submodule.Quotient.equiv ΩLine ΩLine (permC p) (map_permC_ΩLine p)

theorem permQ_mk (p : AutPerm) (a : C) :
    permQ p (Submodule.Quotient.mk a) = Submodule.Quotient.mk (permC p a) := rfl

theorem permC_one (a : C) : permC 1 a = a := Subtype.ext rfl

theorem permC_mul (p q : AutPerm) (a : C) : permC (p * q) a = permC p (permC q a) :=
  Subtype.ext (permWord_mul (q : Equiv.Perm (Fin 24)) p a)

@[expose] def permAct : AutPerm →* MulAut (Multiplicative (C ⧸ ΩLine)) where
  toFun p := AddEquiv.toMultiplicative (permQ p).toAddEquiv
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using Multiplicative.rec with
    | ofAdd x =>
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        show Multiplicative.ofAdd (permQ 1 (Submodule.Quotient.mk a)) =
          Multiplicative.ofAdd (Submodule.Quotient.mk a)
        rw [permQ_mk, permC_one]
  map_mul' p q := by
    refine MulEquiv.ext fun x => ?_
    induction x using Multiplicative.rec with
    | ofAdd x =>
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        show Multiplicative.ofAdd (permQ (p * q) (Submodule.Quotient.mk a)) =
          Multiplicative.ofAdd (permQ p (permQ q (Submodule.Quotient.mk a)))
        rw [permQ_mk, permQ_mk, permQ_mk, permC_mul]

theorem permAct_mk (p : AutPerm) (a : C) :
    permAct p (Multiplicative.ofAdd (Submodule.Quotient.mk a)) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (permC p a)) := rfl

abbrev MonoSD : Type := Multiplicative (C ⧸ ΩLine) ⋊[permAct] AutPerm

theorem multQ_induction {P : Multiplicative (C ⧸ ΩLine) → Prop}
    (h : ∀ a : C, P (Multiplicative.ofAdd (Submodule.Quotient.mk a))) (x) : P x := by
  induction x using Multiplicative.rec with
  | ofAdd x =>
    induction x using Submodule.Quotient.induction_on with
    | H a => exact h a

@[expose] def liftΩ {G : Type*} [Group G] (f : Multiplicative C →* G)
    (hf : f (Multiplicative.ofAdd ΩC) = 1) : Multiplicative (C ⧸ ΩLine) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift ΩLine.toAddSubgroup (MonoidHom.toAdditiveRight f) (by
      intro x hx
      rcases mem_ΩLine_iff.1 hx with rfl | rfl
      · exact map_zero _
      · show Additive.ofMul (f (Multiplicative.ofAdd ΩC)) = 0
        rw [hf]
        rfl))

theorem liftΩ_mk {G : Type*} [Group G] (f : Multiplicative C →* G)
    (hf : f (Multiplicative.ofAdd ΩC) = 1) (a : C) :
    liftΩ f hf (Multiplicative.ofAdd (Submodule.Quotient.mk a)) = f (Multiplicative.ofAdd a) :=
  rfl

theorem signHom_ΩC : signHom (Multiplicative.ofAdd ΩC) = 1 := by
  rw [signHom_apply, gO_ΩC]
  exact (modTwoUnit_eq_one_iff _).2 (.inr rfl)

@[expose] def signQ : Multiplicative (C ⧸ ΩLine) →* GLV := liftΩ signHom signHom_ΩC

theorem signQ_mk (a : C) :
    signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) = modTwoUnit (gO a) := rfl

theorem conj_permHom (p : AutPerm) (a : C) :
    permHom p * modTwoUnit (gO a) * (permHom p)⁻¹ = modTwoUnit (gO (permC p a)) := by
  rw [← PO_inv_mul_gO_mul_PO, modTwoUnit_mul, modTwoUnit_mul, modTwoUnit_inv, permHom_apply,
    mul_assoc]

theorem gO_mul_self (a : C) : gO a * gO a = 1 :=
  mat_injective (by rw [mat_mul, mat_gO, gmat_mul_self, mat_one])

theorem modTwoUnit_gO_inv (a : C) : (modTwoUnit (gO a))⁻¹ = modTwoUnit (gO a) := by
  rw [← modTwoUnit_inv, inv_eq_of_mul_eq_one_right (gO_mul_self a)]

theorem commutatorElement_gO_permHom (d : C) (p : AutPerm) :
    ⁅modTwoUnit (gO d), permHom p⁆ = modTwoUnit (gO (d + permC p d)) := by
  rw [commutatorElement_def, modTwoUnit_gO_inv, mul_assoc (modTwoUnit (gO d)) (permHom p),
    mul_assoc (modTwoUnit (gO d)), conj_permHom, ← modTwoUnit_mul, ← gO_add, add_comm]

@[expose] def monoHom : MonoSD →* GLV :=
  SemidirectProduct.lift signQ permHom fun p => MonoidHom.ext fun x => by
    induction x using multQ_induction with
    | h a =>
      show signQ (permAct p (Multiplicative.ofAdd (Submodule.Quotient.mk a))) =
        permHom p * signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) * (permHom p)⁻¹
      rw [permAct_mk, signQ_mk, signQ_mk, conj_permHom]

theorem monoHom_apply (x : MonoSD) : monoHom x = signQ x.left * permHom x.right := rfl

theorem monoHom_mk (a : C) (p : AutPerm) :
    monoHom ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ = modTwoUnit (PO p * gO a) := by
  rw [monoHom_apply, modTwoUnit_mul]
  rfl

theorem monoHom_comp_inl : monoHom.comp SemidirectProduct.inl = signQ :=
  SemidirectProduct.lift_comp_inl _ _ _

theorem monoHom_comp_inr : monoHom.comp SemidirectProduct.inr = permHom :=
  SemidirectProduct.lift_comp_inr _ _ _

theorem permHom_mem_range_monoHom (p : AutPerm) : permHom p ∈ monoHom.range :=
  ⟨SemidirectProduct.inr p, SemidirectProduct.lift_inr _ _ _ p⟩

theorem signQ_mem_range_monoHom (n : Multiplicative (C ⧸ ΩLine)) : signQ n ∈ monoHom.range :=
  ⟨SemidirectProduct.inl n, SemidirectProduct.lift_inl _ _ _ n⟩

theorem mk_eq_zero_of_scalar {a : C} (h : a = 0 ∨ a = ΩC) :
    (Submodule.Quotient.mk a : C ⧸ ΩLine) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (mem_ΩLine_iff.2 h)

theorem monoHom_injective : Function.Injective monoHom := by
  refine (injective_iff_map_eq_one monoHom).2 fun x hx => ?_
  obtain ⟨n, p⟩ := x
  induction n using multQ_induction with
  | h a =>
    rw [monoHom_mk, modTwoUnit_eq_one_iff, PO_mul_gO] at hx
    obtain ⟨hp, hb⟩ := eq_of_gO_mul_PO_scalar hx
    have ha : a = 0 ∨ a = ΩC := by
      rw [← LinearEquiv.apply_symm_apply (permC p) a]
      rcases hb with h | h <;> rw [h]
      · exact .inl (map_zero _)
      · exact .inr (permC_ΩC p)
    refine SemidirectProduct.ext ?_ hp
    show Multiplicative.ofAdd (Submodule.Quotient.mk a) = Multiplicative.ofAdd 0
    rw [mk_eq_zero_of_scalar ha]

theorem mem_range_monoHom {u : GLV} :
    u ∈ monoHom.range ↔ ∃ (a : C) (p : AutPerm), u = modTwoUnit (gO a * PO p) := by
  constructor
  · rintro ⟨⟨n, p⟩, rfl⟩
    induction n using multQ_induction with
    | h a => exact ⟨(permC p).symm a, p, by rw [monoHom_mk, PO_mul_gO]⟩
  · rintro ⟨a, p, rfl⟩
    exact ⟨⟨Multiplicative.ofAdd (Submodule.Quotient.mk (permC p a)), p⟩, by
      rw [monoHom_mk, gO_mul_PO]⟩

theorem modTwoEnd_twoΩCls_eq_iff (g : latticeO) :
    modTwoEnd g twoΩCls = twoΩCls ↔ modTwoUnit g ∈ monoHom.range := by
  rw [twoΩCls_eq_frameClass, modTwoEnd_frameClass_eq_iff, mem_range_monoHom]
  constructor
  · rintro ⟨a, p, rfl⟩
    exact ⟨a, p, rfl⟩
  · rintro ⟨a, p, h⟩
    rcases (modTwoUnit_eq_modTwoUnit_iff g _).1 h with h | h
    · exact ⟨a, p, h⟩
    · refine ⟨ΩC + a, p, ?_⟩
      rw [h, gO_add, gO_ΩC, mul_assoc]

abbrev OLq : Type := latticeO ⧸ Subgroup.zpowers negOneO

@[expose] def actQ : OLq →* GLVᵐᵒᵖ := QuotientGroup.lift _ modTwoHom zpowers_negOneO_eq_ker.le

theorem actQ_mk (g : latticeO) :
    actQ (QuotientGroup.mk g) = MulOpposite.op (modTwoUnit g) := rfl

theorem actQ_injective : Function.Injective actQ := injective_lift_modTwoHom

@[expose] def stabQ : Subgroup OLq := (MulAction.stabilizer GLV twoΩCls).op.comap actQ

theorem mk_mem_stabQ_iff (g : latticeO) :
    (QuotientGroup.mk g : OLq) ∈ stabQ ↔ modTwoEnd g twoΩCls = twoΩCls := Iff.rfl

@[expose] def permOHom : AutPerm →* latticeO where
  toFun p := PO p⁻¹
  map_one' := by rw [inv_one, PO_one]
  map_mul' p q := by rw [_root_.mul_inv_rev, PO_mul]

theorem permOHom_apply (p : AutPerm) : permOHom p = PO p⁻¹ := rfl

@[expose] def signOHom : Multiplicative C →* latticeO where
  toFun a := gO (Multiplicative.toAdd a)
  map_one' := gO_zero
  map_mul' _ _ := gO_add _ _

theorem signOHom_apply (a : C) : signOHom (Multiplicative.ofAdd a) = gO a := rfl

@[expose] def signQO : Multiplicative (C ⧸ ΩLine) →* OLq :=
  liftΩ ((QuotientGroup.mk' _).comp signOHom) (by
    show (QuotientGroup.mk (gO ΩC) : OLq) = 1
    rw [gO_ΩC, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _)

theorem signQO_mk (a : C) :
    signQO (Multiplicative.ofAdd (Submodule.Quotient.mk a)) = QuotientGroup.mk (gO a) := rfl

@[expose] def monoQ : MonoSD →* OLq :=
  SemidirectProduct.lift signQO ((QuotientGroup.mk' _).comp permOHom) fun p =>
    MonoidHom.ext fun x => by
      induction x using multQ_induction with
      | h a =>
        show signQO (permAct p (Multiplicative.ofAdd (Submodule.Quotient.mk a))) =
          (QuotientGroup.mk (PO p⁻¹) : OLq) * signQO (Multiplicative.ofAdd
            (Submodule.Quotient.mk a)) * (QuotientGroup.mk (PO p⁻¹))⁻¹
        rw [permAct_mk, signQO_mk, signQO_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul, PO_inv, inv_inv, PO_inv_mul_gO_mul_PO]

theorem monoQ_mk (a : C) (p : AutPerm) :
    monoQ ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ =
      QuotientGroup.mk (gO a * PO p⁻¹) := rfl

theorem monoQ_injective : Function.Injective monoQ := by
  refine (injective_iff_map_eq_one monoQ).2 fun x hx => ?_
  obtain ⟨n, p⟩ := x
  induction n using multQ_induction with
  | h a =>
    rw [monoQ_mk, QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff] at hx
    obtain ⟨hp, ha⟩ := eq_of_gO_mul_PO_scalar hx
    refine SemidirectProduct.ext ?_ (inv_eq_one.1 hp)
    show Multiplicative.ofAdd (Submodule.Quotient.mk a) = Multiplicative.ofAdd 0
    rw [mk_eq_zero_of_scalar ha]

theorem mem_range_monoQ {x : OLq} :
    x ∈ monoQ.range ↔ ∃ (a : C) (p : AutPerm), x = QuotientGroup.mk (gO a * PO p) := by
  constructor
  · rintro ⟨⟨n, p⟩, rfl⟩
    induction n using multQ_induction with
    | h a => exact ⟨a, p⁻¹, rfl⟩
  · rintro ⟨a, p, rfl⟩
    exact ⟨⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⁻¹⟩, by rw [monoQ_mk, inv_inv]⟩

theorem mem_stabQ_iff {x : OLq} :
    x ∈ stabQ ↔ ∃ (a : C) (p : AutPerm), x = QuotientGroup.mk (gO a * PO p) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [mk_mem_stabQ_iff, twoΩCls_eq_frameClass, modTwoEnd_frameClass_eq_iff]
    constructor
    · rintro ⟨a, p, rfl⟩
      exact ⟨a, p, rfl⟩
    · rintro ⟨a, p, h⟩
      have h1 := (mk_mem_stabQ_iff (gO a * PO p)).2 (by
        rw [twoΩCls_eq_frameClass]
        exact (modTwoEnd_frameClass_eq_iff _).2 ⟨a, p, rfl⟩)
      rw [← h] at h1
      exact (modTwoEnd_frameClass_eq_iff g).1 h1

theorem range_monoQ : monoQ.range = stabQ := by
  ext x
  rw [mem_range_monoQ, mem_stabQ_iff]

def stabQEquiv : MonoSD ≃* stabQ :=
  (MonoidHom.ofInjective monoQ_injective).trans (MulEquiv.subgroupCongr range_monoQ)

theorem mk_gO_mul_PO_eq_iff (a b : C) (p q : AutPerm) :
    (QuotientGroup.mk (gO a * PO p) : OLq) = QuotientGroup.mk (gO b * PO q) ↔
      p = q ∧ (a = b ∨ a = ΩC + b) := by
  have e : ∀ (c : C) (r : AutPerm), (QuotientGroup.mk (gO c * PO r) : OLq) =
      monoQ ⟨Multiplicative.ofAdd (Submodule.Quotient.mk c), r⁻¹⟩ := fun c r => by
    rw [monoQ_mk, inv_inv]
  rw [e, e, monoQ_injective.eq_iff]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk a : C ⧸ ΩLine) = Submodule.Quotient.mk b :=
      congrArg (fun x : MonoSD => Multiplicative.toAdd x.left) h
    have h2 : p⁻¹ = q⁻¹ := congrArg (fun x : MonoSD => x.right) h
    refine ⟨inv_injective h2, ?_⟩
    rw [Submodule.Quotient.eq, mem_ΩLine_iff, sub_eq_zero, sub_eq_iff_eq_add] at h1
    exact h1
  · rintro ⟨rfl, h⟩
    refine SemidirectProduct.ext (congrArg Multiplicative.ofAdd ?_) rfl
    rw [Submodule.Quotient.eq, mem_ΩLine_iff, sub_eq_zero, sub_eq_iff_eq_add]
    exact h

theorem signQ_injective : Function.Injective signQ := by
  rw [← monoHom_comp_inl]
  exact monoHom_injective.comp SemidirectProduct.inl_injective

theorem range_signQ : signQ.range = Esign := by
  ext u
  rw [mem_Esign]
  constructor
  · rintro ⟨x, rfl⟩
    induction x using multQ_induction with
    | h a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), rfl⟩

theorem finrank_ΩLine : Module.finrank (ZMod 2) ΩLine = 1 :=
  finrank_span_singleton (fun h => by
    have := congrArg (fun a : C => (a : Fin 24 → ZMod 2) 0) h
    exact absurd this (by decide))

theorem natCard_quot_ΩLine : Nat.card (C ⧸ ΩLine) = 2 ^ 11 := by
  have h := Submodule.finrank_quotient_add_finrank ΩLine
  rw [finrank_C, finrank_ΩLine] at h
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    show Module.finrank (ZMod 2) (C ⧸ ΩLine) = 11 by omega]

theorem natCard_Esign : Nat.card Esign = 2 ^ 11 := by
  rw [← range_signQ, ← Nat.card_congr (MonoidHom.ofInjective signQ_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, natCard_quot_ΩLine]

theorem natCard_range_monoHom : Nat.card monoHom.range = 2 ^ 11 * Nat.card AutPerm := by
  rw [← Nat.card_congr (MonoidHom.ofInjective monoHom_injective).toEquiv,
    SemidirectProduct.card, Nat.card_congr Multiplicative.toAdd, natCard_quot_ΩLine]

theorem Esign_le_range_monoHom : Esign ≤ monoHom.range := by
  rw [← range_signQ, ← monoHom_comp_inl, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

@[expose] def rangeMonoToAutPerm : monoHom.range →* AutPerm :=
  SemidirectProduct.rightHom.comp
    (MonoidHom.ofInjective monoHom_injective).symm.toMonoidHom

theorem rangeMonoToAutPerm_apply (x : MonoSD) :
    rangeMonoToAutPerm (MonoidHom.ofInjective monoHom_injective x) = x.right := by
  show SemidirectProduct.rightHom ((MonoidHom.ofInjective monoHom_injective).symm
    (MonoidHom.ofInjective monoHom_injective x)) = x.right
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem rangeMonoToAutPerm_surjective : Function.Surjective rangeMonoToAutPerm := fun p =>
  ⟨MonoidHom.ofInjective monoHom_injective (SemidirectProduct.inr p),
    rangeMonoToAutPerm_apply _⟩

theorem ker_rangeMonoToAutPerm : rangeMonoToAutPerm.ker = Esign.subgroupOf monoHom.range := by
  ext y
  obtain ⟨x, rfl⟩ := (MonoidHom.ofInjective monoHom_injective).surjective y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← range_signQ, rangeMonoToAutPerm_apply,
    MonoidHom.ofInjective_apply]
  constructor
  · intro h
    refine ⟨x.left, ?_⟩
    rw [monoHom_apply, h, map_one, mul_one]
  · rintro ⟨n, hn⟩
    have h1 : monoHom (SemidirectProduct.inl n) = monoHom x := by
      rw [← hn, ← MonoidHom.comp_apply, monoHom_comp_inl]
    rw [← monoHom_injective h1]
    rfl

instance normal_Esign_subgroupOf : (Esign.subgroupOf monoHom.range).Normal :=
  ker_rangeMonoToAutPerm ▸ MonoidHom.normal_ker _

def rangeMonoQuotEquiv : monoHom.range ⧸ Esign.subgroupOf monoHom.range ≃* AutPerm :=
  (QuotientGroup.quotientMulEquivOfEq ker_rangeMonoToAutPerm.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rangeMonoToAutPerm_surjective)

theorem kGen_one : kGen 1 = permHom pAAut := by
  simp [kGen, frameGen, permHom_apply]

theorem kGen_two : kGen 2 = permHom pBAut := by
  simp [kGen, frameGen, permHom_apply]

theorem kGen_of_three_le {j : Fin 15} (h : 3 ≤ (j : ℕ)) :
    kGen j = modTwoUnit (gO (bC ⟨j - 3, by omega⟩)) := by
  simp [kGen, frameGen, show (j : ℕ) ≠ 0 by omega, show (j : ℕ) ≠ 1 by omega,
    show (j : ℕ) ≠ 2 by omega]

theorem kGen_bC (j : Fin 12) :
    kGen ⟨j + 3, by omega⟩ = modTwoUnit (gO (bC j)) := by
  have e : (⟨((⟨j + 3, by omega⟩ : Fin 15) : ℕ) - 3, by simp⟩ : Fin 12) = j := Fin.ext (by simp)
  rw [kGen_of_three_le (by simp), e]

theorem modTwoUnit_gO_bC_mem_Evis (j : Fin 12) : modTwoUnit (gO (bC j)) ∈ Evis := by
  rw [← kGen_bC]
  exact Subgroup.subset_closure ⟨_, (by simp : 3 ≤ ((⟨j + 3, by omega⟩ : Fin 15) : ℕ)), rfl⟩

private theorem zmod2_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with h | h <;> simp [h]

theorem modTwoUnit_gO_mem_Evis (a : C) : modTwoUnit (gO a) ∈ Evis := by
  have ha : a = ∑ i, ψ (a : Fin 24 → ZMod 2) i • bC i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact eq_comb_of_mem_C a.2
  have key : Multiplicative.ofAdd a ∈ Evis.comap signHom := by
    rw [ha, ofAdd_sum]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap]
    rcases zmod2_cases' (ψ (a : Fin 24 → ZMod 2) i) with h | h <;> rw [h]
    · rw [zero_smul, ofAdd_zero, map_one]
      exact Evis.one_mem
    · rw [one_smul, signHom_apply]
      exact modTwoUnit_gO_bC_mem_Evis i
  exact key

theorem Evis_eq_Esign : Evis = Esign := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun u hu => ?_
  · rintro _ ⟨j, hj, rfl⟩
    rw [kGen_of_three_le hj]
    exact mem_Esign.2 ⟨_, rfl⟩
  · obtain ⟨a, rfl⟩ := mem_Esign.1 hu
    exact modTwoUnit_gO_mem_Evis a

end CFSG.Monster.VisQuot
