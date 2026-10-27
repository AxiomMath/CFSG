module

public import CFSG.Monster.Spin.SpinCoord
public import CFSG.Monster.Spin.Coords

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Matrix Subgroup
open scoped commutatorElement

section Transport

variable {G H : Type*} [Group G] [Group H] (e : G ≃* H)

theorem mem_zpowers_map_iff {g x : G} : e x ∈ zpowers (e g) ↔ x ∈ zpowers g := by
  simp only [mem_zpowers_iff, ← map_zpow]
  exact exists_congr fun k => e.injective.eq_iff

theorem center_eq_zpowers_of_mulEquiv {g : G} (h : center G = zpowers g) :
    center H = zpowers (e g) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_zpowers_map_iff, ← h, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hx g'
    apply e.injective
    rw [map_mul, map_mul, hx]
  · intro hx g'
    obtain ⟨g', rfl⟩ := e.surjective g'
    rw [← map_mul, ← map_mul, hx]

theorem commutator_eq_zpowers_of_mulEquiv {g : G} (h : commutator G = zpowers g) :
    commutator H = zpowers (e g) := by
  have h1 : (commutator G).map (e : G →* H) = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h1, h, MonoidHom.map_zpowers]
  rfl

theorem frattini_eq_zpowers_of_mulEquiv {g : G} (h : frattini G = zpowers g) :
    frattini H = zpowers (e g) := by
  have h1 : (frattini G).map e.toMonoidHom = frattini H :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  rw [← h1, h, MonoidHom.map_zpowers]
  rfl

theorem isElementaryAbelian_two_of_mulEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : G ≃* Multiplicative V) : IsElementaryAbelian 2 G where
  is_comm := ⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => e.injective (by
    rw [map_pow, map_one, pow_two, ← ofAdd_toAdd (e g), ← ofAdd_add, ← two_smul (ZMod 2),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, ofAdd_zero])

end Transport

@[expose] def zU : GL SpinIdx ℚ := -1

@[expose] def TU (a : C) : GL SpinIdx ℚ := XU ⟨a, 0⟩ * DU (thetaD a)

@[simp] theorem coe_zU : (zU : Matrix SpinIdx SpinIdx ℚ) = zmat := by
  rw [zU, Units.val_neg, Units.val_one, zmat]

@[simp] theorem coe_TU (a : C) : (TU a : Matrix SpinIdx SpinIdx ℚ) = Tmat a := rfl

theorem coe_zU_pow (s : ZMod 2) :
    ((zU ^ s.val : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = zmat ^ s.val := by
  rw [Units.val_pow_eq_pow_val, coe_zU]

@[expose] def toGL : SpinCoord →* GL SpinIdx ℚ where
  toFun x := ⟨qmatR ℚ x.s x.a x.δ, (qmatR ℚ x.s x.a x.δ)ᵀ, qmatR_mul_transpose_self _ _ _,
    qmatR_transpose_mul_self _ _ _⟩
  map_one' := Units.ext qmatR_zero
  map_mul' _ _ := Units.ext (qmatR_mul _ _ _ _ _ _).symm

theorem coe_toGL (x : SpinCoord) :
    (toGL x : Matrix SpinIdx SpinIdx ℚ) = qmatR ℚ x.s x.a x.δ := rfl

theorem toGL_injective : Function.Injective toGL := fun x y h => by
  obtain ⟨h1, h2, h3⟩ := qmatR_injective (R := ℚ) two_ne_zero (congrArg Units.val h)
  exact SpinCoord.ext h1 h2 h3

theorem toGL_mk (s : ZMod 2) (a : C) (δ : Cocode) :
    toGL ⟨s, a, δ⟩ = zU ^ s.val * TU a * DU δ := by
  apply Units.ext
  rw [coe_toGL, Units.val_mul, Units.val_mul, coe_zU_pow, coe_TU, coe_DU,
    zmat_pow_mul_Tmat_mul_Dmat]

theorem toGL_eq (x : SpinCoord) : toGL x = zU ^ x.s.val * TU x.a * DU x.δ := toGL_mk _ _ _

theorem XU_eq_toGL (e : Parker) : XU e = toGL ⟨e.sign, e.code, thetaD e.code⟩ :=
  Units.ext (Xmat_eq_qmatR e)

theorem DU_eq_toGL (δ : Cocode) : DU δ = toGL ⟨0, 0, δ⟩ := Units.ext (Dmat_eq_qmatR δ)

theorem TU_eq_toGL (a : C) : TU a = toGL ⟨0, a, 0⟩ := Units.ext (Tmat_eq_qmatR a)

theorem zU_eq_toGL : zU = toGL SpinCoord.z := Units.ext (by rw [coe_zU, coe_toGL]; exact zmat_eq_qmatR)

@[simp] theorem TU_zero : TU 0 = 1 := by
  rw [TU_eq_toGL]
  exact toGL.map_one

@[simp] theorem DU_zero : DU 0 = 1 := by
  rw [DU_eq_toGL]
  exact toGL.map_one

theorem XU_mul_DU (e : Parker) (δ : Cocode) :
    XU e * DU δ = toGL ⟨e.sign, e.code, thetaD e.code + δ⟩ := by
  rw [XU_eq_toGL, DU_eq_toGL, ← map_mul]
  congr 1
  ext <;> simp

theorem toGL_eq_XU_mul_DU (x : SpinCoord) : toGL x = XU ⟨x.a, x.s⟩ * DU (thetaD x.a + x.δ) := by
  rw [XU_mul_DU, ← add_assoc, add_self_cocode, zero_add]

theorem range_toGL : toGL.range = Q := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [toGL_eq_XU_mul_DU]
    exact Q.mul_mem (XU_mem_Q _) (DU_mem_Q _)
  · rw [Q, Subgroup.closure_le]
    rintro _ (⟨e, rfl⟩ | ⟨δ, rfl⟩)
    · exact ⟨_, (XU_eq_toGL e).symm⟩
    · exact ⟨_, (DU_eq_toGL δ).symm⟩

@[expose] def spinEquiv : SpinCoord ≃* Q :=
  (MonoidHom.ofInjective toGL_injective).trans (MulEquiv.subgroupCongr range_toGL)

theorem coe_spinEquiv (x : SpinCoord) : (spinEquiv x : GL SpinIdx ℚ) = toGL x := rfl

@[expose] def zQ : Q := spinEquiv SpinCoord.z

theorem coe_zQ : (zQ : GL SpinIdx ℚ) = zU := zU_eq_toGL.symm

theorem zU_mem_Q : zU ∈ Q := coe_zQ ▸ zQ.2

theorem TU_mem_Q (a : C) : TU a ∈ Q := by
  rw [TU_eq_toGL, ← range_toGL]
  exact ⟨_, rfl⟩

theorem zU_pow_mul_mem_Q (s : ZMod 2) (a : C) (δ : Cocode) : zU ^ s.val * TU a * DU δ ∈ Q := by
  rw [← toGL_mk, ← range_toGL]
  exact ⟨_, rfl⟩

theorem existsUnique_zU_pow_mul {g : GL SpinIdx ℚ} (hg : g ∈ Q) :
    ∃! x : ZMod 2 × C × Cocode, zU ^ x.1.val * TU x.2.1 * DU x.2.2 = g := by
  rw [← range_toGL] at hg
  obtain ⟨y, rfl⟩ := hg
  refine ⟨(y.s, y.a, y.δ), (toGL_eq y).symm, fun x hx => ?_⟩
  dsimp only at hx
  rw [← toGL_mk] at hx
  rw [← toGL_injective hx]

theorem zU_pow_mul_mul (s t : ZMod 2) (a b : C) (δ ε : Cocode) :
    (zU ^ s.val * TU a * DU δ) * (zU ^ t.val * TU b * DU ε) =
      zU ^ (s + t + pair b δ).val * TU (a + b) * DU (δ + ε) := by
  rw [← toGL_mk, ← toGL_mk, ← toGL_mk, ← map_mul]
  rfl

theorem toGL_s (s : ZMod 2) : toGL ⟨s, 0, 0⟩ = zU ^ s.val := by
  rw [toGL_mk, TU_zero, DU_zero, mul_one, mul_one]

theorem zU_pow_mul_sq (s : ZMod 2) (a : C) (δ : Cocode) :
    (zU ^ s.val * TU a * DU δ) ^ 2 = zU ^ (pair a δ).val := by
  rw [← toGL_mk, ← map_pow, SpinCoord.sq_eq, toGL_s]

theorem commutatorElement_zU_pow_mul (s t : ZMod 2) (a b : C) (δ ε : Cocode) :
    ⁅zU ^ s.val * TU a * DU δ, zU ^ t.val * TU b * DU ε⁆ = zU ^ (pair a ε + pair b δ).val := by
  rw [← toGL_mk, ← toGL_mk, ← map_commutatorElement, SpinCoord.commutatorElement_eq, toGL_s]

theorem existsUnique_XU_mul_DU {g : GL SpinIdx ℚ} (hg : g ∈ Q) :
    ∃! p : Parker × Cocode, XU p.1 * DU p.2 = g := by
  rw [← range_toGL] at hg
  obtain ⟨y, rfl⟩ := hg
  refine ⟨(⟨y.a, y.s⟩, thetaD y.a + y.δ), (toGL_eq_XU_mul_DU y).symm, fun p hp => ?_⟩
  dsimp only at hp
  rw [XU_mul_DU] at hp
  have h := toGL_injective hp
  obtain ⟨p₁, p₂⟩ := p
  have h₁ : p₁.sign = y.s := congrArg SpinCoord.s h
  have h₂ : p₁.code = y.a := congrArg SpinCoord.a h
  have h₃ : thetaD p₁.code + p₂ = y.δ := congrArg SpinCoord.δ h
  refine Prod.ext (Parker.ext h₂ h₁) ?_
  change p₂ = thetaD y.a + y.δ
  rw [← h₃, ← h₂, ← add_assoc, add_self_cocode, zero_add]

theorem natCard_Q : Nat.card Q = 2 ^ 25 := by
  rw [← Nat.card_congr spinEquiv.toEquiv, SpinCoord.natCard]

theorem center_Q : center Q = zpowers zQ :=
  center_eq_zpowers_of_mulEquiv spinEquiv SpinCoord.center_eq

theorem commutator_Q : commutator Q = zpowers zQ :=
  commutator_eq_zpowers_of_mulEquiv spinEquiv SpinCoord.commutator_eq

theorem frattini_Q : frattini Q = zpowers zQ :=
  frattini_eq_zpowers_of_mulEquiv spinEquiv SpinCoord.frattini_eq

theorem orderOf_zQ : orderOf zQ = 2 := by
  rw [zQ, MulEquiv.orderOf_eq, SpinCoord.orderOf_z]

theorem natCard_zpowers_zQ : Nat.card (zpowers zQ) = 2 := by
  rw [Nat.card_zpowers, orderOf_zQ]

theorem isExtraspecialPGroup_Q : IsExtraspecialPGroup 2 Q :=
  ⟨IsPGroup.of_card natCard_Q, by rw [commutator_Q, center_Q], by rw [frattini_Q, center_Q],
    by rw [center_Q, natCard_zpowers_zQ]⟩

@[expose] def SpinCoord.proj : SpinCoord →* Multiplicative (C × Cocode) where
  toFun x := Multiplicative.ofAdd (x.a, x.δ)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def projQ : Q →* Multiplicative (C × Cocode) :=
  SpinCoord.proj.comp spinEquiv.symm.toMonoidHom

theorem projQ_spinEquiv (x : SpinCoord) : projQ (spinEquiv x) = Multiplicative.ofAdd (x.a, x.δ) := by
  simp only [projQ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem ker_projQ : projQ.ker = center Q := by
  ext g
  obtain ⟨x, rfl⟩ := spinEquiv.surjective g
  have hz : zQ = spinEquiv SpinCoord.z := rfl
  rw [MonoidHom.mem_ker, projQ_spinEquiv, center_Q, hz, mem_zpowers_map_iff spinEquiv,
    SpinCoord.mem_zpowers_z, ofAdd_eq_one, Prod.mk_eq_zero]

theorem projQ_surjective : Function.Surjective projQ := fun v =>
  ⟨spinEquiv ⟨0, (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2⟩, by
    rw [projQ_spinEquiv]
    rfl⟩

@[expose] def quotCenterEquiv : (Q ⧸ center Q) ≃* Multiplicative (C × Cocode) :=
  (QuotientGroup.quotientMulEquivOfEq ker_projQ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projQ projQ_surjective)

theorem isElementaryAbelian_quot : IsElementaryAbelian 2 (Q ⧸ center Q) :=
  isElementaryAbelian_two_of_mulEquiv quotCenterEquiv

theorem finrank_C_prod_cocode : Module.finrank (ZMod 2) (C × Cocode) = 24 := by
  rw [Module.finrank_prod, finrank_C, finrank_cocode]

theorem natCard_quot : Nat.card (Q ⧸ center Q) = 2 ^ 24 := by
  rw [Nat.card_congr quotCenterEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
    natCard_C, natCard_cocode]
  norm_num

@[expose] def SpinCoord.transSub : Subgroup SpinCoord where
  carrier := {x | x.δ = 0}
  mul_mem' := fun {x y} hx hy => by
    change x.δ + y.δ = 0
    rw [show x.δ = 0 from hx, show y.δ = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' := fun {x} hx => hx

@[expose] def TransQ : Subgroup (GL SpinIdx ℚ) := SpinCoord.transSub.map toGL

theorem mem_TransQ {g : GL SpinIdx ℚ} : g ∈ TransQ ↔ ∃ (s : ZMod 2) (a : C), zU ^ s.val * TU a = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨x.s, x.a, ?_⟩
    rw [toGL_eq, show x.δ = 0 from hx, DU_zero, mul_one]
  · rintro ⟨s, a, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨s, a, 0⟩, rfl, by rw [toGL_mk, DU_zero, mul_one]⟩

theorem TransQ_le_Q : TransQ ≤ Q := by
  rw [← range_toGL]
  exact Subgroup.map_le_range _ _

private theorem transSub_mul_comm {x y : SpinCoord} (hx : x.δ = 0) (hy : y.δ = 0) :
    x * y = y * x := by
  ext
  · simp only [SpinCoord.mul_s, hx, hy, pair_zero_right, add_zero]
    exact add_comm _ _
  · exact add_comm _ _
  · simp only [SpinCoord.mul_δ, hx, hy]

theorem TransQ_mul_comm (g h : TransQ) : g * h = h * g := by
  obtain ⟨x, hx, hgx⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨y, hy, hhy⟩ := Subgroup.mem_map.1 h.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hgx, ← hhy, ← map_mul, ← map_mul,
    transSub_mul_comm hx hy]

theorem TransQ_sq (g : TransQ) : g ^ 2 = 1 := by
  obtain ⟨x, hx, hgx⟩ := Subgroup.mem_map.1 g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hgx, ← map_pow, SpinCoord.sq_eq, show x.δ = 0 from hx,
    pair_zero_right, Subgroup.coe_one]
  exact toGL.map_one

theorem isElementaryAbelian_TransQ : IsElementaryAbelian 2 TransQ where
  is_comm := ⟨TransQ_mul_comm⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one TransQ_sq

theorem natCard_TransQ : Nat.card TransQ = 2 ^ 13 := by
  have e₁ := Subgroup.equivMapOfInjective SpinCoord.transSub toGL toGL_injective
  have e₂ : SpinCoord.transSub ≃ ZMod 2 × C :=
    { toFun := fun x => (x.1.s, x.1.a)
      invFun := fun p => ⟨⟨p.1, p.2, 0⟩, rfl⟩
      left_inv := fun x => Subtype.ext (SpinCoord.ext rfl rfl (show (0 : Cocode) = x.1.δ from
        (show x.1.δ = 0 from x.2).symm))
      right_inv := fun _ => rfl }
  rw [TransQ, ← Nat.card_congr e₁.toEquiv, Nat.card_congr e₂, Nat.card_prod, Nat.card_zmod,
    natCard_C]
  norm_num

theorem spin_extraspecial_group_structure :
    (∀ (s : ZMod 2) (a : C) (δ : Cocode), zU ^ s.val * TU a * DU δ ∈ Q) ∧
    (∀ g ∈ Q, ∃! x : ZMod 2 × C × Cocode, zU ^ x.1.val * TU x.2.1 * DU x.2.2 = g) ∧
    (∀ (s t : ZMod 2) (a b : C) (δ ε : Cocode),
      (zU ^ s.val * TU a * DU δ) * (zU ^ t.val * TU b * DU ε) =
        zU ^ (s + t + pair b δ).val * TU (a + b) * DU (δ + ε)) ∧
    Nat.card Q = 2 ^ 25 ∧
    center Q = zpowers zQ ∧ commutator Q = zpowers zQ ∧ frattini Q = zpowers zQ ∧
    Nat.card (zpowers zQ) = 2 ∧ (zQ : GL SpinIdx ℚ) = zU ∧
    (zU : Matrix SpinIdx SpinIdx ℚ) = zmat ∧
    IsElementaryAbelian 2 (Q ⧸ center Q) ∧ Nat.card (Q ⧸ center Q) = 2 ^ 24 ∧
    Nonempty ((Q ⧸ center Q) ≃* Multiplicative (C × Cocode)) ∧
    Module.finrank (ZMod 2) (C × Cocode) = 24 ∧
    IsExtraspecialPGroup 2 Q ∧
    (∀ (s : ZMod 2) (a : C) (δ : Cocode),
      (zU ^ s.val * TU a * DU δ) ^ 2 = zU ^ (pair a δ).val) ∧
    (∀ (s t : ZMod 2) (a b : C) (δ ε : Cocode),
      ⁅zU ^ s.val * TU a * DU δ, zU ^ t.val * TU b * DU ε⁆ = zU ^ (pair a ε + pair b δ).val) ∧
    (TransQ ≤ Q ∧ (∀ g, g ∈ TransQ ↔ ∃ (s : ZMod 2) (a : C), zU ^ s.val * TU a = g) ∧
      IsElementaryAbelian 2 TransQ ∧ Nat.card TransQ = 2 ^ 13) ∧
    (∀ g ∈ Q, ∃! p : Parker × Cocode, XU p.1 * DU p.2 = g) :=
  ⟨zU_pow_mul_mem_Q, fun _ hg => existsUnique_zU_pow_mul hg, zU_pow_mul_mul, natCard_Q, center_Q,
    commutator_Q, frattini_Q, natCard_zpowers_zQ, coe_zQ, coe_zU, isElementaryAbelian_quot,
    natCard_quot, ⟨quotCenterEquiv⟩, finrank_C_prod_cocode, isExtraspecialPGroup_Q, zU_pow_mul_sq,
    commutatorElement_zU_pow_mul,
    ⟨TransQ_le_Q, fun _ => mem_TransQ, isElementaryAbelian_TransQ, natCard_TransQ⟩,
    fun _ hg => existsUnique_XU_mul_DU hg⟩

end CFSG.Monster.Spin
