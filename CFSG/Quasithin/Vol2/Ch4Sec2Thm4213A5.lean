module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat

public section

namespace CFSG.Quasithin.H13.Ch4.A5Herm

open CFSG.GH74.KGroups CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem fintype_card_GF4 : Fintype.card GF4 = 2 ^ 2 := by decide

instance : CharP GF4 2 := charP_of_card_eq_prime_pow fintype_card_GF4

theorem card_GF4 : Nat.card GF4 = 2 ^ (2 * 1) := by
  rw [Nat.card_eq_fintype_card, fintype_card_GF4]

@[expose] def pts : Fin 5 → Fin 2 → GF4 :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, ⟨2⟩], ![1, ⟨3⟩]]

@[expose] def tab : Fin 4 → Fin 5 := ![0, 2, 3, 4]

@[expose] def idx (w : Fin 2 → GF4) : Fin 5 :=
  if w 0 = 0 then 1 else tab (w 1 * (w 0)⁻¹).val

theorem idx_pts : ∀ i, idx (pts i) = i := by decide

theorem pts_ne_zero : ∀ i, pts i ≠ 0 := by decide

theorem idx_smul : ∀ (c : GF4) (w : Fin 2 → GF4), c ≠ 0 → idx (c • w) = idx w := by decide

theorem exists_smul_pts : ∀ w : Fin 2 → GF4, w ≠ 0 → ∃ c : GF4, c ≠ 0 ∧ w = c • pts (idx w) := by
  decide

theorem mul_sq_eq_one : ∀ c : GF4, c ≠ 0 → c * c ^ 2 = 1 := by decide

@[expose] def act (A : Matrix (Fin 2) (Fin 2) GF4) (i : Fin 5) : Fin 5 := idx (Aᵀ *ᵥ pts i)

theorem transpose_mulVec_ne_zero (A : Matrix.GeneralLinearGroup (Fin 2) GF4) {w : Fin 2 → GF4}
    (hw : w ≠ 0) : ((A : Matrix (Fin 2) (Fin 2) GF4))ᵀ *ᵥ w ≠ 0 := by
  intro h
  apply hw
  have h1 : (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4))ᵀ *ᵥ
      ((((A : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4))ᵀ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  rw [← h1, h, Matrix.mulVec_zero]

theorem act_one : act 1 = id := by
  funext i
  simp [act, idx_pts]

theorem act_mul (A : Matrix.GeneralLinearGroup (Fin 2) GF4) (B : Matrix (Fin 2) (Fin 2) GF4)
    (i : Fin 5) :
    act ((A : Matrix (Fin 2) (Fin 2) GF4) * B) i = act B (act A i) := by
  obtain ⟨c, hc, hcw⟩ := exists_smul_pts _
    (transpose_mulVec_ne_zero A (pts_ne_zero i))
  have key : idx (Bᵀ *ᵥ ((A : Matrix (Fin 2) (Fin 2) GF4)ᵀ *ᵥ pts i)) =
      idx (Bᵀ *ᵥ pts (idx ((A : Matrix (Fin 2) (Fin 2) GF4)ᵀ *ᵥ pts i))) := by
    conv_lhs => rw [hcw]
    rw [Matrix.mulVec_smul, idx_smul _ _ hc]
  simp only [act]
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  exact key

@[expose] def actPerm (A : Matrix.GeneralLinearGroup (Fin 2) GF4) : Equiv.Perm (Fin 5) where
  toFun := act ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4)
  invFun := act (A : Matrix (Fin 2) (Fin 2) GF4)
  left_inv i := by
    show act _ (act _ i) = i
    rw [← act_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, act_one, id]
  right_inv i := by
    show act _ (act _ i) = i
    rw [← act_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, act_one, id]

@[expose] def actHom : Matrix.GeneralLinearGroup (Fin 2) GF4 →* Equiv.Perm (Fin 5) where
  toFun := actPerm
  map_one' := by
    refine Equiv.ext fun i => ?_
    show act _ i = i
    rw [inv_one, Units.val_one, act_one, id]
  map_mul' A B := by
    refine Equiv.ext fun i => ?_
    show act _ i = act _ (act _ i)
    rw [mul_inv_rev, Units.val_mul, act_mul]

@[expose] noncomputable def slHom : ↥(StatedSL 2 GF4) →* Equiv.Perm (Fin 5) :=
  actHom.comp (StatedSL 2 GF4).subtype

theorem slHom_symm_apply (γ : ↥(StatedSL 2 GF4)) (i : Fin 5) :
    (slHom γ).symm i =
      act (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4) i := rfl

theorem det_eq_one (γ : ↥(StatedSL 2 GF4)) :
    (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4).det = 1 := by
  obtain ⟨x, hx⟩ := γ
  rw [statedSL_eq_range_toGL] at hx
  obtain ⟨A, hA⟩ := hx
  change ((x : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4).det = 1
  rw [← hA]
  exact A.2

theorem eq_one_of_act_eq : ∀ A : Matrix (Fin 2) (Fin 2) GF4, A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 →
    (∀ i, act A i = i) → A = 1 := by
  decide +kernel

theorem slHom_injective : Function.Injective slHom := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have h1 : ∀ i, act (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
      Matrix (Fin 2) (Fin 2) GF4) i = i := fun i => by
    rw [← slHom_symm_apply, hγ]
    rfl
  have h2 := eq_one_of_act_eq _ (by rw [← Matrix.det_fin_two]; exact det_eq_one γ) h1
  exact Subtype.ext (Units.ext h2)

theorem card_statedSL : Nat.card ↥(StatedSL 2 GF4) = 60 := by
  rw [statedSL_eq_range_toGL, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective, Subgroup.card_top,
    CFSG.OrderReductions.LinearOrders.card_specialLinear GF4 2 (by norm_num), card_GF4]
  decide

theorem slHom_range : slHom.range = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hc : Nat.card slHom.range = 60 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective slHom_injective,
      Subgroup.card_top, card_statedSL]
  have h := Subgroup.card_mul_index slHom.range
  rw [hc, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h120 : Nat.factorial 5 = 120 := by decide
  omega

@[expose] noncomputable def slEquiv : ↥(StatedSL 2 GF4) ≃* ↥(alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective
    (slHom.codRestrict (alternatingGroup (Fin 5)) fun γ => by
      rw [← slHom_range]
      exact ⟨γ, rfl⟩)
    ⟨fun a b h => slHom_injective (congrArg Subtype.val h), fun σ => by
      have hσ : (σ : Equiv.Perm (Fin 5)) ∈ slHom.range := by
        rw [slHom_range]
        exact σ.2
      obtain ⟨γ, hγ⟩ := hσ
      exact ⟨γ, Subtype.ext hγ⟩⟩

theorem coe_slEquiv (γ : ↥(StatedSL 2 GF4)) :
    ((slEquiv γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = slHom γ := rfl

@[expose] def hval (X : Matrix (Fin 2) (Fin 2) GF4) (w : Fin 2 → GF4) : GF4 :=
  w ⬝ᵥ (X *ᵥ fun j => w j ^ 2)

theorem hval_add (X Y : Matrix (Fin 2) (Fin 2) GF4) (w : Fin 2 → GF4) :
    hval (X + Y) w = hval X w + hval Y w := by
  simp only [hval, Matrix.add_mulVec, dotProduct_add]

theorem hval_smul (X : Matrix (Fin 2) (Fin 2) GF4) (c : GF4) (w : Fin 2 → GF4) :
    hval X (c • w) = c * c ^ 2 * hval X w := by
  have h : (fun j => (c • w) j ^ 2) = c ^ 2 • fun j => w j ^ 2 := by
    funext j
    simp [mul_pow]
  simp only [hval, h, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem frobPow_mulVec (γ : Matrix (Fin 2) (Fin 2) GF4) (w : Fin 2 → GF4) :
    (frobPow 1 γ)ᵀ *ᵥ (fun j => w j ^ 2) = fun j => (γᵀ *ᵥ w) j ^ 2 := by
  funext j
  simp only [frobPow, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.map_apply, pow_one]
  rw [CharTwo.add_sq]
  ring

theorem hval_twist (γ X : Matrix (Fin 2) (Fin 2) GF4) (w : Fin 2 → GF4) :
    hval (γ * X * (frobPow 1 γ)ᵀ) w = hval X (γᵀ *ᵥ w) := by
  simp only [hval]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frobPow_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]

@[expose] def toZ2 (a : GF4) : ZMod 2 := if a = 1 then 1 else 0

theorem toZ2_add : ∀ a b : GF4, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
    toZ2 (a + b) = toZ2 a + toZ2 b := by decide

theorem hval_bin : ∀ X : Matrix (Fin 2) (Fin 2) GF4, (frobPow 1 X)ᵀ = X →
    ∀ i, hval X (pts i) = 0 ∨ hval X (pts i) = 1 := by
  decide +kernel

theorem hval_inj : ∀ X : Matrix (Fin 2) (Fin 2) GF4, (frobPow 1 X)ᵀ = X →
    (∀ i, toZ2 (hval X (pts i)) = 0) → X = 0 := by
  decide +kernel

theorem hval_even : ∀ X : Matrix (Fin 2) (Fin 2) GF4, (frobPow 1 X)ᵀ = X →
    ∑ i, toZ2 (hval X (pts i)) = 0 := by
  decide +kernel

theorem hval_surj : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
    ∃ X : Matrix (Fin 2) (Fin 2) GF4, (frobPow 1 X)ᵀ = X ∧ ∀ i, toZ2 (hval X (pts i)) = y i := by
  decide +kernel

@[expose] def hermToEven (X : ↥(hermSub 1 (Fin 2) GF4)) : ↥(evenWeight 5) :=
  ⟨fun i => toZ2 (hval (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) GF4)))
      (pts i)), by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact hval_even _ X.2⟩

theorem hermToEven_apply (X : ↥(hermSub 1 (Fin 2) GF4)) (i : Fin 5) :
    (hermToEven X : Fin 5 → ZMod 2) i =
      toZ2 (hval (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) GF4)))
        (pts i)) :=
  rfl

theorem hermToEven_mul (X Y : ↥(hermSub 1 (Fin 2) GF4)) :
    hermToEven (X * Y) = hermToEven X + hermToEven Y := by
  apply Subtype.ext
  funext i
  simp only [AddSubgroup.coe_add, Pi.add_apply, hermToEven_apply, Subgroup.coe_mul, toAdd_mul,
    hval_add]
  exact toZ2_add _ _ (hval_bin _ X.2 i) (hval_bin _ Y.2 i)

theorem hermToEven_bijective : Function.Bijective hermToEven := by
  refine ⟨fun X Y h => ?_, fun y => ?_⟩
  · have hXY : hermToEven (X * Y⁻¹) = 0 := by
      rw [hermToEven_mul, h, ← hermToEven_mul, mul_inv_cancel]
      apply Subtype.ext
      funext i
      simp [hermToEven_apply, hval, toZ2]
    have h0 := hval_inj _ (X * Y⁻¹).2 fun i => congrFun (congrArg Subtype.val hXY) i
    have h1 : X * Y⁻¹ = 1 := Subtype.ext (Multiplicative.toAdd.injective h0)
    exact mul_inv_eq_one.mp h1
  · have hy : ∑ i, (y : Fin 5 → ZMod 2) i = 0 := by
      have := y.2
      simpa [evenWeight] using this
    obtain ⟨X, hX, hXy⟩ := hval_surj _ hy
    exact ⟨⟨Multiplicative.ofAdd X, hX⟩, Subtype.ext (funext hXy)⟩

@[expose] noncomputable def hermEquiv : ↥(hermSub 1 (Fin 2) GF4) ≃ ↥(evenWeight 5) :=
  Equiv.ofBijective hermToEven hermToEven_bijective

theorem hermToEven_twist (γ : ↥(StatedSL 2 GF4)) (X : ↥(hermSub 1 (Fin 2) GF4)) :
    hermToEven ⟨twistAct 1 (StatedSL 2 GF4) γ X, twistAct_mem_hermSub 1 _ card_GF4 γ X.2⟩ =
      permWeight 5 (slHom γ) (hermToEven X) := by
  apply Subtype.ext
  funext i
  set A := (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4) with hA
  obtain ⟨c, hc, hcw⟩ := exists_smul_pts _ (transpose_mulVec_ne_zero
    (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (pts_ne_zero i))
  show toZ2 (hval (A * Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) GF4)) *
      (frobPow 1 A)ᵀ) (pts i)) =
    toZ2 (hval (Multiplicative.toAdd (X : Multiplicative (Matrix (Fin 2) (Fin 2) GF4)))
      (pts ((slHom γ)⁻¹ i)))
  rw [hval_twist, hcw, hval_smul, mul_sq_eq_one c hc, one_mul, Equiv.Perm.inv_def,
    slHom_symm_apply]
  rfl

theorem hermEquiv_symm_permWeight (γ : ↥(StatedSL 2 GF4)) (x : ↥(evenWeight 5)) :
    ((hermEquiv.symm (permWeight 5 (slHom γ) x) : ↥(hermSub 1 (Fin 2) GF4)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) GF4)) =
      twistAct 1 (StatedSL 2 GF4) γ (hermEquiv.symm x) := by
  have h := hermToEven_twist γ (hermEquiv.symm x)
  have hx : hermToEven (hermEquiv.symm x) = x := hermEquiv.apply_symm_apply x
  rw [hx] at h
  rw [← h]
  show ((hermEquiv.symm (hermEquiv _) : ↥(hermSub 1 (Fin 2) GF4)) :
    Multiplicative (Matrix (Fin 2) (Fin 2) GF4)) = _
  rw [Equiv.symm_apply_apply]

theorem eq_zero_of_const : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → (∀ i j, x i = x j) → x = 0 := by
  decide

theorem constWeight_five : constWeight 5 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [AddSubgroup.mem_bot]
  apply Subtype.ext
  have hx' : ∑ i, (x : Fin 5 → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  exact eq_zero_of_const _ hx' hx

@[expose] noncomputable def heartEquiv : AltHeart 5 ≃+ ↥(evenWeight 5) :=
  (QuotientAddGroup.quotientAddEquivOfEq constWeight_five).trans QuotientAddGroup.quotientBot

theorem heartEquiv_mk (x : ↥(evenWeight 5)) : heartEquiv (QuotientAddGroup.mk x) = x := rfl

theorem mk_heartEquiv (y : AltHeart 5) : (QuotientAddGroup.mk (heartEquiv y) : AltHeart 5) = y :=
  heartEquiv.injective (heartEquiv_mk _)

@[expose] noncomputable def hermMulEquiv :
    ↥(hermSub 1 (Fin 2) GF4) ≃* Multiplicative ↥(evenWeight 5) where
  toFun X := Multiplicative.ofAdd (hermToEven X)
  invFun y := hermEquiv.symm (Multiplicative.toAdd y)
  left_inv X := hermEquiv.symm_apply_apply X
  right_inv y := by
    show Multiplicative.ofAdd (hermEquiv (hermEquiv.symm (Multiplicative.toAdd y))) = y
    rw [Equiv.apply_symm_apply]
    rfl
  map_mul' X Y := by
    show Multiplicative.ofAdd (hermToEven (X * Y)) = _
    rw [hermToEven_mul]
    rfl

open scoped IsMulCommutative in
theorem binaryOrthogonalFour_of_altNatural {G : Type} [Group G] {A V : Subgroup G}
    [IsMulCommutative ↥V] {N : Subgroup ↥A} (h : IsAltNaturalSection A V ⊥ N 5) :
    BinaryOrthogonalFour (V := ↥V) (autOn A V) ⊤ ⊥ 1 := by
  obtain ⟨hAV, α, hα, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := h
  have hβ₀i : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₀k, Subgroup.bot_subgroupOf]
  have hrep : ∀ (a : ↥A) (w w' : ↥V), (w' : G) = a * w * (a : G)⁻¹ →
      heartEquiv (Multiplicative.toAdd (β₀ w')) =
        permWeight 5 (α a) (heartEquiv (Multiplicative.toAdd (β₀ w))) := by
    intro a w w' hw'
    have h1 := hβ₀e a w w' hw' (heartEquiv (Multiplicative.toAdd (β₀ w))) (mk_heartEquiv _)
    rw [← h1]
    rfl
  have hker : ∀ a : ↥A, α a = 1 → (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    set v' : ↥V := ⟨(a : G) * v * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp hv⟩ with hv'
    have h1 := hrep a ⟨v, hv⟩ v' rfl
    rw [ha] at h1
    have h2 : permWeight 5 ((1 : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
        (heartEquiv (Multiplicative.toAdd (β₀ ⟨v, hv⟩))) =
        heartEquiv (Multiplicative.toAdd (β₀ ⟨v, hv⟩)) := by
      apply Subtype.ext
      funext i
      rfl
    rw [h2] at h1
    have h3 : β₀ v' = β₀ ⟨v, hv⟩ :=
      Multiplicative.toAdd.injective (heartEquiv.injective h1)
    have h4 := congrArg Subtype.val (hβ₀i h3)
    simp only [hv'] at h4
    calc v * (a : G) = (a : G) * v * (a : G)⁻¹ * a := by rw [h4]
      _ = a * v := by group
  set ρ := T4213N.rhoAut hAV with hρ
  have hle : α.ker ≤ ρ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    apply Subtype.ext
    exact InternalSec.conjAct_eq_one_of_mem_centralizer _ (hker a ha)
  set e := QuotientGroup.quotientKerEquivOfSurjective α hα with he
  set π₀ : ↥(alternatingGroup (Fin 5)) →* ↥(autOn A V) :=
    (QuotientGroup.lift α.ker ρ hle).comp e.symm.toMonoidHom with hπ₀
  have hπ₀α : ∀ a : ↥A, π₀ (α a) = ρ a := by
    intro a
    have h1 : e.symm (α a) = (a : ↥A ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  set π : ↥(StatedSL 2 GF4) →* ↥(autOn A V) := π₀.comp slEquiv.toMonoidHom with hπ
  have hπs : Function.Surjective π := by
    intro χ
    obtain ⟨a, rfl⟩ := T4213N.rhoAut_surjective hAV χ
    refine ⟨slEquiv.symm (α a), ?_⟩
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hπ₀α]
  let fV : ↥V → ↥(hermSub 1 (Fin 2) GF4) := fun v =>
    hermEquiv.symm (heartEquiv (Multiplicative.toAdd (β₀ v)))
  have hfV_mul : ∀ v w, fV (v * w) = fV v * fV w := by
    intro v w
    show hermMulEquiv.symm (Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd (β₀ (v * w))))) =
      hermMulEquiv.symm (Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd (β₀ v)))) *
        hermMulEquiv.symm (Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd (β₀ w))))
    rw [← map_mul, map_mul, toAdd_mul, map_add, ofAdd_add]
  have hfV_one : fV 1 = 1 := by
    show hermMulEquiv.symm (Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd (β₀ 1)))) = 1
    rw [map_one, toAdd_one, map_zero, ofAdd_zero, map_one]
  have hfV_inj : ∀ v, fV v = 1 → v = 1 := by
    intro v hv
    have h1 : hermMulEquiv.symm (Multiplicative.ofAdd (heartEquiv (Multiplicative.toAdd (β₀ v)))) =
        1 := hv
    rw [MulEquiv.map_eq_one_iff] at h1
    have h2 : heartEquiv (Multiplicative.toAdd (β₀ v)) = 0 := h1
    rw [AddEquiv.map_eq_zero_iff] at h2
    have h3 : β₀ v = 1 := h2
    exact (map_eq_one_iff β₀ hβ₀i).mp h3
  have hfV_surj : ∀ m, ∃ v, fV v = m := by
    intro m
    obtain ⟨v, hv⟩ := hβ₀s (Multiplicative.ofAdd (heartEquiv.symm (hermEquiv m)))
    refine ⟨v, ?_⟩
    show hermEquiv.symm (heartEquiv (Multiplicative.toAdd (β₀ v))) = m
    rw [hv, toAdd_ofAdd, AddEquiv.apply_symm_apply, Equiv.symm_apply_apply]
  have hfV_act : ∀ (γ : ↥(StatedSL 2 GF4)) (v : ↥V),
      fV (((π γ : ↥(autOn A V)) : MulAut ↥V) v) =
        ⟨twistAct 1 (StatedSL 2 GF4) γ (fV v), twistAct_mem_hermSub 1 _ card_GF4 γ (fV v).2⟩ := by
    intro γ v
    obtain ⟨a, ha⟩ := hα (slEquiv γ)
    have hπa : π γ = ρ a := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← ha, hπ₀α]
    apply Subtype.ext
    rw [hπa]
    have hrv := hrep a v (((ρ a : ↥(autOn A V)) : MulAut ↥V) v) (T4213N.rhoAut_apply hAV a v)
    show ((hermEquiv.symm (heartEquiv (Multiplicative.toAdd
      (β₀ (((ρ a : ↥(autOn A V)) : MulAut ↥V) v)))) : ↥(hermSub 1 (Fin 2) GF4)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) GF4)) = _
    rw [hrv, ha, coe_slEquiv]
    exact hermEquiv_symm_permWeight γ _
  let β : ↥(⊤ : Subgroup ↥V) →* ↥(hermSub 1 (Fin 2) GF4) ⧸
      ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) GF4))).subgroupOf
        (hermSub 1 (Fin 2) GF4)) :=
    { toFun := fun u => QuotientGroup.mk (fV u)
      map_one' := by
        show QuotientGroup.mk (fV 1) = 1
        rw [hfV_one]
        rfl
      map_mul' := fun u u' => by
        show QuotientGroup.mk (fV ((u : ↥V) * u')) = _
        rw [hfV_mul]
        rfl }
  have hmk : ∀ x y : ↥(hermSub 1 (Fin 2) GF4),
      (QuotientGroup.mk x : ↥(hermSub 1 (Fin 2) GF4) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) GF4))).subgroupOf
          (hermSub 1 (Fin 2) GF4))) = QuotientGroup.mk y ↔ x = y := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_mul_eq_one]
    exact Subtype.ext_iff.symm
  refine ⟨GF4, inferInstance, inferInstance, inferInstance, card_GF4, π, hπs, bot_le, bot_le,
    fun _ _ _ => trivial, fun h z hz => ?_, fun γ m hm => twistAct_mem_hermSub 1 _ card_GF4 γ hm,
    fun γ m hm => ?_, β, ?_, fun u => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hm' : m = 1 := hm
    show twistAct 1 (StatedSL 2 GF4) γ m ∈ (⊥ : Subgroup _)
    rw [Subgroup.mem_bot, hm']
    exact act_map_one (twistAct 1 (StatedSL 2 GF4)) γ (twistAct_mul 1 _ γ)
  · intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨v, hv⟩ := hfV_surj m
      exact ⟨⟨v, trivial⟩, by
        show QuotientGroup.mk (fV v) = _
        rw [hv]
        rfl⟩
  · show (QuotientGroup.mk (fV u) : ↥(hermSub 1 (Fin 2) GF4) ⧸
        ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) GF4))).subgroupOf
          (hermSub 1 (Fin 2) GF4))) = 1 ↔ (u : ↥V) ∈ ⊥
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      exact hfV_inj u (Subtype.ext h)
    · intro h
      rw [h, hfV_one]
      rfl
  · intro γ u m hu hm hum
    have hum' : fV u = m := (hmk _ _).mp hum
    show (QuotientGroup.mk (fV (((π γ : ↥(autOn A V)) : MulAut ↥V) (u : ↥V))) :
        ↥(hermSub 1 (Fin 2) GF4) ⧸
          ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) GF4))).subgroupOf
            (hermSub 1 (Fin 2) GF4))) =
      QuotientGroup.mk (⟨twistAct 1 (StatedSL 2 GF4) γ m.1, hm⟩ : ↥(hermSub 1 (Fin 2) GF4))
    rw [hmk]
    refine (hfV_act γ (u : ↥V)).trans ?_
    apply Subtype.ext
    show twistAct 1 (StatedSL 2 GF4) γ (fV u).1 = twistAct 1 (StatedSL 2 GF4) γ m.1
    rw [hum']

theorem sum_pair :
    ∀ a b : Fin 5, ∑ i, ((Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2)) i = 0 := by
  decide +kernel

@[expose] def pairVec (a b : Fin 5) : ↥(evenWeight 5) :=
  ⟨(Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2), by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact sum_pair a b⟩

theorem three_cycle_add : ∀ (x : Fin 5 → ZMod 2) (i j k : Fin 5), i ≠ j → j ≠ k → i ≠ k →
    x i = 1 → x k = 1 → x j = 0 → ∀ m : Fin 5,
    x m + x ((Equiv.swap i j * Equiv.swap j k)⁻¹ m) =
      ((Pi.single j 1 + Pi.single k 1 : Fin 5 → ZMod 2)) m := by
  decide +kernel

theorem exists_three : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → x ≠ 0 →
    ∃ i j k : Fin 5, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i = 1 ∧ x k = 1 ∧ x j = 0 := by
  decide +kernel

theorem decomp_pairs : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 →
    x = ∑ i, (if i ≠ 0 ∧ x i = 1 then (Pi.single 0 1 + Pi.single i 1 : Fin 5 → ZMod 2) else 0) := by
  decide +kernel

theorem permWeight_pairVec (σ : Equiv.Perm (Fin 5)) (a b : Fin 5) :
    permWeight 5 σ (pairVec a b) = pairVec (σ a) (σ b) := by
  apply Subtype.ext
  funext m
  show (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) (σ⁻¹ m) =
    (Pi.single (σ a) 1 + Pi.single (σ b) 1 : Fin 5 → ZMod 2) m
  have h1 : (σ⁻¹ m = a) ↔ (m = σ a) := Equiv.Perm.inv_eq_iff_eq
  have h2 : (σ⁻¹ m = b) ↔ (m = σ b) := Equiv.Perm.inv_eq_iff_eq
  simp only [Pi.add_apply, Pi.single_apply, h1, h2]

theorem exists_alt5_pair {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : alternatingGroup (Fin 5), (σ : Equiv.Perm (Fin 5)) a = c ∧
      (σ : Equiv.Perm (Fin 5)) b = d := by
  have h3 := alternatingGroup.isMultiplyPretransitive (Fin 5)
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 5)) (Fin 5) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 5) - 2) (by simp) (by simp)
  let x : Fin 2 ↪ Fin 5 := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin 5 := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) x y
  refine ⟨g, ?_, ?_⟩
  · exact congrArg (fun z : Fin 2 ↪ Fin 5 => z 0) hg
  · exact congrArg (fun z : Fin 2 ↪ Fin 5 => z 1) hg

theorem evenWeight_eq_bot_or_top (X : AddSubgroup ↥(evenWeight 5))
    (hX : ∀ σ : alternatingGroup (Fin 5), ∀ x ∈ X, permWeight 5 (σ : Equiv.Perm (Fin 5)) x ∈ X) :
    X = ⊥ ∨ X = ⊤ := by
  by_cases hb : X = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨x, hxX⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hb
  have hx0 : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hxs : ∑ i, (x : Fin 5 → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have hx0' : (x : Fin 5 → ZMod 2) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨i, j, k, hij, hjk, hik, hi, hk, hj⟩ := exists_three _ hxs hx0'
  let τ : alternatingGroup (Fin 5) := ⟨Equiv.swap i j * Equiv.swap j k, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
      Equiv.Perm.sign_swap hjk]
    decide⟩
  have hpair : pairVec j k ∈ X := by
    have h1 := X.add_mem hxX (hX τ x hxX)
    have h2 : x + permWeight 5 (τ : Equiv.Perm (Fin 5)) x = pairVec j k := by
      apply Subtype.ext
      funext m
      exact three_cycle_add x i j k hij hjk hik hi hk hj m
    rw [h2] at h1
    exact h1
  have hall : ∀ a b : Fin 5, a ≠ b → pairVec a b ∈ X := by
    intro a b hab
    obtain ⟨σ, hσa, hσb⟩ := exists_alt5_pair hjk hab
    have h1 := hX σ _ hpair
    rwa [permWeight_pairVec, hσa, hσb] at h1
  rw [eq_top_iff]
  rintro w -
  have hws : ∑ i, (w : Fin 5 → ZMod 2) i = 0 := by
    have := w.2
    simpa [evenWeight] using this
  have hw : w = ∑ i, (if i ≠ 0 ∧ (w : Fin 5 → ZMod 2) i = 1 then pairVec 0 i else 0) := by
    apply Subtype.ext
    push_cast
    convert decomp_pairs _ hws using 2 with i
    split_ifs <;> rfl
  rw [hw]
  refine sum_mem fun i _ => ?_
  split_ifs with h
  · exact hall 0 i (Ne.symm h.1)
  · exact X.zero_mem

theorem eq_bot_or_eq_of_altNatural {G : Type} [Group G] {A V W : Subgroup G} {N : Subgroup ↥A}
    (h : IsAltNaturalSection A V ⊥ N 5) (hWV : W ≤ V)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  obtain ⟨hAV, α, hα, -, β₀, -, hβ₀k, hβ₀e⟩ := h
  have hβ₀i : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₀k, Subgroup.bot_subgroupOf]
  have hrep : ∀ (a : ↥A) (w w' : ↥V), (w' : G) = a * w * (a : G)⁻¹ →
      heartEquiv (Multiplicative.toAdd (β₀ w')) =
        permWeight 5 (α a) (heartEquiv (Multiplicative.toAdd (β₀ w))) := by
    intro a w w' hw'
    have h1 := hβ₀e a w w' hw' (heartEquiv (Multiplicative.toAdd (β₀ w))) (mk_heartEquiv _)
    rw [← h1]
    rfl
  let X : AddSubgroup ↥(evenWeight 5) :=
    { carrier := {x | ∃ w : ↥V, (w : G) ∈ W ∧ heartEquiv (Multiplicative.toAdd (β₀ w)) = x}
      zero_mem' := ⟨1, W.one_mem, by rw [map_one, toAdd_one, map_zero]⟩
      add_mem' := by
        rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
        exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by rw [map_mul, toAdd_mul, map_add]⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, by rw [map_inv, toAdd_inv, map_neg]⟩ }
  have hX : ∀ σ : alternatingGroup (Fin 5), ∀ x ∈ X,
      permWeight 5 (σ : Equiv.Perm (Fin 5)) x ∈ X := by
    rintro σ _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := hα σ
    refine ⟨⟨(a : G) * w * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hAV a.2) w).mp w.2⟩,
      (Subgroup.mem_normalizer_iff.mp (hAW a.2) w).mp hw, ?_⟩
    exact hrep a w _ rfl
  rcases evenWeight_eq_bot_or_top X hX with hb | ht
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : heartEquiv (Multiplicative.toAdd (β₀ ⟨w, hWV hw⟩)) ∈ X := ⟨_, hw, rfl⟩
    rw [hb, AddSubgroup.mem_bot, AddEquiv.map_eq_zero_iff] at h1
    have h2 : β₀ ⟨w, hWV hw⟩ = 1 := h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val ((map_eq_one_iff β₀ hβ₀i).mp h2)
  · right
    refine le_antisymm hWV fun v hv => ?_
    have h1 : heartEquiv (Multiplicative.toAdd (β₀ ⟨v, hv⟩)) ∈ X := by
      rw [ht]
      exact AddSubgroup.mem_top _
    obtain ⟨w, hw, hwv⟩ := h1
    have h2 : (w : G) = v :=
      congrArg Subtype.val (hβ₀i (Multiplicative.toAdd.injective (heartEquiv.injective hwv)))
    rw [← h2]
    exact hw

end CFSG.Quasithin.H13.Ch4.A5Herm
