
module

public import CFSG.Quasithin.Background.B4ModelsApi
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Matrix

theorem act_map_one {A B : Type*} [Group B] (f : A → B → B) (γ : A)
    (h : ∀ x y, f γ (x * y) = f γ x * f γ y) : f γ 1 = 1 := by
  have h11 := h 1 1
  rw [mul_one] at h11
  exact (mul_left_cancel (a := f γ 1) (by rw [mul_one]; exact h11)).symm

theorem FFModel.isActionModel_of_top_bot (D : FFModel) (hsec : D.sec = ⊤) (hker : D.ker = ⊥)
    (act_mul : ∀ (γ : D.Gam) (x y : D.Amb), D.act γ (x * y) = D.act γ x * D.act γ y)
    (act_one : ∀ x : D.Amb, D.act 1 x = x)
    (act_mul_act : ∀ (γ δ : D.Gam) (x : D.Amb), D.act (γ * δ) x = D.act γ (D.act δ x)) :
    D.IsActionModel where
  act_mul := act_mul
  act_one := act_one
  act_mul_act := act_mul_act
  sec_inv _ _ _ := by rw [hsec]; trivial
  ker_inv γ m hm := by
    rw [hker, Subgroup.mem_bot] at hm ⊢
    rw [hm]
    exact act_map_one D.act γ (act_mul γ)
  ker_le := by rw [hker]; exact bot_le

section Natural

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))

theorem natAct_mul (g : ↥Γ) (x y : Multiplicative (ι → K)) :
    natAct Γ g (x * y) = natAct Γ g x * natAct Γ g y := by
  simp [natAct, Matrix.mulVec_add]

theorem natAct_one (x : Multiplicative (ι → K)) : natAct Γ 1 x = x := by
  simp [natAct]

theorem natAct_mul_act (g h : ↥Γ) (x : Multiplicative (ι → K)) :
    natAct Γ (g * h) x = natAct Γ g (natAct Γ h x) := by
  simp [natAct, Matrix.mulVec_mulVec]

theorem FFModel.nat_isActionModel : (FFModel.nat Γ).IsActionModel :=
  FFModel.isActionModel_of_top_bot _ rfl rfl (natAct_mul Γ) (natAct_one Γ) (natAct_mul_act Γ)

theorem dualNatAct_mul (g : ↥Γ) (x y : Multiplicative (ι → K)) :
    dualNatAct Γ g (x * y) = dualNatAct Γ g x * dualNatAct Γ g y := by
  simp [dualNatAct, Matrix.mulVec_add]

theorem dualNatAct_one (x : Multiplicative (ι → K)) : dualNatAct Γ 1 x = x := by
  simp [dualNatAct]

theorem dualNatAct_mul_act (g h : ↥Γ) (x : Multiplicative (ι → K)) :
    dualNatAct Γ (g * h) x = dualNatAct Γ g (dualNatAct Γ h x) := by
  simp [dualNatAct, Matrix.mulVec_mulVec, mul_inv_rev, Matrix.transpose_mul]

theorem FFModel.dualNat_isActionModel : (FFModel.dualNat Γ).IsActionModel :=
  FFModel.isActionModel_of_top_bot _ rfl rfl (dualNatAct_mul Γ) (dualNatAct_one Γ)
    (dualNatAct_mul_act Γ)

end Natural

section Dn

theorem permAct_one_act (n : ℕ) (x : G6.PermMod n) : G6.permAct n 1 x = x := by
  rw [map_one]
  rfl

theorem permAct_mul_act (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (x : G6.PermMod n) :
    G6.permAct n (σ * τ) x = G6.permAct n σ (G6.permAct n τ x) := by
  rw [map_mul]
  rfl

theorem permAct_allOnes (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    G6.permAct n σ (G6.allOnes n) = G6.allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, G6.allOnes]

theorem permAct_mem_ker (n : ℕ) (σ : Equiv.Perm (Fin n)) {m : G6.PermMod n}
    (hm : m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) :
    G6.permAct n σ m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := by
  obtain ⟨hz, hcore⟩ := hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩, G6.permAct_mem_coreMod σ hcore⟩
  rw [← hk, map_zpow, permAct_allOnes]
  rfl

theorem FFModel.symDn_isActionModel (n : ℕ) : (FFModel.symDn n).IsActionModel where
  act_mul σ x y := map_mul (G6.permAct n σ) x y
  act_one x := permAct_one_act n x
  act_mul_act σ τ x := permAct_mul_act n σ τ x
  sec_inv σ _ hm := G6.permAct_mem_coreMod σ hm
  ker_inv σ _ hm := permAct_mem_ker n σ hm
  ker_le := fun _ hx => hx.2

theorem FFModel.altDn_isActionModel (n : ℕ) : (FFModel.altDn n).IsActionModel where
  act_mul := fun (σ : ↥(alternatingGroup (Fin n))) x y =>
    map_mul (G6.permAct n (σ : Equiv.Perm (Fin n))) x y
  act_one := fun x => permAct_one_act n x
  act_mul_act := fun (σ τ : ↥(alternatingGroup (Fin n))) x => permAct_mul_act n (σ : Equiv.Perm (Fin n)) τ x
  sec_inv := fun (σ : ↥(alternatingGroup (Fin n))) _ hm => G6.permAct_mem_coreMod (σ : Equiv.Perm (Fin n)) hm
  ker_inv := fun (σ : ↥(alternatingGroup (Fin n))) _ hm => permAct_mem_ker n (σ : Equiv.Perm (Fin n)) hm
  ker_le := fun _ hx => hx.2

end Dn

section A7

theorem a7Act_mul (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (σ : ↥(alternatingGroup (Fin 7))) (x y : Multiplicative (Fin 4 → ZMod 2)) :
    a7Act α σ (x * y) = a7Act α σ x * a7Act α σ y := by
  simp [a7Act, Matrix.mulVec_add]

theorem a7Act_one (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (x : Multiplicative (Fin 4 → ZMod 2)) : a7Act α 1 x = x := by
  have h1 : altLift7 (1 : ↥(alternatingGroup (Fin 7))) = 1 := map_one _
  simp [a7Act, h1]

theorem a7Act_mul_act (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (σ τ : ↥(alternatingGroup (Fin 7))) (x : Multiplicative (Fin 4 → ZMod 2)) :
    a7Act α (σ * τ) x = a7Act α σ (a7Act α τ x) := by
  have h1 : altLift7 (σ * τ) = altLift7 σ * altLift7 τ := map_mul _ _ _
  simp [a7Act, h1, Matrix.mulVec_mulVec]

theorem FFModel.a7Four_isActionModel
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    (FFModel.a7Four α).IsActionModel :=
  FFModel.isActionModel_of_top_bot _ rfl rfl (a7Act_mul α) (a7Act_one α) (a7Act_mul_act α)

end A7

section Exterior

variable (K : Type) [Field K] (d : ℕ)

theorem extSqAct_mul (g : ↥(StatedSL d K)) (x y : Multiplicative (⋀[K]^2 (Fin d → K))) :
    extSqAct K d g (x * y) = extSqAct K d g x * extSqAct K d g y := by
  simp [extSqAct]

theorem extSqAct_one (x : Multiplicative (⋀[K]^2 (Fin d → K))) : extSqAct K d 1 x = x := by
  simp [extSqAct, Matrix.toLin'_one, exteriorPower.map_id]

theorem extSqAct_mul_act (g h : ↥(StatedSL d K)) (x : Multiplicative (⋀[K]^2 (Fin d → K))) :
    extSqAct K d (g * h) x = extSqAct K d g (extSqAct K d h x) := by
  simp [extSqAct, Matrix.toLin'_mul, exteriorPower.map_comp]

theorem FFModel.extSq_isActionModel : (FFModel.extSq K d).IsActionModel :=
  FFModel.isActionModel_of_top_bot _ rfl rfl (extSqAct_mul K d) (extSqAct_one K d)
    (extSqAct_mul_act K d)

end Exterior

section Twisted

theorem frobPow_eq_map {ι : Type} {F : Type} [Field F] [CharP F 2] (a : ℕ) (X : Matrix ι ι F) :
    frobPow a X = X.map (iterateFrobenius F 2 a) := by
  ext i j
  simp [frobPow, iterateFrobenius_def]

theorem frobPow_mul {ι : Type} [Fintype ι] {F : Type} [Field F] [CharP F 2] (a : ℕ)
    (X Y : Matrix ι ι F) : frobPow a (X * Y) = frobPow a X * frobPow a Y := by
  rw [frobPow_eq_map, frobPow_eq_map, frobPow_eq_map]
  exact Matrix.map_mul

theorem frobPow_one {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [CharP F 2] (a : ℕ) :
    frobPow a (1 : Matrix ι ι F) = 1 := by
  rw [frobPow_eq_map]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem frobPow_transpose {ι : Type} {F : Type} [Field F] (a : ℕ) (X : Matrix ι ι F) :
    frobPow a Xᵀ = (frobPow a X)ᵀ := by
  ext i j
  simp [frobPow]

theorem frobPow_frobPow {ι : Type} {F : Type} [Field F] [Finite F] (a : ℕ)
    (hF : Nat.card F = 2 ^ (2 * a)) (X : Matrix ι ι F) : frobPow a (frobPow a X) = X := by
  ext i j
  simp only [frobPow, Matrix.map_apply]
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ (2 * a) := by rw [← hF, Nat.card_eq_fintype_card]
  rw [← pow_mul, ← pow_add, ← two_mul, ← hcard]
  exact FiniteField.pow_card _

end Twisted

section TwistedAction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [CharP F 2] (a : ℕ)
  (Γ : Subgroup (Matrix.GeneralLinearGroup ι F))

omit [CharP F 2] in
theorem twistAct_mul (g : ↥Γ) (X Y : Multiplicative (Matrix ι ι F)) :
    twistAct a Γ g (X * Y) = twistAct a Γ g X * twistAct a Γ g Y := by
  simp [twistAct, mul_add, add_mul]

theorem twistAct_one (X : Multiplicative (Matrix ι ι F)) : twistAct a Γ 1 X = X := by
  simp [twistAct, frobPow_one]

theorem twistAct_mul_act (g h : ↥Γ) (X : Multiplicative (Matrix ι ι F)) :
    twistAct a Γ (g * h) X = twistAct a Γ g (twistAct a Γ h X) := by
  simp [twistAct, frobPow_mul, Matrix.transpose_mul, Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem mem_hermSub {X : Multiplicative (Matrix ι ι F)} :
    X ∈ hermSub a ι F ↔ (frobPow a (Multiplicative.toAdd X))ᵀ = Multiplicative.toAdd X := Iff.rfl

theorem twistAct_mem_hermSub [Finite F] (hF : Nat.card F = 2 ^ (2 * a)) (g : ↥Γ)
    {X : Multiplicative (Matrix ι ι F)} (hX : X ∈ hermSub a ι F) :
    twistAct a Γ g X ∈ hermSub a ι F := by
  rw [mem_hermSub] at hX ⊢
  simp only [twistAct, toAdd_ofAdd]
  have e1 : frobPow a (((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) * Multiplicative.toAdd X *
      (frobPow a ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F))ᵀ) =
      frobPow a ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) * frobPow a (Multiplicative.toAdd X) *
        ((g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)ᵀ := by
    rw [frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow a hF]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX]
  simp [Matrix.mul_assoc]

theorem FFModel.twistTensor_isActionModel [Finite F] (hF : Nat.card F = 2 ^ (2 * a)) :
    (FFModel.twistTensor a Γ).IsActionModel where
  act_mul := twistAct_mul a Γ
  act_one := twistAct_one a Γ
  act_mul_act := twistAct_mul_act a Γ
  sec_inv γ m hm := twistAct_mem_hermSub a Γ hF γ hm
  ker_inv γ m hm := by
    have h1 : m = 1 := hm
    rw [h1]
    show twistAct a Γ γ 1 ∈ (⊥ : Subgroup (Multiplicative (Matrix ι ι F)))
    rw [Subgroup.mem_bot]
    exact act_map_one (twistAct a Γ) γ (twistAct_mul a Γ γ)
  ker_le := bot_le

end TwistedAction

section Zorn
variable {K : Type} [Field K]

@[expose] def zornOne : quasithinZorn K := (1, 0, 0, 1)

theorem zornMul_one_left (y : quasithinZorn K) : quasithinZornMul zornOne y = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp [quasithinZornMul, zornOne, quasithinCross]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp

theorem zornMul_one_right (y : quasithinZorn K) : quasithinZornMul y zornOne = y := by
  obtain ⟨r, u, v, s⟩ := y
  simp [quasithinZornMul, zornOne, quasithinCross]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp

theorem quasithinCross_self (u : Fin 3 → K) : quasithinCross u u = 0 := by
  funext i
  fin_cases i <;> simp [quasithinCross] <;> ring

theorem zornMul_self (x : quasithinZorn K) :
    quasithinZornMul x x = (x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i, (x.1 + x.2.2.2) • x.2.1,
      (x.1 + x.2.2.2) • x.2.2.1, x.2.2.2 * x.2.2.2 + ∑ i, x.2.2.1 i * x.2.1 i) := by
  obtain ⟨r, u, v, s⟩ := x
  simp only [quasithinZornMul, quasithinCross_self]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  · funext i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

@[expose] def IsZornAuto (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) : Prop :=
  ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)

theorem IsZornAuto.map_one {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g) :
    g zornOne = zornOne := by
  have h := hg zornOne (g.symm zornOne)
  rw [zornMul_one_left, LinearEquiv.apply_symm_apply, zornMul_one_right] at h
  exact h.symm

theorem IsZornAuto.map_smul_one {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g)
    (c : K) : g ((c, 0, 0, c) : quasithinZorn K) = (c, 0, 0, c) := by
  have h1 : ((c, 0, 0, c) : quasithinZorn K) = c • zornOne := by
    simp [zornOne]
  rw [h1, map_smul, hg.map_one]

theorem IsZornAuto.trace_zero [CharP K 2] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : IsZornAuto g) {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0) :
    (g x).1 + (g x).2.2.2 = 0 := by
  have hs : x.2.2.2 = x.1 := by
    have := eq_neg_of_add_eq_zero_right hx
    rw [this, CharTwo.neg_eq]
  set N : K := x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i with hN
  have hxx : quasithinZornMul x x = ((N, 0, 0, N) : quasithinZorn K) := by
    rw [zornMul_self]
    have h0 : x.1 + x.2.2.2 = 0 := hx
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [h0]
    · simp [h0]
    · simp only [hs, hN]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hyy := hg x x
  rw [hxx, hg.map_smul_one] at hyy
  set y := g x with hy
  have hyy' := zornMul_self y
  rw [← hyy] at hyy'
  have h1 := congrArg Prod.fst hyy'
  have h4 := congrArg (fun z => z.2.2.2) hyy'
  simp only at h1 h4
  have hsum : ∑ i, y.2.1 i * y.2.2.1 i = ∑ i, y.2.2.1 i * y.2.1 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsq : y.1 * y.1 = y.2.2.2 * y.2.2.2 := by
    have : y.1 * y.1 + ∑ i, y.2.1 i * y.2.2.1 i = y.2.2.2 * y.2.2.2 + ∑ i, y.2.2.1 i * y.2.1 i := by
      rw [← h1, ← h4]
    rw [hsum] at this
    exact add_right_cancel this
  have h2 : (y.1 + y.2.2.2) * (y.1 + y.2.2.2) = 0 := by
    have hc : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (y.1 + y.2.2.2) * (y.1 + y.2.2.2)
        = y.1 * y.1 + y.2.2.2 * y.2.2.2 + 2 * (y.1 * y.2.2.2) := by ring
      _ = 0 := by rw [hc, zero_mul, add_zero, hsq, CharTwo.add_self_eq_zero]
  exact mul_self_eq_zero.mp h2

theorem mem_quasithinG2_isZornAuto {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) : IsZornAuto g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => intro x y; rfl
  | mul g h _ _ hg hh =>
    intro x y
    show g (h (quasithinZornMul x y)) = quasithinZornMul (g (h x)) (g (h y))
    rw [hh, hg]
  | inv g _ hg =>
    intro x y
    have h1 := hg (g⁻¹ x) (g⁻¹ y)
    have e1 : g (g⁻¹ x) = x := LinearEquiv.apply_symm_apply g x
    have e2 : g (g⁻¹ y) = y := LinearEquiv.apply_symm_apply g y
    rw [e1, e2] at h1
    show g.symm (quasithinZornMul x y) = quasithinZornMul (g.symm x) (g.symm y)
    rw [← h1]
    exact LinearEquiv.symm_apply_apply g _

variable (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K))

theorem zornAct_mul (g : ↥Γ) (x y : Multiplicative (quasithinZorn K)) :
    zornAct Γ g (x * y) = zornAct Γ g x * zornAct Γ g y := by
  simp [zornAct]

theorem zornAct_one (x : Multiplicative (quasithinZorn K)) : zornAct Γ 1 x = x := by
  simp [zornAct]

theorem zornAct_mul_act (g h : ↥Γ) (x : Multiplicative (quasithinZorn K)) :
    zornAct Γ (g * h) x = zornAct Γ g (zornAct Γ h x) := by
  simp [zornAct]

theorem zornAct_mem_O0 [CharP K 2] (hΓ : Γ ≤ quasithinG2 K) (g : ↥Γ)
    {x : Multiplicative (quasithinZorn K)} (hx : x ∈ zornO0 K) : zornAct Γ g x ∈ zornO0 K :=
  (mem_quasithinG2_isZornAuto (hΓ g.2)).trace_zero hx

theorem zornAct_mem_R [CharP K 2] (hΓ : Γ ≤ quasithinG2 K) (g : ↥Γ)
    {x : Multiplicative (quasithinZorn K)} (hx : x ∈ zornR K) : zornAct Γ g x ∈ zornR K := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, ?_⟩
  show (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd x) = (c, 0, 0, c)
  rw [hc]
  exact (mem_quasithinG2_isZornAuto (hΓ g.2)).map_smul_one c

theorem zornR_le_zornO0 [CharP K 2] : zornR K ≤ zornO0 K := by
  rintro m ⟨c, hc⟩
  show (Multiplicative.toAdd m).1 + (Multiplicative.toAdd m).2.2.2 = 0
  rw [hc]
  exact CharTwo.add_self_eq_zero c

theorem FFModel.zornQ_isActionModel [CharP K 2] (hΓ : Γ ≤ quasithinG2 K) :
    (FFModel.zornQ Γ).IsActionModel where
  act_mul := zornAct_mul Γ
  act_one := zornAct_one Γ
  act_mul_act := zornAct_mul_act Γ
  sec_inv := fun γ _ hm => zornAct_mem_O0 Γ hΓ γ hm
  ker_inv := fun γ _ hm => zornAct_mem_R Γ hΓ γ hm
  ker_le := zornR_le_zornO0

end Zorn

section Golay

open CFSG.Monster.Code

theorem mem_golayC_iff {c : G6.PermMod 24} : c ∈ golayC ↔ Multiplicative.toAdd c ∈ CFSG.Monster.Code.C :=
  Iff.rfl

theorem allOnes_eq_Omega : Multiplicative.toAdd (G6.allOnes 24) = CFSG.Monster.Code.Ω := rfl

theorem allOnes_mem_golayC : G6.allOnes 24 ∈ golayC := by
  rw [mem_golayC_iff, allOnes_eq_Omega]
  exact Ω_mem_C

theorem golayC_le_coreMod : golayC ≤ G6.coreMod 24 := by
  intro c hc
  rw [G6.mem_coreMod]
  have h4 := four_dvd_wt (mem_golayC_iff.mp hc)
  rw [sum_eq_hammingNorm]
  have h2 : 2 ∣ hammingNorm (Multiplicative.toAdd c) := Nat.dvd_trans (by norm_num) h4
  exact (ZMod.natCast_eq_zero_iff _ 2).mpr h2

theorem golayC_inv {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {m : G6.PermMod 24} (hm : m ∈ golayC) :
    G6.permAct 24 σ m ∈ golayC := by
  rw [mem_golayC_iff] at hm ⊢
  have h := (mem_AutPerm_iff.mp (AutPerm.inv_mem hσ) (Multiplicative.toAdd m)).mp hm
  have e : Multiplicative.toAdd (G6.permAct 24 σ m) = Multiplicative.toAdd m ∘ ⇑σ⁻¹ := by
    funext i
    exact G6.permAct_apply 24 σ m i
  rw [e]
  exact h

theorem permAct_mem_zpowers_allOnes (n : ℕ) (σ : Equiv.Perm (Fin n)) {m : G6.PermMod n}
    (hm : m ∈ Subgroup.zpowers (G6.allOnes n)) : G6.permAct n σ m ∈ Subgroup.zpowers (G6.allOnes n) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hk, map_zpow]
  have : G6.permAct n σ (G6.allOnes n) = G6.allOnes n := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [G6.permAct_apply, G6.allOnes]
  rw [this]
  rfl

theorem permAct_mem_sup {M : Type*} [CommGroup M] (f : MulAut M) {A B : Subgroup M}
    (hA : ∀ m ∈ A, f m ∈ A) (hB : ∀ m ∈ B, f m ∈ B) {m : M} (hm : m ∈ A ⊔ B) : f m ∈ A ⊔ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hm
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA a ha) (hB b hb)

theorem permAct_mem_closure {M : Type*} [CommGroup M] (f : MulAut M) {S : Set M}
    (hS : ∀ m ∈ S, f m ∈ Subgroup.closure S) {m : M} (hm : m ∈ Subgroup.closure S) :
    f m ∈ Subgroup.closure S := by
  induction hm using Subgroup.closure_induction with
  | mem m hm => exact hS m hm
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem unitVec_apply (x i : Fin 24) : Multiplicative.toAdd (unitVec x) i = if i = x then 1 else 0 := by
  simp [unitVec, Pi.single_apply]

theorem permAct_unitVec (σ : Equiv.Perm (Fin 24)) (x : Fin 24) :
    G6.permAct 24 σ (unitVec x) = unitVec (σ x) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, unitVec_apply, unitVec_apply]
  simp [Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem permAct_pairVec_of_fix {σ : Equiv.Perm (Fin 24)} {x y : Fin 24} (hx : σ x = x) (hy : σ y = y) :
    G6.permAct 24 σ (pairVec x y) = pairVec x y := by
  rw [pairVec, map_mul, permAct_unitVec, permAct_unitVec, hx, hy]

theorem pairKer_inv {σ : Equiv.Perm (Fin 24)} {x y : Fin 24} (hx : σ x = x) (hy : σ y = y)
    {m : G6.PermMod 24} (hm : m ∈ pairKer x y) : G6.permAct 24 σ m ∈ pairKer x y := by
  have hx' : σ⁻¹ x = x := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hx.symm
  have hy' : σ⁻¹ y = y := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hy.symm
  show (Multiplicative.toAdd (G6.permAct 24 σ m)) x + (Multiplicative.toAdd (G6.permAct 24 σ m)) y = 0
  rw [G6.permAct_apply, G6.permAct_apply, hx', hy']
  exact hm

theorem pairVec_mem_core (x y : Fin 24) : pairVec x y ∈ G6.coreMod 24 := by
  rw [G6.mem_coreMod]
  simp only [pairVec, unitVec, toAdd_mul, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib]
  simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
  decide

theorem allOnes_mem_pairKer (x y : Fin 24) : G6.allOnes 24 ∈ pairKer x y := by
  show (Multiplicative.toAdd (G6.allOnes 24)) x + (Multiplicative.toAdd (G6.allOnes 24)) y = 0
  show (1 : ZMod 2) + 1 = 0
  decide

theorem permSubAct_mul (Γ : Subgroup (Equiv.Perm (Fin 24))) (σ : ↥Γ) (x y : G6.PermMod 24) :
    permSubAct Γ σ (x * y) = permSubAct Γ σ x * permSubAct Γ σ y :=
  map_mul (G6.permAct 24 (σ : Equiv.Perm (Fin 24))) x y

theorem permSubAct_one (Γ : Subgroup (Equiv.Perm (Fin 24))) (x : G6.PermMod 24) :
    permSubAct Γ 1 x = x := permAct_one_act 24 x

theorem permSubAct_mul_act (Γ : Subgroup (Equiv.Perm (Fin 24))) (σ τ : ↥Γ) (x : G6.PermMod 24) :
    permSubAct Γ (σ * τ) x = permSubAct Γ σ (permSubAct Γ τ x) :=
  permAct_mul_act 24 (σ : Equiv.Perm (Fin 24)) τ x

theorem FFModel.golaySec_isActionModel (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (numer denom : Subgroup (G6.PermMod 24))
    (hnum : ∀ σ : ↥Γ, ∀ m ∈ numer, permSubAct Γ σ m ∈ numer)
    (hden : ∀ σ : ↥Γ, ∀ m ∈ denom, permSubAct Γ σ m ∈ denom) (hle : denom ≤ numer) :
    (FFModel.golaySec Γ numer denom).IsActionModel where
  act_mul := permSubAct_mul Γ
  act_one := permSubAct_one Γ
  act_mul_act := permSubAct_mul_act Γ
  sec_inv := hnum
  ker_inv := hden
  ker_le := hle

theorem golayCode_isActionModel (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    (FFModel.golaySec Γ golayC (Subgroup.zpowers (G6.allOnes 24))).IsActionModel :=
  FFModel.golaySec_isActionModel Γ golayC (Subgroup.zpowers (G6.allOnes 24))
    (fun σ _ hm => golayC_inv (hΓ σ.2) hm)
    (fun σ _ hm => permAct_mem_zpowers_allOnes 24 σ hm)
    (Subgroup.zpowers_le.mpr allOnes_mem_golayC)

theorem golayCocode_isActionModel (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) :
    (FFModel.golaySec Γ (G6.coreMod 24) golayC).IsActionModel :=
  FFModel.golaySec_isActionModel Γ (G6.coreMod 24) golayC
    (fun σ _ hm => G6.permAct_mem_coreMod (σ : Equiv.Perm (Fin 24)) hm)
    (fun σ _ hm => golayC_inv (hΓ σ.2) hm)
    golayC_le_coreMod

theorem mem_stabilizer_fix {x : Fin 24} {σ : Equiv.Perm (Fin 24)}
    (h : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 24)) x) : σ x = x :=
  MulAction.mem_stabilizer_iff.mp h

theorem stab_facts (x y : Fin 24) (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) (σ : ↥Γ) :
    (σ : Equiv.Perm (Fin 24)) ∈ AutPerm ∧ (σ : Equiv.Perm (Fin 24)) x = x ∧
      (σ : Equiv.Perm (Fin 24)) y = y := by
  have h := hΓ σ.2
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at h
  exact ⟨h.1.1, mem_stabilizer_fix h.1.2, mem_stabilizer_fix h.2⟩

theorem code22_sec_inv (x y : Fin 24) (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) (σ : ↥Γ) (m : G6.PermMod 24)
    (hm : m ∈ golayC ⊓ pairKer x y) : permSubAct Γ σ m ∈ golayC ⊓ pairKer x y := by
  obtain ⟨h1, h2, h3⟩ := stab_facts x y Γ hΓ σ
  rw [Subgroup.mem_inf] at hm ⊢
  exact ⟨golayC_inv h1 hm.1, pairKer_inv h2 h3 hm.2⟩

theorem golayCode22_isActionModel (x y : Fin 24) (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) :
    (FFModel.golaySec Γ (golayC ⊓ pairKer x y) (Subgroup.zpowers (G6.allOnes 24))).IsActionModel :=
  FFModel.golaySec_isActionModel Γ (golayC ⊓ pairKer x y) (Subgroup.zpowers (G6.allOnes 24))
    (fun σ m hm => code22_sec_inv x y Γ hΓ σ m hm)
    (fun σ _ hm => permAct_mem_zpowers_allOnes 24 σ hm)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨allOnes_mem_golayC, allOnes_mem_pairKer x y⟩))

theorem cocode22_ker_inv (x y : Fin 24) (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) (σ : ↥Γ) (m : G6.PermMod 24)
    (hm : m ∈ golayC ⊔ Subgroup.zpowers (pairVec x y)) :
    permSubAct Γ σ m ∈ golayC ⊔ Subgroup.zpowers (pairVec x y) := by
  obtain ⟨h1, h2, h3⟩ := stab_facts x y Γ hΓ σ
  refine permAct_mem_sup (G6.permAct 24 (σ : Equiv.Perm (Fin 24)))
    (fun m hm' => golayC_inv h1 hm') (fun m hm' => ?_) hm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm'
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hk]
  show (pairVec x y) ^ k = G6.permAct 24 (σ : Equiv.Perm (Fin 24)) ((pairVec x y) ^ k)
  rw [map_zpow, permAct_pairVec_of_fix h2 h3]
  rfl

theorem golayCocode22_isActionModel (x y : Fin 24) (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hΓ : Γ ≤ AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) :
    (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec x y))).IsActionModel :=
  FFModel.golaySec_isActionModel Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec x y))
    (fun σ _ hm => G6.permAct_mem_coreMod (σ : Equiv.Perm (Fin 24)) hm)
    (fun σ m hm => cocode22_ker_inv x y Γ hΓ σ m hm)
    (sup_le golayC_le_coreMod (Subgroup.zpowers_le.mpr (pairVec_mem_core x y)))

theorem m12Ten_isActionModel (eY : G6.PermMod 24) (hY : eY ∈ golayC) :
    (FFModel.golaySec (m24Fix eY) golayC (Subgroup.closure {G6.allOnes 24, eY})).IsActionModel :=
  FFModel.golaySec_isActionModel _ _ _
    (fun σ _ hm => golayC_inv σ.2.1 hm)
    (fun σ _ hm => permAct_mem_closure _ (fun m hm' => by
      rcases hm' with rfl | rfl
      · have : G6.permAct 24 (σ : Equiv.Perm (Fin 24)) (G6.allOnes 24) = G6.allOnes 24 := by
          apply Multiplicative.toAdd.injective
          funext i
          simp [G6.permAct_apply, G6.allOnes]
        show G6.permAct 24 (σ : Equiv.Perm (Fin 24)) (G6.allOnes 24) ∈ _
        rw [this]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · show G6.permAct 24 (σ : Equiv.Perm (Fin 24)) m ∈ _
        rw [σ.2.2]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hm)
    ((Subgroup.closure_le _).mpr (by
      intro m hm'
      rcases hm' with rfl | rfl
      · exact allOnes_mem_golayC
      · exact hY))

end Golay

section Satisfiable

private theorem commutator_le_self_aux {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

theorem exists_alternatingNatural (n : ℕ) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), AlternatingNatural H ⊤ ⊥ n :=
  ⟨_, inferInstance, _, (FFModel.altDn_isActionModel n).realizesMod_range⟩

theorem exists_symmetricNatural (n : ℕ) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), SymmetricNatural H ⊤ ⊥ n :=
  ⟨_, inferInstance, _, (FFModel.symDn_isActionModel n).realizesMod_range⟩

theorem exists_binaryNaturalSL (d a : ℕ) (ha : a ≠ 0) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), BinaryNaturalSL H ⊤ ⊥ d a :=
  ⟨_, inferInstance, _, GaloisField 2 a, inferInstance, inferInstance,
    GaloisField.card 2 a ha, (FFModel.nat_isActionModel _).realizesMod_range⟩

theorem exists_g2Natural (a : ℕ) (ha : a ≠ 0) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), G2Natural H ⊤ ⊥ a :=
  ⟨_, inferInstance, _, GaloisField 2 a, inferInstance, inferInstance, GaloisField.card 2 a ha,
    (FFModel.zornQ_isActionModel (quasithinG2 (GaloisField 2 a)) le_rfl).realizesMod_range⟩

theorem exists_g2NaturalDerived (a : ℕ) (ha : a ≠ 0) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), G2NaturalDerived H ⊤ ⊥ a :=
  ⟨_, inferInstance, _, GaloisField 2 a, inferInstance, inferInstance, GaloisField.card 2 a ha,
    (FFModel.zornQ_isActionModel ⁅quasithinG2 (GaloisField 2 a), quasithinG2 (GaloisField 2 a)⁆
      (commutator_le_self_aux _)).realizesMod_range⟩

theorem exists_slExteriorTwo (d : ℕ) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), SLExteriorTwo H ⊤ ⊥ d :=
  ⟨_, inferInstance, _, (FFModel.extSq_isActionModel (ZMod 2) d).realizesMod_range⟩

theorem exists_twistedTensorSL (d a : ℕ) (ha : a ≠ 0) :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), TwistedTensorSL H ⊤ ⊥ d a :=
  ⟨_, inferInstance, _, GaloisField 2 (2 * a), inferInstance, inferInstance, inferInstance,
    GaloisField.card 2 (2 * a) (by omega),
    (FFModel.twistTensor_isActionModel a _ (GaloisField.card 2 (2 * a) (by omega))).realizesMod_range⟩

theorem exists_mathieuCode24 :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), MathieuCode24 H ⊤ ⊥ :=
  ⟨_, inferInstance, _,
    (golayCode_isActionModel CFSG.Monster.Code.AutPerm le_rfl).realizesMod_range⟩

theorem exists_mathieuCocode24 :
    ∃ (V : Type) (_ : CommGroup V) (H : Subgroup (MulAut V)), MathieuCocode24 H ⊤ ⊥ :=
  ⟨_, inferInstance, _,
    (golayCocode_isActionModel CFSG.Monster.Code.AutPerm le_rfl).realizesMod_range⟩

end Satisfiable

end CFSG.Quasithin
