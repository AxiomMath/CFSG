module

public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.C4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.FFn

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

section Transport

variable {G : Type} [Group G]

open scoped IsMulCommutative in
theorem isFFModule_autOn_of_equiv {A W : Subgroup G} [IsMulCommutative ↥W]
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) {Γ M : Type*} [Group Γ] [CommGroup M]
    (act : Γ →* MulAut M) (α : ↥A →* Γ) (hα : Function.Surjective α) (f : ↥W ≃* M)
    (hf : ∀ (a : ↥A) (w w' : ↥W), (w' : G) = a * w * (a : G)⁻¹ → f w' = act (α a) (f w))
    (hFF : IsFFModule act.range) : IsFFModule (autOn A W) := by
  rw [← E3.isFFModule_map_congr_iff f]
  refine B1Red.isFFModule_mono ?_ hFF
  rintro _ ⟨γ, rfl⟩
  obtain ⟨a, rfl⟩ := hα γ
  refine ⟨conjAct W ⟨a, hAW a.2⟩, Setup.mem_autOn_iff.mpr ⟨⟨a, hAW a.2⟩, a.2, rfl⟩, ?_⟩
  ext m
  obtain ⟨w, rfl⟩ := f.surjective m
  have hw := hf a w (conjAct W ⟨a, hAW a.2⟩ w) (Setup.coe_conjAct_apply _ _)
  show f (conjAct W ⟨a, hAW a.2⟩ (f.symm (f w))) = _
  rw [MulEquiv.symm_apply_apply]
  exact hw

end Transport

section Diag

@[expose] noncomputable def diagAct (m k : ℕ) (F : Type) [Field F] :
    Matrix.GeneralLinearGroup (Fin m) F →* MulAut (Multiplicative (Fin k → Fin m → F)) where
  toFun g :=
    { toFun := fun x => Multiplicative.ofAdd fun i =>
        (g : Matrix (Fin m) (Fin m) F) *ᵥ (Multiplicative.toAdd x i)
      invFun := fun x => Multiplicative.ofAdd fun i =>
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ
          (Multiplicative.toAdd x i)
      left_inv := fun x => by
        apply Multiplicative.toAdd.injective
        funext i
        simp [Matrix.mulVec_mulVec]
      right_inv := fun x => by
        apply Multiplicative.toAdd.injective
        funext i
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext x i j
    simp
  map_mul' g h := by
    ext x i j
    simp [Matrix.mulVec_mulVec]

variable {m : ℕ} {F : Type} [Field F]

theorem toAdd_diagAct (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin m) F)
    (x : Multiplicative (Fin k → Fin m → F)) (i : Fin k) :
    Multiplicative.toAdd (diagAct m k F g x) i =
      (g : Matrix (Fin m) (Fin m) F) *ᵥ (Multiplicative.toAdd x i) := rfl

end Diag

section Transvections

variable {n : ℕ} {F : Type} [Field F]

@[expose] def axisVecs (n : ℕ) (F : Type) [Field F] : AddSubgroup (Fin (n + 1) → F) :=
  (Pi.evalAddMonoidHom (fun _ => F) (Fin.last n)).ker

theorem mem_axisVecs {w : Fin (n + 1) → F} : w ∈ axisVecs n F ↔ w (Fin.last n) = 0 :=
  AddMonoidHom.mem_ker

@[expose] def tvMat (w : Fin (n + 1) → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  1 + Matrix.vecMulVec w (Pi.single (Fin.last n) 1)

theorem tvMat_mulVec (w x : Fin (n + 1) → F) : tvMat w *ᵥ x = x + x (Fin.last n) • w := by
  rw [tvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  congr 1
  ext i
  simp [single_dotProduct, mul_comm]

theorem tvMat_mul {w w' : Fin (n + 1) → F} (hw' : w' (Fin.last n) = 0) :
    tvMat w * tvMat w' = tvMat (w + w') := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, tvMat_mulVec, tvMat_mulVec, tvMat_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw', mul_zero, add_zero, smul_add]
  abel

theorem tvMat_zero : tvMat (0 : Fin (n + 1) → F) = 1 := by
  simp [tvMat]

theorem det_tvMat {w : Fin (n + 1) → F} (hw : w (Fin.last n) = 0) : (tvMat w).det = 1 := by
  rw [tvMat, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    single_dotProduct, hw, mul_zero, add_zero]

@[expose] noncomputable def tvSL (w : ↥(axisVecs n F)) : ↥(StatedSL (n + 1) F) :=
  ⟨⟨tvMat (w : Fin (n + 1) → F), tvMat (-(w : Fin (n + 1) → F)),
      by rw [tvMat_mul (by simp [mem_axisVecs.mp w.2]), add_neg_cancel, tvMat_zero],
      by rw [tvMat_mul (mem_axisVecs.mp w.2), neg_add_cancel, tvMat_zero]⟩,
    Subgroup.subset_closure (show (tvMat (w : Fin (n + 1) → F)).det = 1 from
      det_tvMat (mem_axisVecs.mp w.2))⟩

@[expose] noncomputable def tvHom (n : ℕ) (F : Type) [Field F] :
    Multiplicative ↥(axisVecs n F) →* ↥(StatedSL (n + 1) F) where
  toFun w := tvSL (Multiplicative.toAdd w)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show tvMat (0 : Fin (n + 1) → F) = 1
    exact tvMat_zero
  map_mul' w w' := by
    apply Subtype.ext
    apply Units.ext
    show tvMat _ = tvMat _ * tvMat _
    rw [tvMat_mul (mem_axisVecs.mp (Multiplicative.toAdd w').2)]
    rfl

end Transvections

section Model

variable {n k : ℕ} {F : Type} [Field F]

@[expose] noncomputable def slAct (n k : ℕ) (F : Type) [Field F] :
    ↥(StatedSL (n + 1) F) →* MulAut (Multiplicative (Fin k → Fin (n + 1) → F)) :=
  (diagAct (n + 1) k F).comp (StatedSL (n + 1) F).subtype

theorem toAdd_slAct_tvHom (a : Multiplicative ↥(axisVecs n F))
    (x : Multiplicative (Fin k → Fin (n + 1) → F)) (i : Fin k) :
    Multiplicative.toAdd (slAct n k F (tvHom n F a) x) i =
      Multiplicative.toAdd x i +
        Multiplicative.toAdd x i (Fin.last n) • ((Multiplicative.toAdd a : ↥(axisVecs n F)) :
          Fin (n + 1) → F) := by
  show tvMat _ *ᵥ _ = _
  exact tvMat_mulVec _ _

@[expose] def lastHom (n k : ℕ) (F : Type) [Field F] :
    Multiplicative (Fin k → Fin (n + 1) → F) →* Multiplicative (Fin k → F) where
  toFun x := Multiplicative.ofAdd fun i => Multiplicative.toAdd x i (Fin.last n)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem lastHom_surjective : Function.Surjective (lastHom n k F) := by
  intro y
  refine ⟨Multiplicative.ofAdd fun i => Pi.single (Fin.last n) (Multiplicative.toAdd y i), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [lastHom]

theorem card_lastHom_ker [Finite F] :
    Nat.card ↥(lastHom n k F).ker * Nat.card F ^ k =
      Nat.card (Multiplicative (Fin k → Fin (n + 1) → F)) := by
  have h := Subgroup.card_mul_index (lastHom n k F).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr lastHom_surjective, Subgroup.card_top] at h
  rw [← h]
  congr 1
  show _ = Nat.card (Fin k → F)
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]

theorem card_axisVecs [Finite F] :
    Nat.card ↥(axisVecs n F) * Nat.card F = Nat.card F ^ (n + 1) := by
  have h := AddSubgroup.card_mul_index (axisVecs n F)
  have hs : Function.Surjective (Pi.evalAddMonoidHom (fun _ : Fin (n + 1) => F) (Fin.last n)) :=
    fun c => ⟨fun _ => c, rfl⟩
  rw [axisVecs, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs,
    AddSubgroup.card_top] at h
  rw [axisVecs, h, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (n + 1)), Fintype.card_fin]

theorem isFFModule_slAct_range [Finite F] (hF : (2 : F) = 0) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    IsFFModule (slAct n k F).range := by
  set φ := (slAct n k F).comp (tvHom n F) with hφ
  have hφapp : ∀ (a : Multiplicative ↥(axisVecs n F)) (x : Multiplicative (Fin k → Fin (n + 1) → F))
      (i : Fin k), Multiplicative.toAdd (φ a x) i = Multiplicative.toAdd x i +
        Multiplicative.toAdd x i (Fin.last n) • ((Multiplicative.toAdd a : ↥(axisVecs n F)) :
          Fin (n + 1) → F) := fun a x i => toAdd_slAct_tvHom a x i
  have hn0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h := congrArg (fun χ : MulAut (Multiplicative (Fin k → Fin (n + 1) → F)) =>
      Multiplicative.toAdd (χ (Multiplicative.ofAdd fun _ => Pi.single (Fin.last n) (1 : F)))
        ⟨0, hk1⟩) ha
    simp only [hφapp, MulAut.one_apply, toAdd_ofAdd, Pi.single_eq_same, one_smul,
      add_eq_left] at h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h
  set E := φ.range with hE
  have hw₀ : (Pi.single 0 1 : Fin (n + 1) → F) ∈ axisVecs n F := by
    rw [mem_axisVecs, Pi.single_eq_of_ne hn0.symm]
  set a₀ : Multiplicative ↥(axisVecs n F) := Multiplicative.ofAdd ⟨_, hw₀⟩ with ha₀
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hmem : φ a₀ ∈ E := ⟨a₀, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one φ] at hmem
    have h1 := congrArg (fun a : Multiplicative ↥(axisVecs n F) =>
      ((Multiplicative.toAdd a : ↥(axisVecs n F)) : Fin (n + 1) → F) 0) (hinj hmem)
    simp [ha₀] at h1
  have hEab : IsElemAbelian2 E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext j
        simp only [toAdd_pow, toAdd_one, AddSubgroup.coe_nsmul, Pi.smul_apply,
          AddSubgroup.coe_zero, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat, hF, zero_mul]
      rw [this, map_one]
  have hfix : fixV E = (lastHom n k F).ker := by
    ext x
    rw [mem_fixV, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h := hx (φ a₀) ⟨a₀, rfl⟩
      apply Multiplicative.toAdd.injective
      funext i
      have hi := congrArg (fun y : Multiplicative (Fin k → Fin (n + 1) → F) =>
        Multiplicative.toAdd y i 0) h
      simp only [hφapp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha₀, toAdd_ofAdd,
        Pi.single_eq_same, mul_one, add_eq_left] at hi
      exact hi
    · rintro hx _ ⟨a, rfl⟩
      apply Multiplicative.toAdd.injective
      funext i
      have hi : Multiplicative.toAdd x i (Fin.last n) = 0 :=
        congrFun (congrArg Multiplicative.toAdd hx) i
      rw [hφapp, hi, zero_smul, add_zero]
  refine ⟨E, ?_, hEne, hEab, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨tvHom n F a, rfl⟩
  have hq : 0 < Nat.card F := Nat.card_pos
  have hcE : Nat.card E = Nat.card ↥(axisVecs n F) := by
    rw [hE, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
    rfl
  have hax := card_axisVecs (n := n) (F := F)
  have hker := card_lastHom_ker (n := n) (k := k) (F := F)
  rw [hfix, hcE]
  have hax' : Nat.card ↥(axisVecs n F) = Nat.card F ^ n := by
    rw [pow_succ] at hax
    exact Nat.eq_of_mul_eq_mul_right hq hax
  have hpow : Nat.card F ^ k ≤ Nat.card F ^ n := Nat.pow_le_pow_right hq hkn
  have hkpos : 0 < Nat.card F ^ k := pow_pos hq k
  refine Nat.le_of_mul_le_mul_right ?_ hkpos
  calc Nat.card (Multiplicative (Fin k → Fin (n + 1) → F)) * Nat.card F ^ k
      ≤ Nat.card (Multiplicative (Fin k → Fin (n + 1) → F)) * Nat.card ↥(axisVecs n F) := by
        rw [hax']
        exact Nat.mul_le_mul_left _ hpow
    _ = Nat.card ↥(axisVecs n F) * Nat.card ↥(lastHom n k F).ker * Nat.card F ^ k := by
        rw [← hker]
        ring

end Model

open scoped IsMulCommutative in
theorem isFFModule_autOn_of_sum {G : Type} [Group G] {A V : Subgroup G} [IsMulCommutative ↥V]
    {N : Subgroup ↥A} {n k : ℕ} {F : Type} [Field F] [Finite F] (hF : (2 : F) = 0)
    (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (h : IsSumOfNaturalModules A V ⊥ N (StatedSL (n + 1) F) false k) :
    IsFFModule (autOn A V) := by
  obtain ⟨α, hα, -, hAV, -, β, hβ, hβker, hβeq⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  refine isFFModule_autOn_of_equiv hAV (slAct n k F) α hα (MulEquiv.ofBijective β ⟨hinj, hβ⟩)
    (fun a w w' hw' => ?_) (isFFModule_slAct_range hF hk1 hkn)
  apply Multiplicative.toAdd.injective
  funext i
  have := hβeq a w w' hw' i
  show Multiplicative.toAdd (β w') i = Multiplicative.toAdd (slAct n k F (α a) (β w)) i
  rw [slAct, MonoidHom.comp_apply, toAdd_diagAct]
  simpa [moduleAct] using this

end CFSG.Quasithin.H13.Ch4.FFn
