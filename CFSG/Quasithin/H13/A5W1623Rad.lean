module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ln2P

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic CFSG.Quasithin

section Radical

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def InFlagRadical (i : ℕ) (g : SpecialLinearGroup (Fin n) K) : Prop :=
  (∀ v ∈ flagSpace n K i, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v) ∧
    ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ flagSpace n K i

theorem inFlagRadical_one (i : ℕ) : InFlagRadical i (1 : SpecialLinearGroup (Fin n) K) :=
  ⟨fun v _ => by simp, fun v => by simp⟩

theorem InFlagRadical.mul {i : ℕ} {g h : SpecialLinearGroup (Fin n) K} (hg : InFlagRadical i g)
    (hh : InFlagRadical i h) : InFlagRadical i (g * h) := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · change ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) *ᵥ v = v
    rw [← mulVec_mulVec, hh1 v hv, hg1 v hv]
  · change ((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) *ᵥ v - v ∈ _
    rw [← mulVec_mulVec]
    have e : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) - v =
        (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v - v) +
          ((g : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by
      rw [mulVec_sub]
      abel
    rw [e, hg1 _ (hh2 v)]
    exact Submodule.add_mem _ (hh2 v) (hg2 v)

theorem mulVec_inv_mulVec (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [mulVec_mulVec]
  have e : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    change ((g⁻¹ * g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [inv_mul_cancel]
    rfl
  rw [e, one_mulVec]

theorem mulVec_mulVec_inv (g : SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
  rw [mulVec_mulVec]
  have e : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    change ((g * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [mul_inv_cancel]
    rfl
  rw [e, one_mulVec]

theorem InFlagRadical.inv {i : ℕ} {g : SpecialLinearGroup (Fin n) K} (hg : InFlagRadical i g) :
    InFlagRadical i g⁻¹ := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h1 := mulVec_inv_mulVec g v
    rwa [hg1 v hv] at h1
  · set w := ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hw
    have e : w - v = -((g : Matrix (Fin n) (Fin n) K) *ᵥ w - w) := by
      rw [hw, mulVec_mulVec_inv]
      abel
    rw [e]
    exact Submodule.neg_mem _ (hg2 w)

@[expose] def flagRadical (n : ℕ) (K : Type*) [Field K] (i : ℕ) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | InFlagRadical i g}
  one_mem' := inFlagRadical_one i
  mul_mem' := fun hg hh => InFlagRadical.mul hg hh
  inv_mem' := fun hg => InFlagRadical.inv hg

theorem mulVec_mem_of_mem_stabilizer {W : Submodule K (Fin n → K)}
    {q : SpecialLinearGroup (Fin n) K} (hq : q ∈ stabilizer W) {v : Fin n → K} (hv : v ∈ W) :
    (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W := by
  have h1 : (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
      W.map (mulVecLin (q : Matrix (Fin n) (Fin n) K)) := ⟨v, hv, rfl⟩
  rwa [mem_stabilizer.mp hq] at h1

theorem InFlagRadical.conj {i : ℕ} {q r : SpecialLinearGroup (Fin n) K}
    (hq : q ∈ stabilizer (flagSpace n K i)) (hr : InFlagRadical i r) :
    InFlagRadical i (q * r * q⁻¹) := by
  obtain ⟨hr1, hr2⟩ := hr
  have hqi : q⁻¹ ∈ stabilizer (flagSpace n K i) := Subgroup.inv_mem _ hq
  have hc : ((q * r * q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (q : Matrix (Fin n) (Fin n) K) * (r : Matrix (Fin n) (Fin n) K) *
        ((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [hc, ← mulVec_mulVec, ← mulVec_mulVec, hr1 _ (mulVec_mem_of_mem_stabilizer hqi hv),
      mulVec_mulVec_inv]
  · rw [hc, ← mulVec_mulVec, ← mulVec_mulVec]
    have e : (q : Matrix (Fin n) (Fin n) K) *ᵥ ((r : Matrix (Fin n) (Fin n) K) *ᵥ
        (((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) - v =
        (q : Matrix (Fin n) (Fin n) K) *ᵥ ((r : Matrix (Fin n) (Fin n) K) *ᵥ
          (((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) -
          ((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
      rw [mulVec_sub, mulVec_mulVec_inv]
    rw [e]
    exact mulVec_mem_of_mem_stabilizer hq (hr2 _)

theorem stabilizer_le_normalizer_flagRadical (i : ℕ) :
    stabilizer (flagSpace n K i) ≤
      Subgroup.normalizer (flagRadical n K i : Set (SpecialLinearGroup (Fin n) K)) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => InFlagRadical.conj hq hr, fun hr => ?_⟩
  have h1 := InFlagRadical.conj (Subgroup.inv_mem _ hq) hr
  rwa [inv_inv, show q⁻¹ * (q * r * q⁻¹) * q = r by group] at h1

theorem flagRadical_le_stabilizer (i : ℕ) :
    flagRadical n K i ≤ stabilizer (flagSpace n K i) := by
  intro g hg
  refine le_antisymm ?_ fun v hv => ⟨v, hv, hg.1 v hv⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply, hg.1 v hv]
  exact hv

end Radical

theorem sl_ext_of_coe {n : ℕ} {K : Type*} [Field K] {g h : SpecialLinearGroup (Fin n) K}
    (e : (g : Matrix (Fin n) (Fin n) K) = h) : g = h :=
  Subtype.ext e

theorem InFlagRadical.mul_self_eq_one {n i : ℕ} {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : InFlagRadical i g) : g * g = 1 := by
  obtain ⟨hg1, hg2⟩ := hg
  have key : ∀ v, ((g : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ
      v = v := by
    intro v
    have h2 : ∀ x : Fin n → ZMod 2, x + x = 0 := fun x => by
      ext j
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero (x j)
    have hw := hg1 _ (hg2 v)
    set w := (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v with hwdef
    have e : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v + w := by
      rw [hwdef]
      abel
    rw [← mulVec_mulVec]
    calc (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v)
        = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (v + w) := by rw [e]
      _ = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v +
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w := mulVec_add _ _ _
      _ = v + w + w := by rw [e, hw]
      _ = v := by rw [add_assoc, h2, add_zero]
  apply sl_ext_of_coe
  change (g : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1
  ext a b
  have h1 := congrFun (key (Pi.single b 1)) a
  rw [mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

theorem isPGroup_flagRadical (n i : ℕ) : IsPGroup 2 ↥(flagRadical n (ZMod 2) i) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, sq]
    exact InFlagRadical.mul_self_eq_one g.2)⟩

theorem flagRadical_le_pCoreOf (n : ℕ) :
    flagRadical n (ZMod 2) 2 ≤ pCoreOf 2 (flagStabilizer n (ZMod 2) {2}) := by
  have hQ : flagStabilizer n (ZMod 2) {2} = stabilizer (flagSpace n (ZMod 2) 2) := by
    simp [flagStabilizer]
  rw [hQ]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (flagRadical_le_stabilizer 2)
    (stabilizer_le_normalizer_flagRadical 2) (isPGroup_flagRadical n 2)

@[expose] def tau01 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

@[expose] def tau23 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1], by decide⟩

@[expose] noncomputable def levi1 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  reflection 4 (ZMod 2) 1 le_rfl (by norm_num) * tau01

@[expose] noncomputable def levi3 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  reflection 4 (ZMod 2) 3 (by norm_num) (by norm_num) * tau23

@[expose] def mD1 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mD1i : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mD3 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def mD3i : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]

@[expose] def mW0 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def mN (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, a, b, c; 0, 0, d, e; 0, 0, 0, f; 0, 0, 0, 0]

theorem coeM_mul (a b : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ((a * b : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (a : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (b : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  Matrix.SpecialLinearGroup.coe_mul a b

theorem coeM_pow (a : SpecialLinearGroup (Fin 4) (ZMod 2)) (k : ℕ) :
    ((a ^ k : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (a : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ k :=
  Matrix.SpecialLinearGroup.coe_pow a k

theorem coeM_one :
    ((1 : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 :=
  Matrix.SpecialLinearGroup.coe_one

theorem coe_levi1 : (levi1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = mD1 := by
  decide +kernel

theorem coe_levi3 : (levi3 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = mD3 := by
  decide +kernel

theorem coe_inv_eq_of_mul_eq_one {g : SpecialLinearGroup (Fin 4) (ZMod 2)}
    {m' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * m' = 1) :
    ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = m' := by
  calc ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
      = ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * m') := by rw [h, Matrix.mul_one]
    _ = m' := by
      have e : ((g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
        change ((g⁻¹ * g : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
        rw [inv_mul_cancel]
        rfl
      rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem coe_levi1_inv : ((levi1⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = mD1i :=
  coe_inv_eq_of_mul_eq_one (by rw [coe_levi1]; decide)

theorem coe_levi3_inv : ((levi3⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) = mD3i :=
  coe_inv_eq_of_mul_eq_one (by rw [coe_levi3]; decide)

theorem levi1_pow_three : levi1 ^ 3 = 1 := by
  apply sl_ext_of_coe
  change (levi1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 3 = 1
  rw [coe_levi1]
  decide

theorem levi3_pow_three : levi3 ^ 3 = 1 := by
  apply sl_ext_of_coe
  change (levi3 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 3 = 1
  rw [coe_levi3]
  decide

theorem tau01_mem_unitriangular : tau01 ∈ unitriangular 4 (ZMod 2) := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem tau23_mem_unitriangular : tau23 ∈ unitriangular 4 (ZMod 2) := by
  refine mem_unitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem levi1_mem : levi1 ∈ flagStabilizer 4 (ZMod 2) {2} :=
  Subgroup.mul_mem _ (((subflag_stabilizer_generation (K := ZMod 2) (n := 4) {2}).2.2 1 le_rfl
    (by norm_num)).mpr (by simp)) (unitriangular_le_flagStabilizer _ tau01_mem_unitriangular)

theorem levi3_mem : levi3 ∈ flagStabilizer 4 (ZMod 2) {2} :=
  Subgroup.mul_mem _ (((subflag_stabilizer_generation (K := ZMod 2) (n := 4) {2}).2.2 3
    (by norm_num) (by norm_num)).mpr (by simp))
    (unitriangular_le_flagStabilizer _ tau23_mem_unitriangular)

theorem coe_eq_of_mem_unitriangular {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hu : u ∈ unitriangular 4 (ZMod 2)) :
    (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + mN ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1)
      ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2) ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3)
      ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2) ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3)
      ((u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3) := by
  obtain ⟨hl, hd⟩ := hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mN] <;>
    first | exact hd _ | exact hl _ _ (by decide)

theorem one_add_mN_mul : ∀ a b c d e f : ZMod 2, (1 + mN a b c d e f) *
    (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
      mN a b c d e f * mN a b c d e f * mN a b c d e f) = 1 := by
  decide +kernel

theorem mW0_mul_self : mW0 * mW0 = 1 := by decide

theorem permMatrix_revPerm_four :
    permMatrix 4 (ZMod 2) (Fin.revPerm : Equiv.Perm (Fin 4)) = mW0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pow_twelve_graph_mat : ∀ a b c d e f : ZMod 2,
    (mW0 * ((1 + mN a b c d e f) * mD1i * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
      mN a b c d e f * mN a b c d e f * mN a b c d e f))ᵀ * mW0 * mD1i) ^ 12 = 1 ∧
    (mW0 * ((1 + mN a b c d e f) * mD1i * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
      mN a b c d e f * mN a b c d e f * mN a b c d e f))ᵀ * mW0 * mD1i) ^ 4 ≠ 1 := by
  decide +kernel

theorem pow_twelve_inner_mat : ∀ a b c d e f : ZMod 2, (a ≠ 0 ∨ f ≠ 0) →
    (((1 + mN a b c d e f) * mD1 * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f) * mD1i) ^ 12 = 1 ∧
      ((1 + mN a b c d e f) * mD1 * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f) * mD1i) ^ 4 ≠ 1) ∨
    (((1 + mN a b c d e f) * mD3 * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f) * mD3i) ^ 12 = 1 ∧
      ((1 + mN a b c d e f) * mD3 * (1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f) * mD3i) ^ 4 ≠ 1) := by
  decide +kernel

theorem mem_flagRadical_of_entries {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hu : u ∈ unitriangular 4 (ZMod 2)) (h01 : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1 = 0)
    (h23 : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3 = 0) : u ∈ flagRadical 4 (ZMod 2) 2 := by
  have hcoe := coe_eq_of_mem_unitriangular hu
  rw [h01, h23] at hcoe
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h2 := (mem_flagSpace.mp hv) 2 le_rfl
    have h3 := (mem_flagSpace.mp hv) 3 (by decide)
    rw [hcoe]
    ext j
    fin_cases j <;> simp [mN, mulVec, dotProduct, Fin.sum_univ_four, h2, h3]
  · rw [mem_flagSpace]
    intro j hj
    rw [hcoe]
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · simp [mN, mulVec, dotProduct, Fin.sum_univ_four]
    · simp [mN, mulVec, dotProduct, Fin.sum_univ_four]

theorem false_of_pow_twelve {M : Type*} [Monoid M] {h : M} (h12 : h ^ 12 = 1) (h4 : h ^ 4 ≠ 1)
    {e : ℕ} (he : h ^ 2 ^ e = 1) : False := by
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one he)
  have h1 : 2 ^ j ∣ 12 := hjo ▸ orderOf_dvd_of_pow_eq_one h12
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := this.trans h1
    norm_num at this
  apply h4
  rw [← orderOf_dvd_iff_pow_eq_one, hjo]
  exact pow_dvd_pow 2 hj2

theorem pow_twelve_graph {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hu : u ∈ unitriangular 4 (ZMod 2)) :
    (graphAut 4 (u * levi1 * u⁻¹) * levi1⁻¹) ^ 12 = 1 ∧
      (graphAut 4 (u * levi1 * u⁻¹) * levi1⁻¹) ^ 4 ≠ 1 := by
  set a := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1
  set b := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2
  set c := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3
  set d := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2
  set e := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3
  set f := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3
  have hcoe : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + mN a b c d e f :=
    coe_eq_of_mem_unitriangular hu
  have hinv : ((u⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f :=
    coe_inv_eq_of_mul_eq_one (by rw [hcoe]; exact one_add_mN_mul a b c d e f)
  have hm : ((graphAut 4 (u * levi1 * u⁻¹) * levi1⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      mW0 * ((1 + mN a b c d e f) * mD1i * (1 + mN a b c d e f +
        mN a b c d e f * mN a b c d e f + mN a b c d e f * mN a b c d e f * mN a b c d e f))ᵀ *
        mW0 * mD1i := by
    rw [coeM_mul, coe_graphAut, permMatrix_revPerm_four, Matrix.inv_eq_left_inv mW0_mul_self,
      show (u * levi1 * u⁻¹)⁻¹ = u * levi1⁻¹ * u⁻¹ by group, coeM_mul, coeM_mul, hcoe,
      coe_levi1_inv, hinv]
  obtain ⟨h12, h4⟩ := pow_twelve_graph_mat a b c d e f
  refine ⟨sl_ext_of_coe ?_, fun h => h4 ?_⟩
  · rw [coeM_pow, hm, h12, coeM_one]
  · rw [← hm, ← coeM_pow, h, coeM_one]

theorem pow_twelve_inner {u : SpecialLinearGroup (Fin 4) (ZMod 2)}
    (hu : u ∈ unitriangular 4 (ZMod 2)) (hR : u ∉ flagRadical 4 (ZMod 2) 2) :
    ((u * levi1 * u⁻¹ * levi1⁻¹) ^ 12 = 1 ∧ (u * levi1 * u⁻¹ * levi1⁻¹) ^ 4 ≠ 1) ∨
      ((u * levi3 * u⁻¹ * levi3⁻¹) ^ 12 = 1 ∧ (u * levi3 * u⁻¹ * levi3⁻¹) ^ 4 ≠ 1) := by
  set a := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1
  set b := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2
  set c := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3
  set d := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2
  set e := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3
  set f := (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3
  have hcoe : (u : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + mN a b c d e f :=
    coe_eq_of_mem_unitriangular hu
  have hinv : ((u⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      1 + mN a b c d e f + mN a b c d e f * mN a b c d e f +
        mN a b c d e f * mN a b c d e f * mN a b c d e f :=
    coe_inv_eq_of_mul_eq_one (by rw [hcoe]; exact one_add_mN_mul a b c d e f)
  have haf : a ≠ 0 ∨ f ≠ 0 := by
    by_contra h
    push Not at h
    exact hR (mem_flagRadical_of_entries hu h.1 h.2)
  have hm1 : ((u * levi1 * u⁻¹ * levi1⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = (1 + mN a b c d e f) * mD1 * (1 + mN a b c d e f +
        mN a b c d e f * mN a b c d e f + mN a b c d e f * mN a b c d e f * mN a b c d e f) *
        mD1i := by
    rw [coeM_mul, coeM_mul, coeM_mul, hcoe, coe_levi1, hinv, coe_levi1_inv]
  have hm3 : ((u * levi3 * u⁻¹ * levi3⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = (1 + mN a b c d e f) * mD3 * (1 + mN a b c d e f +
        mN a b c d e f * mN a b c d e f + mN a b c d e f * mN a b c d e f * mN a b c d e f) *
        mD3i := by
    rw [coeM_mul, coeM_mul, coeM_mul, hcoe, coe_levi3, hinv, coe_levi3_inv]
  rcases pow_twelve_inner_mat a b c d e f haf with ⟨h12, h4⟩ | ⟨h12, h4⟩
  · refine Or.inl ⟨sl_ext_of_coe ?_, fun h => h4 ?_⟩
    · rw [coeM_pow, hm1, h12, coeM_one]
    · rw [← hm1, ← coeM_pow, h, coeM_one]
  · refine Or.inr ⟨sl_ext_of_coe ?_, fun h => h4 ?_⟩
    · rw [coeM_pow, hm3, h12, coeM_one]
    · rw [← hm3, ← coeM_pow, h, coeM_one]

end CFSG.Quasithin.H13.Ln2P
