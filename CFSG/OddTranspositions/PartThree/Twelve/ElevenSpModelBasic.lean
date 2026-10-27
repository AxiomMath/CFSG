module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModel
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType
import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
import CFSG.RankThree.OrthogonalInvolutions.Witt
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.HardMathSupport.GuralnickMalle.CyclicTwo

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open QuadraticMap
open CFSG.Timmesfeld.Bridge CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.UnbalancedCatalog (polar_self_charTwo)

variable {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
  (hQ₀ : ∀ a b, QuadraticMap.polar Q₀ a b = spForm k F a b)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
@[simp] theorem mForm_apply (X : MSpace k F) :
    mForm Q₀ X = X.1.1 ^ 2 + X.1.1 * X.1.2 + Q₀ X.2 := by
  rw [mForm, QuadraticMap.prod_apply, CFSG.GroupTheory.WeirSylow.binForm_apply]
  ring

omit [Fintype F] [DecidableEq F] in
private theorem polar_binForm_one_zero (v w : F × F) :
    polar (CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0) v w = v.1 * w.2 + w.1 * v.2 := by
  rw [polar, CFSG.GroupTheory.WeirSylow.binForm_apply,
    CFSG.GroupTheory.WeirSylow.binForm_apply,
    CFSG.GroupTheory.WeirSylow.binForm_apply]
  simp only [Prod.fst_add, Prod.snd_add]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (v.1 * w.1) * h2

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
theorem polar_mForm (X Y : MSpace k F) :
    polar (mForm Q₀) X Y = X.1.1 * Y.1.2 + Y.1.1 * X.1.2 + spForm k F X.2 Y.2 := by
  rw [mForm, QuadraticMap.polar_prod, polar_binForm_one_zero, hQ₀]

omit [Fintype F] [DecidableEq F] in
theorem polar_mU_eq_snd (Y : MSpace k F) : polar (mForm Q₀) mU Y = Y.1.2 := by
  rw [mForm, QuadraticMap.polar_prod, mU, polar_binForm_one_zero]
  simp

include hQ₀ in
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem mStabForm_apply (Y : MSpace k F) (x : Fin k ⊕ Fin k → F) :
    mStabForm Q₀ Y x = Q₀ x + spForm k F ((Y.1.2)⁻¹ • Y.2) x ^ 2 := by
  rw [mStabForm, QuadraticMap.add_apply, QuadraticMap.linMulLin_apply,
    polarBilin_apply_apply, hQ₀]
  ring

include hQ₀ in
omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem nondegenerate_polarBilin_mForm : (polarBilin (mForm Q₀)).Nondegenerate := by
  have hb : (polarBilin (CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0)).Nondegenerate :=
    CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.nondegenerate_polarBilin_binForm
      (b := 1) (c := 0) (by norm_num)
  have hsp : (polarBilin Q₀).Nondegenerate := by
    rw [show polarBilin Q₀ = spForm k F from LinearMap.ext₂ hQ₀]
    exact spForm_nondegenerate
  have := CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_prod hb hsp
  simpa [mForm] using this

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem finrank_mSpace : Module.finrank F (MSpace k F) = 2 * (k + 1) := by
  change Module.finrank F ((F × F) × (Fin k ⊕ Fin k → F)) = 2 * (k + 1)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

omit [DecidableEq F] in
@[simp] theorem mForm_mLift (x : Fin k ⊕ Fin k → F) : mForm Q₀ (mLift Q₀ x) = 1 := by
  rw [mForm_apply]
  change (frobeniusEquiv F 2).symm (1 + Q₀ x) ^ 2 +
    (frobeniusEquiv F 2).symm (1 + Q₀ x) * 0 + Q₀ x = 1
  have h : ((frobeniusEquiv F 2).symm (1 + Q₀ x)) ^ 2 = 1 + Q₀ x := by
    have := frobenius_apply_frobeniusEquiv_symm F 2 (1 + Q₀ x)
    rwa [frobenius_def] at this
  rw [h, mul_zero, add_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero]

omit [DecidableEq F] in
@[simp] theorem polar_mU_mLift (x : Fin k ⊕ Fin k → F) :
    polar (mForm Q₀) mU (mLift Q₀ x) = 0 := by
  rw [mForm, QuadraticMap.polar_prod, mU, mLift, polar_binForm_one_zero]
  simp

omit [DecidableEq F] in
theorem mLift_zero : mLift Q₀ (0 : Fin k ⊕ Fin k → F) = mU := by
  have h1 : (frobeniusEquiv F 2).symm (1 : F) = 1 := by
    apply (frobeniusEquiv F 2).injective
    rw [RingEquiv.apply_symm_apply, map_one]
  rw [mLift, QuadraticMap.map_zero, add_zero, h1]
  rfl

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma mRefl_mul_self (X : MSpace k F) : mRefl Q₀ X * mRefl Q₀ X = 1 := by
  apply Subtype.ext
  exact CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (mForm Q₀) X

omit [Fintype F] [DecidableEq F] in
theorem mRefl_apply_of_mForm_eq_one {X : MSpace k F} (hX : mForm Q₀ X = 1)
    (Y : MSpace k F) :
    (mRefl Q₀ X : MSpace k F ≃ₗ[F] MSpace k F) Y =
      Y + polar (mForm Q₀) X Y • X := by
  change CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) X Y = _
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by rw [hX]; exact one_ne_zero), hX,
    div_one, sub_eq_add_neg,
    CFSG.ClassicalGroups.Orthogonal.neg_eq_self_of_two_eq_zero (K := F) (V := MSpace k F)
      (CharTwo.two_eq_zero (R := F))]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem mRefl_mem_centralizer_of_polar_eq_zero {X Y : MSpace k F}
    (hXY : polar (mForm Q₀) X Y = 0) : mRefl Q₀ X ∈ Subgroup.centralizer {mRefl Q₀ Y} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero hXY)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma conj_mul_self_inv {sv sw g : MGroup Q₀}
    (hsv : sv * sv = 1) (hsw : sw * sw = 1) (hg : g = sv * sw) :
    sv * g * sv = g⁻¹ ∧ sw * g * sw = g⁻¹ := by
  have hsv' : sv⁻¹ = sv := inv_eq_of_mul_eq_one_left hsv
  have hsw' : sw⁻¹ = sw := inv_eq_of_mul_eq_one_left hsw
  have hg_inv : g⁻¹ = sw * sv := by
    rw [hg, mul_inv_rev, hsv', hsw']
  constructor
  · rw [hg_inv, hg]
    rw [show sv * (sv * sw) * sv = (sv * sv) * sw * sv by group, hsv, one_mul]
  · rw [hg_inv, hg]
    rw [show sw * (sv * sw) * sw = sw * sv * (sw * sw) by group, hsw, mul_one]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma conj_mul_self_inv_pow {sv sw g z : MGroup Q₀} (m : ℕ)
    (hsv : sv * sv = 1) (hsw : sw * sw = 1) (hg : g = sv * sw)
    (hz : z = g ^ m) (hz2 : z * z = 1) :
    z * sv * z⁻¹ = sv ∧ z * sw * z⁻¹ = sw := by
  have hsv' : sv⁻¹ = sv := inv_eq_of_mul_eq_one_left hsv
  have hsw' : sw⁻¹ = sw := inv_eq_of_mul_eq_one_left hsw
  obtain ⟨hconj_sv, hconj_sw⟩ := conj_mul_self_inv hsv hsw hg
  have hz_sv : sv * z * sv = z := by
    have h1 : (sv * g * sv) ^ m = sv * z * sv := by
      have hcp := conj_pow (a := sv) (b := g) (i := m)
      rw [hsv'] at hcp
      simpa [hz] using hcp
    rw [← h1, hconj_sv, inv_pow, ← hz, inv_eq_of_mul_eq_one_right hz2]
  have hz_sw : sw * z * sw = z := by
    have h1 : (sw * g * sw) ^ m = sw * z * sw := by
      have hcp := conj_pow (a := sw) (b := g) (i := m)
      rw [hsw'] at hcp
      simpa [hz] using hcp
    rw [← h1, hconj_sw, inv_pow, ← hz, inv_eq_of_mul_eq_one_right hz2]
  constructor
  · have hcomm : Commute z sv := by
      rw [commute_iff_eq]
      rw [show z * sv = (sv * z * sv) * sv by rw [hz_sv]]
      rw [mul_assoc, mul_assoc, hsv, mul_one]
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  · have hcomm : Commute z sw := by
      rw [commute_iff_eq]
      rw [show z * sw = (sw * z * sw) * sw by rw [hz_sw]]
      rw [mul_assoc, mul_assoc, hsw, mul_one]
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma mRefl_mul_fixes_of_polar_eq_zero {X Y y : MSpace k F}
    (hyX : polar (mForm Q₀) X y = 0) (hyY : polar (mForm Q₀) Y y = 0) :
    ((mRefl Q₀ X * mRefl Q₀ Y : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) y = y := by
  have hswy : (mRefl Q₀ Y : MSpace k F ≃ₗ[F] MSpace k F) y = y :=
    reflect_apply_of_polar_eq_zero hyY
  have hsvy : (mRefl Q₀ X : MSpace k F ≃ₗ[F] MSpace k F) y = y :=
    reflect_apply_of_polar_eq_zero hyX
  change (mRefl Q₀ X : MSpace k F ≃ₗ[F] MSpace k F)
    ((mRefl Q₀ Y : MSpace k F ≃ₗ[F] MSpace k F) y) = y
  rw [hswy, hsvy]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma pow_mul_fixes_of_fixes {g z : MGroup Q₀} {m : ℕ} (hz : z = g ^ m)
    {y : MSpace k F} (hy : (g : MSpace k F ≃ₗ[F] MSpace k F) y = y) :
    (z : MSpace k F ≃ₗ[F] MSpace k F) y = y := by
  subst hz
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ]
    change ((g ^ m : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F)
      (((g : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) y) = y
    rw [hy, ih]

omit [Fintype F] [DecidableEq F] in
private lemma eq_one_of_sq_eq_one_of_fixes_pair {X Y : MSpace k F}
    (hB : polar (mForm Q₀) X Y ≠ 0) {z : MGroup Q₀}
    (hzX : (z : MSpace k F ≃ₗ[F] MSpace k F) X = X)
    (hzY : (z : MSpace k F ≃ₗ[F] MSpace k F) Y = Y)
    (hzy : ∀ y : MSpace k F, polar (mForm Q₀) X y = 0 →
      polar (mForm Q₀) Y y = 0 → (z : MSpace k F ≃ₗ[F] MSpace k F) y = y) :
    z = 1 := by
  have hdecomp : ∀ W : MSpace k F, (z : MSpace k F ≃ₗ[F] MSpace k F) W = W := by
    intro W
    let c : F := polar (mForm Q₀) X Y
    let a : F := polar (mForm Q₀) W Y / c
    let b : F := polar (mForm Q₀) W X / c
    let p : MSpace k F := a • X + b • Y
    let y : MSpace k F := W - p
    have hc : c ≠ 0 := hB
    have hpX : polar (mForm Q₀) p X = polar (mForm Q₀) W X := by
      dsimp [p, a, b]
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_charTwo (mForm Q₀) X,
        polar_comm (mForm Q₀) Y X]
      change polar (mForm Q₀) W Y / c * 0 + polar (mForm Q₀) W X / c * c =
        polar (mForm Q₀) W X
      rw [mul_zero, zero_add, div_mul_cancel₀ _ hc]
    have hpY : polar (mForm Q₀) p Y = polar (mForm Q₀) W Y := by
      dsimp [p, a, b]
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_charTwo (mForm Q₀) Y]
      change polar (mForm Q₀) W Y / c * c + polar (mForm Q₀) W X / c * 0 =
        polar (mForm Q₀) W Y
      rw [mul_zero, add_zero, div_mul_cancel₀ _ hc]
    have hyX : polar (mForm Q₀) X y = 0 := by
      dsimp [y]
      rw [← polar_comm, polar_sub_left, hpX, sub_self]
    have hyY : polar (mForm Q₀) Y y = 0 := by
      dsimp [y]
      rw [← polar_comm, polar_sub_left, hpY, sub_self]
    have hzy' := hzy y hyX hyY
    have hzp : (z : MSpace k F ≃ₗ[F] MSpace k F) p = p := by
      dsimp [p]
      rw [map_add, map_smul, map_smul, hzX, hzY]
    have hpy : p + y = W := by dsimp [y]; abel
    rw [← hpy, map_add, hzp, hzy']
  apply Subtype.ext
  exact LinearEquiv.ext hdecomp

omit [DecidableEq F] in
private theorem mRefl_mul_odd_orderOf_of_polar_ne_zero
    (hQ : (polarBilin (mForm Q₀)).Nondegenerate) {X Y : MSpace k F}
    (hX : mForm Q₀ X = 1) (hY : mForm Q₀ Y = 1)
    (hB : polar (mForm Q₀) X Y ≠ 0) :
    Odd (orderOf (mRefl Q₀ X * mRefl Q₀ Y)) := by
  classical
  by_contra hodd
  have heven : Even (orderOf (mRefl Q₀ X * mRefl Q₀ Y)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp heven
  let g : MGroup Q₀ := mRefl Q₀ X * mRefl Q₀ Y
  let z : MGroup Q₀ := g ^ m
  have hgpos : 0 < orderOf g := orderOf_pos g
  have hm' : orderOf g = 2 * m := by simpa [g] using hm
  have hmpos : 0 < m := by omega
  have hz2 : z * z = 1 := by
    have h : z * z = g ^ (m + m) := by
      change (g ^ m) * (g ^ m) = g ^ (m + m)
      exact (pow_add g m m).symm
    rw [h, show m + m = 2 * m by ring, ← hm', pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have hdvd : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one (by
      change g ^ m = 1
      exact hz)
    rw [hm'] at hdvd
    have := Nat.le_of_dvd hmpos hdvd
    omega
  obtain ⟨hzsv, hzsw⟩ := conj_mul_self_inv_pow (sv := mRefl Q₀ X) (sw := mRefl Q₀ Y)
    (g := g) (z := z) m (mRefl_mul_self X) (mRefl_mul_self Y) rfl rfl hz2
  have hX0 : mForm Q₀ X ≠ 0 := by rw [hX]; exact one_ne_zero
  have hY0 : mForm Q₀ Y ≠ 0 := by rw [hY]; exact one_ne_zero
  have hczX : Commute z (mRefl Q₀ X) := mul_inv_eq_iff_eq_mul.mp hzsv
  have hczY : Commute z (mRefl Q₀ Y) := mul_inv_eq_iff_eq_mul.mp hzsw
  have hzX := (commute_reflect_iff_apply_eq hQ z hX0).mp hczX
  have hzY := (commute_reflect_iff_apply_eq hQ z hY0).mp hczY
  have hzy : ∀ y : MSpace k F, polar (mForm Q₀) X y = 0 →
      polar (mForm Q₀) Y y = 0 → (z : MSpace k F ≃ₗ[F] MSpace k F) y = y := by
    intro y hyX hyY
    have hgfix : (g : MSpace k F ≃ₗ[F] MSpace k F) y = y :=
      mRefl_mul_fixes_of_polar_eq_zero hyX hyY
    exact pow_mul_fixes_of_fixes rfl hgfix
  exact hz1 (eq_one_of_sq_eq_one_of_fixes_pair hB hzX hzY hzy)

include hQ₀ in
theorem isOddTransp_mClass : Asc72.IsOddTransp (mClass Q₀) := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  refine ⟨?_, ?_⟩
  · rintro d ⟨X, hX, rfl⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact mRefl_mul_self X
    · intro h1
      have hX0 : X ≠ 0 := fun h0 => by
        rw [h0, QuadraticMap.map_zero] at hX
        exact zero_ne_one hX
      obtain ⟨Y, hY⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ hX0
      have h2 : (mRefl Q₀ X : MSpace k F ≃ₗ[F] MSpace k F) Y = Y := by
        rw [h1]
        rfl
      rw [mRefl_apply_of_mForm_eq_one hX] at h2
      have h3 : polar (mForm Q₀) X Y • X = 0 :=
        add_left_cancel (show Y + polar (mForm Q₀) X Y • X = Y + 0 by simpa using h2)
      rcases smul_eq_zero.mp h3 with hc | hX0'
      · exact hY hc
      · exact hX0 hX0'
  · rintro d ⟨X, hX, rfl⟩ e ⟨Y, hY, rfl⟩
    by_cases hB : polar (mForm Q₀) X Y = 0
    · left
      have hcomm : mRefl Q₀ X * mRefl Q₀ Y = mRefl Q₀ Y * mRefl Q₀ X :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (mRefl_mem_centralizer_of_polar_eq_zero hB)
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      calc
        (mRefl Q₀ X * mRefl Q₀ Y) * (mRefl Q₀ X * mRefl Q₀ Y)
            = mRefl Q₀ X * (mRefl Q₀ Y * mRefl Q₀ X) * mRefl Q₀ Y := by group
        _ = mRefl Q₀ X * (mRefl Q₀ X * mRefl Q₀ Y) * mRefl Q₀ Y := by rw [← hcomm]
        _ = (mRefl Q₀ X * mRefl Q₀ X) * (mRefl Q₀ Y * mRefl Q₀ Y) := by group
        _ = 1 := by rw [mRefl_mul_self, mRefl_mul_self, one_mul]
    · right
      exact mRefl_mul_odd_orderOf_of_polar_ne_zero hQ hX hY hB

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem mForm_mU : mForm Q₀ mU = 1 := by
  rw [mForm_apply, mU]
  simp

omit [Fintype F] [DecidableEq F] in
lemma exists_mem_mGroup_apply_eq_of_map_eq
    (hQ : (polarBilin (mForm Q₀)).Nondegenerate) {X Y : MSpace k F}
    (hX : mForm Q₀ X = 1) (hY : mForm Q₀ Y = 1) :
    ∃ g : MGroup Q₀, (g : MSpace k F ≃ₗ[F] MSpace k F) X = Y := by
  have hX0 : X ≠ 0 := fun h0 => by
    rw [h0, QuadraticMap.map_zero] at hX
    exact zero_ne_one hX
  have hY0 : Y ≠ 0 := fun h0 => by
    rw [h0, QuadraticMap.map_zero] at hY
    exact zero_ne_one hY
  have hli : LinearIndependent F (fun _ : Fin 1 => X) :=
    linearIndependent_unique_iff.mpr hX0
  have hli' : LinearIndependent F (fun _ : Fin 1 => Y) :=
    linearIndependent_unique_iff.mpr hY0
  obtain ⟨g, hg, hgXY⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
      (Q := mForm Q₀) hQ (u := fun _ : Fin 1 => X) (u' := fun _ : Fin 1 => Y)
      hli hli' (fun _ => by rw [hY, hX]) (fun i j => by
        fin_cases i; fin_cases j; rw [polar_self_charTwo (mForm Q₀) Y,
          polar_self_charTwo (mForm Q₀) X])
  exact ⟨⟨g, hg⟩, hgXY 0⟩

include hQ₀ in
theorem setup_mClass (hk : 2 ≤ k) : Asc72.Setup (MGroup Q₀) (mClass Q₀) := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have hk2 : 2 ≤ k := hk
  have h6 : 6 ≤ Module.finrank F (MSpace k F) := by
    rw [finrank_mSpace]
    omega
  refine ⟨?_, isOddTransp_mClass (hQ₀ := hQ₀), ?_⟩
  · refine ⟨mRefl Q₀ mU, ?_⟩
    ext g
    constructor
    · rintro ⟨X, hX, rfl⟩
      obtain ⟨c, hc⟩ := exists_mem_mGroup_apply_eq_of_map_eq hQ (mForm_mU) hX
      refine isConj_iff.mpr ⟨c, ?_⟩
      apply Subtype.ext
      change (c : MSpace k F ≃ₗ[F] MSpace k F) *
          CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU *
          (c : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ =
        CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) X
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_conj c.2 mU, hc]
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg
      refine ⟨(c : MSpace k F ≃ₗ[F] MSpace k F) mU, ?_, ?_⟩
      · rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem c.2, mForm_mU]
      · rw [← hc]
        apply Subtype.ext
        exact CFSG.ClassicalGroups.Orthogonal.reflect_conj c.2 mU
  · have hs : CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) ''
        {v : MSpace k F | mForm Q₀ v = 1} ⊆
        ((TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀) :
          Subgroup (MSpace k F ≃ₗ[F] MSpace k F)) : Set (MSpace k F ≃ₗ[F] MSpace k F)) := by
      rintro _ ⟨v, hv, rfl⟩
      exact CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (mForm Q₀) v
    have hpre : ((↑) : MGroup Q₀ → MSpace k F ≃ₗ[F] MSpace k F) ⁻¹'
        (CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) ''
          {v : MSpace k F | mForm Q₀ v = 1}) = mClass Q₀ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, mClass]
      constructor
      · rintro ⟨v, hv, hgv⟩
        exact ⟨v, hv, Subtype.ext hgv.symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
    have hgen :=
      CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_eq_closure_reflect_of_finite hQ h6
    rw [← hpre,
      Subgroup.closure_coe_preimage_of_subset
        (K := TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀)) hs,
      ← hgen, Subgroup.comap_subtype, Subgroup.subgroupOf_self]

include hQ₀ in
omit [DecidableEq F] in
theorem center_mGroup_eq_bot (hk : 1 ≤ k) : Subgroup.center (MGroup Q₀) = ⊥ := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have hk1 : 1 ≤ k := hk
  have h4 : 4 ≤ Module.finrank F (MSpace k F) := by
    rw [finrank_mSpace]
    omega
  exact CFSG.ClassicalGroups.Orthogonal.center_orthogonalGroup_eq_bot
    (Q := mForm Q₀) hQ h4

include hQ₀ in
omit [Fintype F] [DecidableEq F] in
theorem mem_centralizer_mRefl_mU_iff (g : MGroup Q₀) :
    g ∈ Subgroup.centralizer {mRefl Q₀ mU} ↔
      (g : MSpace k F ≃ₗ[F] MSpace k F) mU = mU := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_reflect_iff_apply_eq hQ g (by rw [mForm_mU]; exact one_ne_zero)

private noncomputable def orthPlusCoreMulEquiv (n : ℕ) :
    ↥(CFSG.PGLModel.orthogonalPlus n F) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)) :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by
      have hcl : CFSG.MatrixModel.isometryCore (CFSG.PGLModel.plusQuadForm n (K := F)) =
          (TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)).comap
            (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F).toMonoidHom :=
        CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
          (Q := quadPlus n F) (Q₀ := CFSG.PGLModel.plusQuadForm n)
          ((CFSG.LieType.Universal.Spin.coe_quadPlus n F).trans rfl)
      change Subgroup.map
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F).toMonoidHom
          (CFSG.MatrixModel.isometryCore (CFSG.PGLModel.plusQuadForm n)) = _
      rw [hcl]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F).surjective _))

private noncomputable abbrev quadMinusFin (m : ℕ) (b c : F) :
    QuadraticForm F (Fin m ⊕ Fin m ⊕ Fin 2 → F) :=
  quadMinus (m + 1) F b c

private noncomputable def orthMinusCoreMulEquiv (m : ℕ) (b c : F) :
    ↥(CFSG.PGLModel.orthogonalMinus m F b c) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinusFin (F := F) m b c)) :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by
      have hcl : CFSG.MatrixModel.isometryCore (CFSG.PGLModel.minusQuadForm m b c) =
          (TauCeti.QuadraticMap.orthogonalGroup (quadMinusFin (F := F) m b c)).comap
            (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F).toMonoidHom :=
        CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
          (Q := quadMinusFin (F := F) m b c) (Q₀ := CFSG.PGLModel.minusQuadForm m b c)
          ((CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) F b c).trans rfl)
      change Subgroup.map
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F).toMonoidHom
          (CFSG.MatrixModel.isometryCore (CFSG.PGLModel.minusQuadForm m b c)) = _
      rw [hcl]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F).surjective _))

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma coe_orthPlusCoreMulEquiv (n : ℕ)
    (A : ↥(CFSG.PGLModel.orthogonalPlus n F)) :
    (orthPlusCoreMulEquiv (F := F) n A :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F
        (A : GL (Fin n ⊕ Fin n) F) := rfl

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma coe_orthMinusCoreMulEquiv (m : ℕ) (b c : F)
    (A : ↥(CFSG.PGLModel.orthogonalMinus m F b c)) :
    ((orthMinusCoreMulEquiv (F := F) m b c A).1 :
      (Fin m ⊕ Fin m ⊕ Fin 2 → F) ≃ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F)) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F
        (A : GL (Fin m ⊕ Fin m ⊕ Fin 2) F) := rfl

include hQ₀ in
omit [Fintype F] in
private lemma finrank_range_reflect_mU_sub_one :
    Module.finrank F (LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1)) = 1 := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have hmU : mForm Q₀ mU = 1 := mForm_mU
  have hmU0 : mU ≠ (0 : MSpace k F) := by simp [mU]
  have happ : ∀ Y : MSpace k F,
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1) Y =
        polar (mForm Q₀) mU Y • mU := by
    intro Y
    rw [LinearMap.sub_apply]
    change (mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F) Y - Y = _
    rw [mRefl_apply_of_mForm_eq_one hmU, add_sub_cancel_left]
  have hrange : LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1) = Submodule.span F {mU} := by
    ext Y
    constructor
    · rintro ⟨W, rfl⟩
      rw [happ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · intro hY
      rw [Submodule.mem_span_singleton] at hY
      obtain ⟨d, rfl⟩ := hY
      by_cases hd : d = 0
      · refine ⟨0, ?_⟩
        rw [happ, hd, zero_smul]
        simp
      · obtain ⟨Z, hZ⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ hmU0
        refine ⟨(d / polar (mForm Q₀) mU Z) • Z, ?_⟩
        rw [happ, CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
          div_mul_cancel₀ _ hZ]
  rw [hrange, finrank_span_singleton hmU0]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma matrix_rank_sub_one_eq_finrank_range_toLinEquiv
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : GL ι F) :
    Matrix.rank ((A : Matrix ι ι F) - 1) =
      Module.finrank F (LinearMap.range
        (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι F) A :
          (ι → F) ≃ₗ[F] (ι → F)) - 1 : (ι → F) →ₗ[F] (ι → F))) := by
  rw [Matrix.rank_eq_finrank_range_toLin ((A : Matrix ι ι F) - 1)
    (Pi.basisFun F ι) (Pi.basisFun F ι), Matrix.toLin_eq_toLin']
  have hlin : Matrix.toLin' ((A : Matrix ι ι F) - 1) =
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι F A :
        (ι → F) ≃ₗ[F] (ι → F)) - 1 : (ι → F) →ₗ[F] (ι → F)) := by
    ext x
    simp [Matrix.toLin'_apply', CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  rw [hlin]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma isPlusType_binForm_one_zero :
    CFSG.GroupTheory.WeirSylow.IsPlusType (CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0) := by
  refine ⟨Submodule.span F {(0, 1)}, ?_, ?_⟩
  · rw [finrank_span_singleton (by simp), Module.finrank_prod, Module.finrank_self]
  · rintro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    rw [CFSG.GroupTheory.WeirSylow.binForm_apply]
    simp

private noncomputable def binFormOneZeroIsometry :
    (CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0).IsometryEquiv (quadPlus 1 F) :=
  Classical.choice (CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
    (Q := CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0)
    (CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal.nondegenerate_polarBilin_binForm
      (b := 1) (c := 0) (by norm_num))
    (by rw [Module.finrank_prod, Module.finrank_self])
    isPlusType_binForm_one_zero)

private noncomputable def mFormProdPlusIsometry :
    (mForm Q₀).IsometryEquiv (Q₀.prod (quadPlus 1 F)) :=
  (QuadraticMap.IsometryEquiv.prodComm
      (CFSG.GroupTheory.WeirSylow.binForm (1 : F) 0) Q₀).trans
    ((QuadraticMap.IsometryEquiv.refl Q₀).prod binFormOneZeroIsometry)

include hQ₀ in
omit [DecidableEq F] [CharP F 2] in
private lemma isPlusType_mForm_iff (hk : 1 ≤ k) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (mForm Q₀) ↔
      CFSG.GroupTheory.WeirSylow.IsPlusType Q₀ := by
  have hQ0nd : (polarBilin Q₀).Nondegenerate := by
    rw [show polarBilin Q₀ = spForm k F from LinearMap.ext₂ hQ₀]
    exact spForm_nondegenerate
  have hdimQ : Module.finrank F (Fin k ⊕ Fin k → F) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  constructor
  · intro h
    by_contra hnot
    have h' : CFSG.GroupTheory.WeirSylow.IsPlusType (Q₀.prod (quadPlus 1 F)) :=
      (CFSG.GroupTheory.WeirSylow.isPlusType_congr mFormProdPlusIsometry).1 h
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_prod_quadPlus hQ0nd hk hdimQ hnot 1 h'
  · intro h
    exact (CFSG.GroupTheory.WeirSylow.isPlusType_congr mFormProdPlusIsometry).2
      (CFSG.GroupTheory.WeirSylow.IsPlusType.prod h
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F 1))

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma isRankOneIn_orthPlusCoreMulEquiv_orthogonalGroupCongr {n : ℕ}
    (e0 : (mForm Q₀).IsometryEquiv (quadPlus n F))
    (hrange : Module.finrank F (LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1)) = 1) :
    CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
      (((orthPlusCoreMulEquiv (F := F) n).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
        GL (Fin n ⊕ Fin n) F)) := by
  rw [CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn]
  rw [matrix_rank_sub_one_eq_finrank_range_toLinEquiv (ι := Fin n ⊕ Fin n)
    ((orthPlusCoreMulEquiv (F := F) n).symm
      ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
      GL (Fin n ⊕ Fin n) F)]
  have htoLin : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F
      (((orthPlusCoreMulEquiv (F := F) n).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
        ↥(CFSG.PGLModel.orthogonalPlus n F)) : GL _ F) :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) =
      ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) := by
    have h := coe_orthPlusCoreMulEquiv (F := F) n
      ((orthPlusCoreMulEquiv (F := F) n).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)))
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hfr : Module.finrank F (LinearMap.range
      ((((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) :
        (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) - 1)) = 1 := by
    have hf : ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) =
        (e0.toLinearEquiv.symm.trans
          ((mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F))).trans e0.toLinearEquiv := by
      refine LinearEquiv.ext fun x => ?_
      funext y
      exact congrFun (TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e0
        (mRefl Q₀ mU) x) y
    rw [hf, CFSG.HardMathSupport.GuralnickMalle.finrank_range_sub_one_eq_of_intertwines
      (e := e0.toLinearEquiv) (f := (↑(mRefl Q₀ mU) : MSpace k F →ₗ[F] MSpace k F))
      (g := ((e0.toLinearEquiv.symm.trans
        (mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F)).trans e0.toLinearEquiv).toLinearMap)
      (fun x => by simp [LinearEquiv.trans_apply])]
    exact hrange
  rw [htoLin, hfr]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma isRankOneIn_orthMinusCoreMulEquiv_orthogonalGroupCongr {m : ℕ} {b c : F}
    (e0 : (mForm Q₀).IsometryEquiv (quadMinusFin (F := F) m b c))
    (hrange : Module.finrank F (LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1)) = 1) :
    CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
      (((orthMinusCoreMulEquiv (F := F) m b c).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) F)) := by
  rw [CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn]
  rw [matrix_rank_sub_one_eq_finrank_range_toLinEquiv (ι := Fin m ⊕ Fin m ⊕ Fin 2)
    ((orthMinusCoreMulEquiv (F := F) m b c).symm
      ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
      GL (Fin m ⊕ Fin m ⊕ Fin 2) F)]
  have htoLin : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) F
      (((orthMinusCoreMulEquiv (F := F) m b c).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) :
        ↥(CFSG.PGLModel.orthogonalMinus m F b c)) : GL _ F) :
      (Fin m ⊕ Fin m ⊕ Fin 2 → F) ≃ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F)) =
      (((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinusFin (F := F) m b c))).1 :
        (Fin m ⊕ Fin m ⊕ Fin 2 → F) ≃ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F)) := by
    have h := coe_orthMinusCoreMulEquiv (F := F) m b c
      ((orthMinusCoreMulEquiv (F := F) m b c).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)))
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hfr : Module.finrank F (LinearMap.range
      (((((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinusFin (F := F) m b c))).1 :
        (Fin m ⊕ Fin m ⊕ Fin 2 → F) →ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F))) - 1)) = 1 := by
    have hf : ((((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU) :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinusFin (F := F) m b c))).1 :
        (Fin m ⊕ Fin m ⊕ Fin 2 → F) →ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F))) =
        (((e0.toLinearEquiv.symm.trans
          ((mRefl Q₀ mU : MSpace k F ≃ₗ[F] MSpace k F))).trans e0.toLinearEquiv :
          (Fin m ⊕ Fin m ⊕ Fin 2 → F) ≃ₗ[F]
            (Fin m ⊕ Fin m ⊕ Fin 2 → F)) :
          (Fin m ⊕ Fin m ⊕ Fin 2 → F) →ₗ[F] (Fin m ⊕ Fin m ⊕ Fin 2 → F)) := by
      refine LinearMap.ext fun x => ?_
      funext y
      exact congrFun (TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e0
        (mRefl Q₀ mU) x) y
    rw [hf, CFSG.HardMathSupport.GuralnickMalle.finrank_range_sub_one_eq_of_intertwines
      (e := e0.toLinearEquiv) (f := (↑(mRefl Q₀ mU) : MSpace k F →ₗ[F] MSpace k F))
      (g := ((e0.toLinearEquiv.symm.trans (mRefl Q₀ mU).1).trans e0.toLinearEquiv).toLinearMap)
      (fun x => by simp [LinearEquiv.trans_apply])]
    exact hrange
  rw [htoLin, hfr]

include hQ₀ in
private lemma exists_isRankOneIn_orthogonalPlus_of_isPlusType (hk : 1 ≤ k)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q₀) :
    ∃ e : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃*
        ↥(CFSG.PGLModel.orthogonalPlus (k + 1) F),
      CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
        ((e (QuotientGroup.mk (mRefl Q₀ mU)) : GL (Fin (k + 1) ⊕ Fin (k + 1)) F)) := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have hdimM : Module.finrank F (MSpace k F) = 2 * (k + 1) := finrank_mSpace
  have hcenter : Subgroup.center (MGroup Q₀) = ⊥ := center_mGroup_eq_bot (hQ₀ := hQ₀) hk
  let eQuot : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃* MGroup Q₀ :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have heQuot : ∀ x : MGroup Q₀, eQuot (QuotientGroup.mk x) = x := by
    intro x
    simp only [eQuot]
    rfl
  have hrange : Module.finrank F (LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1)) = 1 :=
    finrank_range_reflect_mU_sub_one (hQ₀ := hQ₀)
  have hplusM : CFSG.GroupTheory.WeirSylow.IsPlusType (mForm Q₀) :=
    (isPlusType_mForm_iff (hQ₀ := hQ₀) hk).2 hplus
  obtain ⟨e0⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
    (Q := mForm Q₀) hQ (n := k + 1) hdimM hplusM
  let eGroup : MGroup Q₀ ≃* ↥(CFSG.PGLModel.orthogonalPlus (k + 1) F) :=
    (TauCeti.QuadraticMap.orthogonalGroupCongr e0).trans
      (orthPlusCoreMulEquiv (F := F) (k + 1)).symm
  let e : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃*
      ↥(CFSG.PGLModel.orthogonalPlus (k + 1) F) := eQuot.trans eGroup
  refine ⟨e, ?_⟩
  have hA : (e (QuotientGroup.mk (mRefl Q₀ mU)) :
      ↥(CFSG.PGLModel.orthogonalPlus (k + 1) F)) =
      (orthPlusCoreMulEquiv (F := F) (k + 1)).symm
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e0) (mRefl Q₀ mU)) := by
    simp [e, eGroup, heQuot]
  change CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
    ((e (QuotientGroup.mk (mRefl Q₀ mU)) : GL (Fin (k + 1) ⊕ Fin (k + 1)) F))
  rw [hA]
  exact isRankOneIn_orthPlusCoreMulEquiv_orthogonalGroupCongr e0 hrange

include hQ₀ in
private lemma exists_isRankOneIn_orthogonalMinus_of_not_isPlusType (hk : 1 ≤ k)
    (hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q₀) :
    ∃ (b c : F) (_ : ∀ t : F, t ^ 2 + b * t + c ≠ 0)
      (e : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃*
        ↥(CFSG.PGLModel.orthogonalMinus k F b c)),
      CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
        ((e (QuotientGroup.mk (mRefl Q₀ mU)) : GL (Fin k ⊕ Fin k ⊕ Fin 2) F)) := by
  have hQ : (polarBilin (mForm Q₀)).Nondegenerate :=
    nondegenerate_polarBilin_mForm (hQ₀ := hQ₀)
  have hdimM : Module.finrank F (MSpace k F) = 2 * (k + 1) := finrank_mSpace
  have hcenter : Subgroup.center (MGroup Q₀) = ⊥ := center_mGroup_eq_bot (hQ₀ := hQ₀) hk
  let eQuot : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃* MGroup Q₀ :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have heQuot : ∀ x : MGroup Q₀, eQuot (QuotientGroup.mk x) = x := by
    intro x
    simp only [eQuot]
    rfl
  have hrange : Module.finrank F (LinearMap.range
      ((CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU :
        MSpace k F →ₗ[F] MSpace k F) - 1)) = 1 :=
    finrank_range_reflect_mU_sub_one (hQ₀ := hQ₀)
  have hnotplusM : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (mForm Q₀) :=
    fun h => hnotplus ((isPlusType_mForm_iff (hQ₀ := hQ₀) hk).1 h)
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
    (Q := mForm Q₀) hQ (n := k + 1) (by omega) hdimM with hplus' | ⟨b, c, hirr, he0⟩
  · obtain ⟨eplus⟩ := hplus'
    exact absurd ((CFSG.GroupTheory.WeirSylow.isPlusType_congr eplus).2
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F (k + 1))) hnotplusM
  · obtain ⟨e0⟩ := he0
    let e0' : (mForm Q₀).IsometryEquiv (quadMinusFin (F := F) k b c) := e0
    let eGroup : MGroup Q₀ ≃* ↥(CFSG.PGLModel.orthogonalMinus k F b c) :=
      (TauCeti.QuadraticMap.orthogonalGroupCongr e0').trans
        (orthMinusCoreMulEquiv (F := F) k b c).symm
    let e : (MGroup Q₀ ⧸ Subgroup.center (MGroup Q₀)) ≃*
        ↥(CFSG.PGLModel.orthogonalMinus k F b c) := eQuot.trans eGroup
    refine ⟨b, c, hirr, e, ?_⟩
    have hA : (e (QuotientGroup.mk (mRefl Q₀ mU)) :
        ↥(CFSG.PGLModel.orthogonalMinus k F b c)) =
        (orthMinusCoreMulEquiv (F := F) k b c).symm
          ((TauCeti.QuadraticMap.orthogonalGroupCongr e0') (mRefl Q₀ mU)) := by
      simp [e, eGroup, heQuot]
    change CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
      ((e (QuotientGroup.mk (mRefl Q₀ mU)) : GL (Fin k ⊕ Fin k ⊕ Fin 2) F))
    rw [hA]
    exact isRankOneIn_orthMinusCoreMulEquiv_orthogonalGroupCongr e0' hrange

include hQ₀ in
theorem isOrthReflection_mGroup (hk : 1 ≤ k) {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection (MGroup Q₀) (2 * k + 2) f
      (mRefl Q₀ mU) := by
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q₀
  · obtain ⟨e, he⟩ :=
      exists_isRankOneIn_orthogonalPlus_of_isPlusType (hQ₀ := hQ₀) hk hplus
    exact Or.inl ⟨k + 1, by omega, by ring, F, inferInstance, Finite.of_fintype F, hF, e, he⟩
  · obtain ⟨b, c, hirr, e, he⟩ :=
      exists_isRankOneIn_orthogonalMinus_of_not_isPlusType (hQ₀ := hQ₀) hk hplus
    exact Or.inr ⟨k, hk, rfl, F, inferInstance, Finite.of_fintype F, hF, b, c, hirr, e, he⟩

end CFSG.OddTranspositions.PartThree.ElevenSp

end
