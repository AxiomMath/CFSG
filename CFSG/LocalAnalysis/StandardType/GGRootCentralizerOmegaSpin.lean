module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaFrame
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LieType.Steinberg.Classical.SpinOdd.Weyl
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed

public section

namespace CFSG.StandardType

namespace RootCentOmega

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

theorem spinAction_longRoot_eq_eichler {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N) {i j : Fin N} (hij : i ≠ j) (s t : Bool)
    (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) = eichler Q (F.vec j t) (c • F.vec i s) := by
  have hw : polar Q (F.vec j t) (c • F.vec i s) = 0 := by
    rw [polar_smul_right_eq, F.polar_vec_of_ne hij.symm, mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [F.spinAction_longRoot, eichler_apply (F.map_vec j t) hw, QuadraticMap.map_smul, F.map_vec,
    smul_zero, zero_mul, add_zero, polar_smul_right_eq, smul_smul,
    mul_comm (polar Q v (F.vec j t)) c]

theorem centralizer_le_ggOTwoPrime_of_injective {U G : Type*} [Group U] [Group G] (φ : U →* G)
    (hφ : Function.Injective φ) {x : U}
    (h : centralizer {φ x} ⊓ φ.range ≤ ggOTwoPrime (centralizer {φ x} ⊓ φ.range)) :
    centralizer {x} ≤ ggOTwoPrime (centralizer {x}) := by
  have hle : ggOTwoPrime (centralizer {φ x} ⊓ φ.range) ≤
      (ggOTwoPrime (centralizer ({x} : Set U))).map φ := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro g ⟨hg, k, hk⟩
    obtain ⟨hgC, y, rfl⟩ := Subgroup.mem_inf.mp hg
    refine ⟨y, Subgroup.subset_closure ⟨?_, k, hφ (by rw [map_pow, hk, map_one])⟩, rfl⟩
    rw [mem_centralizer_singleton_iff] at hgC ⊢
    exact hφ (by rw [map_mul, map_mul, hgC])
  intro y hy
  have hφy : φ y ∈ centralizer {φ x} ⊓ φ.range := by
    refine Subgroup.mem_inf.mpr ⟨?_, y, rfl⟩
    rw [mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, hy, map_mul]
  obtain ⟨y', hy', hyy'⟩ := hle (h hφy)
  rwa [hφ hyy'] at hy'

section Plus

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem center_spinGroup_quadPlus_eq_bot_charTwo (hn : 3 ≤ n) :
    center (spinGroup (quadPlus n K)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn
    CharTwo.two_eq_zero

omit [Finite K] in
theorem spinAction_quadPlus_injective : Function.Injective (spinAction (quadPlus n K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix, ker_spinMatrix_quadPlus_eq_bot
    CharTwo.two_eq_zero]

omit [Finite K] in
theorem elementaryGroup_quadPlus_le_omegaGroup (hn : 3 ≤ n) :
    elementaryGroup (quadPlus n K) ≤
      omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K) := by
  rw [← commutator_orthogonalGroup_quadPlus hn]
  exact CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup _

omit [Finite K] [CharP K 2] in
theorem eq_zero_of_polar_plusVec {x : Fin n ⊕ Fin n → K}
    (hx : ∀ k u, polar (quadPlus n K) (plusVec n K k u) x = 0) : x = 0 := by
  funext a
  rcases a with k | k
  · have h := hx k false
    rwa [plusVec_false, polar_single_inr_quadPlus] at h
  · have h := hx k true
    rwa [plusVec_true, polar_single_inl_quadPlus] at h

theorem centralizer_longRoot_plus_le (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    {c : K} (hc : c ≠ 0) :
    centralizer {(plusFrame n K (by omega)).longRoot hij s t (.ofAdd c)} ≤
      ggOTwoPrime (centralizer {(plusFrame n K (by omega)).longRoot hij s t (.ofAdd c)}) := by
  apply centralizer_le_ggOTwoPrime_of_injective _ spinAction_quadPlus_injective
  rw [spinAction_longRoot_eq_eichler, range_spinAction_quadPlus (by omega)]
  exact centralizer_frame_le_ggOTwoPrime (nondegenerate_polarBilin_quadPlus n K)
    (elementaryGroup_quadPlus_le_omegaGroup (by omega)) (by omega) (plusFrame n K (by omega))
    (fun x hx _ => eq_zero_of_polar_plusVec hx)
    (fun x _ hx _ hx0 _ => absurd (eq_zero_of_polar_plusVec hx) hx0) (Or.inl hn) hij s t hc

end Plus

section Minus

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem spinAction_quadMinus_injective : Function.Injective (spinAction (quadMinus n K b c)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix,
    ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero]

include hirr in
theorem elementaryGroup_quadMinus_le_omegaGroup (hn : 4 ≤ n) :
    elementaryGroup (quadMinus n K b c) ≤
      omegaGroup (quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) := by
  rw [← commutator_orthogonalGroup_quadMinus hn hirr]
  exact CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup _

omit [Finite K] [CharP K 2] in
theorem mem_tailSpace_of_polar_minusVec (hn0 : 0 < n - 1) {x : Vm n K}
    (hx : ∀ k u, polar (quadMinus n K b c) (minusVec n k u) x = 0) :
    x ∈ tailSpace (minusFamily K b c hn0) (n - 1) := by
  rw [mem_tailSpace]
  intro m hm
  rw [minusFamily_of_lt hn0 hm]
  exact ⟨hx ⟨m, hm⟩ true, hx ⟨m, hm⟩ false⟩

include hirr in
theorem centralizer_longRoot_minus_le (hn : 4 ≤ n) {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) {a : K} (ha : a ≠ 0) :
    centralizer {(minusFrame n b c).longRoot hij s t (.ofAdd a)} ≤
      ggOTwoPrime (centralizer {(minusFrame n b c).longRoot hij s t (.ofAdd a)}) := by
  have hn0 : 0 < n - 1 := by omega
  have hz0 : (minusFrame n b c).z ≠ 0 := fun h => by
    have h1 := (minusFrame n b c).map_z
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  apply centralizer_le_ggOTwoPrime_of_injective _ (spinAction_quadMinus_injective hirr)
  rw [spinAction_longRoot_eq_eichler, range_spinAction_quadMinus hn hirr]
  exact centralizer_frame_le_ggOTwoPrime (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (elementaryGroup_quadMinus_le_omegaGroup hirr hn) (by omega) (minusFrame n b c).toHypFrame
    (fun x hx hQx => eq_zero_of_mem_tailSpace_minusFamily hirr hn0
      (mem_tailSpace_of_polar_minusVec hn0 hx) hQx)
    (fun x y hx hy hx0 hxy => exists_eq_smul_of_mem_tailSpace_minusFamily CharTwo.two_eq_zero
      hirr hn0 (mem_tailSpace_of_polar_minusVec hn0 hx) hx0
      (mem_tailSpace_of_polar_minusVec hn0 hy) hxy)
    (Or.inr ⟨(minusFrame n b c).z, hz0, fun k u => (minusFrame n b c).polar_vec_z k u⟩)
    hij s t ha

end Minus

theorem exists_long_weylAction {m : ℕ} (w : (coxeterMatrix (isFiniteType_cartanB m)).Group)
    {γ : Fin m → ℤ}
    (h : ∃ (i j : Fin m) (_ : i ≠ j) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ∃ (i j : Fin m) (_ : i ≠ j) (s t : Bool),
      toStdB m (weylAction (isFiniteType_cartanB m) w γ) =
        Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  induction w using
    (coxeterMatrix (isFiniteType_cartanB m)).toCoxeterSystem.simple_induction_left with
  | one => simpa using h
  | mul_simple_left w l ih =>
    obtain ⟨i, j, hij, s, t, hst⟩ := ih
    rw [weylAction_mul_apply, weylAction_simple]
    by_cases hl : l.val + 1 < m
    · exact ⟨_, _, (Equiv.swap _ _).injective.ne hij, s, t,
        CFSG.LieType.Steinberg.SpinOdd.toStdB_reflection_long_of_lt hl hst⟩
    · exact ⟨i, j, hij, _, _,
        CFSG.LieType.Steinberg.SpinOdd.toStdB_reflection_long_of_not_lt hl hst⟩

section MinusLong

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem exists_long_of_ggLongRoot_minus (hn : 4 ≤ n) {γ : Fin (minusDatum n hirr).rank → ℤ}
    (hγ : GGLongRoot (minusDatum n hirr) γ) :
    ∃ (i j : Fin (n - 1)) (_ : i ≠ j) (s t : Bool),
      toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ
  refine exists_long_weylAction w ?_
  rcases exists_toStdB_eq_of_mem_roots n hγ₀ with h | ⟨k, s, hk⟩
  · exact h
  · exfalso
    set e : Fin (n - 1) → ℤ := Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 with he
    have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hδ := ofStdB_mem_rootsB (n - 1) (e := e)
      (Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1, h01, Or.inl rfl, Or.inl rfl, rfl⟩)
    have h1 : @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ (ofStdB (n - 1) e) ≤
        @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ γ₀ := hmax _ hδ
    rw [ht_of_toStdB_eq_add (n - 1) (toStdB_ofStdB (n - 1) e),
      ht_of_toStdB_eq_single (n - 1) hk] at h1
    have hk' := k.isLt
    cases s <;> simp [boolSign] at h1 <;> omega

end MinusLong

end RootCentOmega

end CFSG.StandardType
