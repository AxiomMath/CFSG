module

public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.TypeAReflOver

open Module Polynomial.Chebyshev

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem reflection_mul_self_of_apply {x : V} {f : Module.Dual K V} (hf : f x = 2) :
    reflection hf * reflection hf = 1 := by
  ext z
  rw [LinearEquiv.mul_apply]
  simpa using Module.involutive_reflection hf z

theorem rankOne_pow_three_apply {T : V ≃ₗ[K] V} {w : V} {φ : Module.Dual K V}
    (hφw : φ w = 0) (hT : ∀ z, T z = z + φ z • w) (z : V) :
    (T ^ 3) z = z + (3 : K) • (φ z • w) := by
  have h2 : T (T z) = z + (2 : K) • (φ z • w) := by
    rw [hT, hT]
    simp only [map_add, map_smul, hφw, smul_zero, mul_zero, add_zero, smul_add, smul_smul]
    rw [← smul_smul, two_smul]
    abel
  have h3 : T (T (T z)) = z + (3 : K) • (φ z • w) := by
    rw [h2, hT]
    simp only [map_add, map_smul, hφw, smul_zero, mul_zero, add_zero, smul_add, smul_smul]
    rw [show (3 : K) * φ z = 2 * φ z + φ z by ring, add_smul]
    abel
  rw [show (T ^ 3) z = T (T (T z)) by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]]
  exact h3

theorem rankOne_pow_two_apply {T : V ≃ₗ[K] V} {w : V} {φ : Module.Dual K V}
    (hφw : φ w = 0) (hT : ∀ z, T z = z + φ z • w) (z : V) :
    (T ^ 2) z = z + (2 : K) • (φ z • w) := by
  rw [show (T ^ 2) z = T (T z) by
    rw [pow_two, LinearEquiv.mul_apply]]
  rw [hT, hT]
  simp only [map_add, map_smul, hφw, smul_zero, mul_zero, add_zero, smul_add, smul_smul]
  rw [← smul_smul, two_smul]
  abel

private lemma ggCoxA_three (t : K) : ggCoxA K ((3 : ℕ) : ℤ) t = t + 1 := by
  have h : ((3 : ℕ) : ℤ) = 2 * 1 + 1 := by norm_num
  rw [h, ggCoxA_two_mul_add_one]
  simp [S_zero, S_one]

private lemma ggCoxB_three (t : K) : ggCoxB K ((3 : ℕ) : ℤ) t = t * (t + 1) := by
  have h : ((3 : ℕ) : ℤ) = 2 * 1 + 1 := by norm_num
  rw [h, ggCoxB_two_mul_add_one]
  simp [S_zero, S_one]

private lemma ggCoxA_two (t : K) : ggCoxA K ((2 : ℕ) : ℤ) t = 1 := by
  have h : ((2 : ℕ) : ℤ) = 2 * 1 := by norm_num
  rw [h, ggCoxA_two_mul]
  simp [S_zero, S_one, S_neg_one]

private lemma ggCoxB_two (t : K) : ggCoxB K ((2 : ℕ) : ℤ) t = t + 1 := by
  have h : ((2 : ℕ) : ℤ) = 2 * 1 := by norm_num
  rw [h, ggCoxB_two_mul]
  simp [S_zero, S_one]

private lemma ne_zero_of_two {x : V} {f : Module.Dual K V} (h2 : (2 : K) ≠ 0)
    (hf : f x = 2) : x ≠ 0 ∧ f ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, map_zero] at hf
    exact h2 hf.symm
  · rw [h, LinearMap.zero_apply] at hf
    exact h2 hf.symm

theorem reflection_mul_reflection_pow_three_cross (h2 : (2 : K) ≠ 0)
    {x y : V} {f g : Module.Dual K V} (hf : f x = 2) (hg : g y = 2)
    (h3 : (reflection hf * reflection hg) ^ 3 = 1)
    (hne : reflection hf ≠ reflection hg) : f y * g x = 1 := by
  obtain ⟨hx0, hf0⟩ := ne_zero_of_two h2 hf
  by_cases hxy : LinearIndependent K ![x, y]
  · by_cases hfg : LinearIndependent K ![f, g]
    ·
      have hcrit := (reflection_mul_reflection_pow_eq_one_iff hf hg hxy hfg 3).mp h3
      have hsum := hcrit.1
      simp only [ggCoxA_three, ggCoxB_three] at hsum
      have hsq : (f y * g x - 2 + 1) * (f y * g x - 2 + 1) = 0 := by
        linear_combination hsum
      have ht : f y * g x - 2 + 1 = 0 := mul_self_eq_zero.mp hsq
      linear_combination ht
    ·
      obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent hf0 hfg
      set w : V := x - c • y with hwdef
      have hw : w ≠ 0 := by
        intro hw0
        have hrel : (1 : K) • x + (-c) • y = 0 := by
          have h' : x - c • y = 0 := by rw [← hwdef, hw0]
          rw [sub_eq_add_neg, ← neg_smul] at h'
          simpa using h'
        obtain ⟨h1, -⟩ := LinearIndependent.pair_iff.mp hxy 1 (-c) hrel
        exact one_ne_zero h1
      have hfw : f w = 0 := apply_sub_smul_of_eq_smul_dual hf hg hc
      have hT : ∀ z, (reflection hf * reflection hg) z = z + f z • w :=
        fun z => reflection_mul_reflection_apply_of_eq_smul_dual hf hg hc z
      obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
        by_contra h
        push Not at h
        exact hf0 (LinearMap.ext h)
      have h3z : z + (3 : K) • (f z • w) = z := by
        have := congrArg (fun T : V ≃ₗ[K] V => T z) h3
        rw [rankOne_pow_three_apply hfw hT z] at this
        simpa using this
      have h3N : (3 : K) • (f z • w) = 0 := by
        have h' : z + (3 : K) • (f z • w) = z + 0 := by simpa using h3z
        exact add_left_cancel h'
      have hcoef : (3 : K) * f z = 0 := by
        rw [smul_smul] at h3N
        exact (smul_eq_zero.mp h3N).resolve_right hw
      have h3zero : (3 : K) = 0 := (mul_eq_zero.mp hcoef).resolve_right hz
      have hcx : g x = c * (2 : K) := by
        rw [hc]
        simp [smul_eq_mul, hf]
      have hcy : c * f y = 2 := by
        have := hg
        rw [hc] at this
        simpa [smul_eq_mul] using this
      have huv : f y * g x = 4 := by
        rw [hcx]
        calc f y * (c * 2) = (c * f y) * 2 := by ring
          _ = 2 * 2 := by rw [hcy]
          _ = 4 := by norm_num
      have h4 : (4 : K) = 1 := by
        have : (4 : K) = 3 + 1 := by norm_num
        rw [this, h3zero, zero_add]
      rwa [huv, h4]
  ·
    obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent hx0 hxy
    set φ : Module.Dual K V := c • g - f with hφdef
    have hφapply : ∀ z, φ z = c * g z - f z := by
      intro z
      simp [hφdef, smul_eq_mul]
    have hφx : φ x = 0 := by
      rw [hφapply]
      exact sub_apply_self_of_eq_smul hf hg hc
    have hT : ∀ z, (reflection hf * reflection hg) z = z + φ z • x := by
      intro z
      rw [reflection_mul_reflection_apply_of_eq_smul hf hg hc, hφapply]
    by_cases hφ0 : φ = 0
    · exfalso
      apply hne
      have hfg : f = c • g := by
        have : c • g - f = 0 := hφ0
        exact (sub_eq_zero.mp this).symm
      ext z
      rw [reflection_apply, reflection_apply, hc]
      simp only [hfg, LinearMap.smul_apply, smul_eq_mul, smul_smul]
      rw [mul_comm]
    · obtain ⟨z, hz⟩ : ∃ z, φ z ≠ 0 := by
        by_contra h
        push Not at h
        exact hφ0 (LinearMap.ext h)
      have h3z : z + (3 : K) • (φ z • x) = z := by
        have := congrArg (fun T : V ≃ₗ[K] V => T z) h3
        rw [rankOne_pow_three_apply hφx hT z] at this
        simpa using this
      have h3N : (3 : K) • (φ z • x) = 0 := by
        have h' : z + (3 : K) • (φ z • x) = z + 0 := by simpa using h3z
        exact add_left_cancel h'
      have hcoef : (3 : K) * φ z = 0 := by
        rw [smul_smul] at h3N
        exact (smul_eq_zero.mp h3N).resolve_right hx0
      have h3zero : (3 : K) = 0 := (mul_eq_zero.mp hcoef).resolve_right hz
      have hfy : f y = c * (2 : K) := by
        rw [hc]
        simp [smul_eq_mul, hf]
      have hgy : c * g x = 2 := by
        have := hg
        rw [hc] at this
        simpa [smul_eq_mul] using this
      have huv : f y * g x = 4 := by
        rw [hfy]
        calc c * 2 * g x = 2 * (c * g x) := by ring
          _ = 2 * 2 := by rw [hgy]
          _ = 4 := by norm_num
      have h4 : (4 : K) = 1 := by
        have : (4 : K) = 3 + 1 := by norm_num
        rw [this, h3zero, zero_add]
      rwa [huv, h4]

theorem reflection_mul_reflection_pow_two_cross (h2 : (2 : K) ≠ 0)
    {x y : V} {f g : Module.Dual K V} (hf : f x = 2) (hg : g y = 2)
    (hsq : (reflection hf * reflection hg) ^ 2 = 1)
    (hne : reflection hf ≠ reflection hg) : f y = 0 ∧ g x = 0 := by
  haveI : NeZero (2 : K) := ⟨h2⟩
  rcases linearIndependent_and_or_exists_transvection hf hg with
    ⟨hxy, hfg⟩ | ⟨w, φ, hφw, hT⟩
  · have hcrit := (reflection_mul_reflection_pow_eq_one_iff hf hg hxy hfg 2).mp hsq
    have hA := hcrit.1
    have hB := hcrit.2.1
    have hC := hcrit.2.2
    simp only [ggCoxA_two, ggCoxB_two] at hA hB
    simp only [ggCoxA_two, mul_one] at hC
    have hB' : f y * (f y * g x - 2 + 1) = 0 := hB
    have hsub : f y * g x - 2 + 1 = -(1 : K) := by rw [hC]; ring
    rw [hsub] at hB'
    have hu : f y = 0 := by
      have : -(f y) = 0 := by simpa using hB'
      exact neg_eq_zero.mp this
    exact ⟨hu, hC⟩
  · exfalso
    apply hne
    have hsqz : ∀ z, (reflection hf * reflection hg) z = z := by
      intro z
      have h := congrArg (fun T : V ≃ₗ[K] V => T z) hsq
      rw [rankOne_pow_two_apply hφw hT z] at h
      have h2N : (2 : K) • (φ z • w) = 0 := by
        have h' : z + (2 : K) • (φ z • w) = z + 0 := by simpa using h
        exact add_left_cancel h'
      have hhalf : φ z • w = 0 := by
        have := smul_eq_zero.mp h2N
        exact this.resolve_left h2
      rw [hT]
      rw [hhalf, add_zero]
    have hprod : reflection hf * reflection hg = 1 := by
      ext z
      rw [hsqz z]
      rfl
    have hr2 : reflection hf * reflection hf = 1 := reflection_mul_self_of_apply hf
    calc reflection hf = reflection hf * 1 := (mul_one _).symm
      _ = reflection hf * (reflection hf * reflection hg) := by rw [hprod]
      _ = (reflection hf * reflection hf) * reflection hg := (mul_assoc _ _ _).symm
      _ = 1 * reflection hg := by rw [hr2]
      _ = reflection hg := one_mul _

end Generic

section StepOne

variable {p n : ℕ} [Fact p.Prime]

private def swapRoot (p n : ℕ) (a b : Fin (n + 1)) : Fin (n + 1) → ZMod p :=
  Pi.single a (1 : ZMod p) - Pi.single b (1 : ZMod p)

private def swapForm (p n : ℕ) (a b : Fin (n + 1)) :
    Module.Dual (ZMod p) (Fin (n + 1) → ZMod p) :=
  (LinearMap.proj a : Module.Dual (ZMod p) (Fin (n + 1) → ZMod p)) - LinearMap.proj b

private theorem swapForm_swapRoot {a b : Fin (n + 1)} (hab : a ≠ b) :
    swapForm p n a b (swapRoot p n a b) = 2 := by
  simp [swapForm, swapRoot, Pi.single_apply, hab]
  norm_num

private theorem coordPerm_swap_apply {a b : Fin (n + 1)} (hab : a ≠ b)
    (v : Fin (n + 1) → ZMod p) :
    coordPerm p n (Equiv.swap a b) v =
      v - (swapForm p n a b v) • swapRoot p n a b := by
  funext i
  simp only [coordPerm_apply, Pi.sub_apply, Pi.smul_apply, swapForm, swapRoot,
    LinearMap.sub_apply, LinearMap.proj_apply]
  rw [Equiv.symm_swap a b]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left]
    simp [hab]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right]
      simp [hab]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      simp [hia, hib]

private theorem root_coord_eq_of_comm (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {T : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)} (hT : IsLinRefl T)
    {x : Fin (n + 1) → ZMod p} {f : Module.Dual (ZMod p) (Fin (n + 1) → ZMod p)}
    (hfx : f x = 2) (hTapply : ∀ v, T v = v - f v • x)
    (hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      T * coordPerm p n σ = coordPerm p n σ * T) :
    ∀ i j : Fin n, x i.castSucc = x j.castSucc := by
  have hTx : T x = -x := by
    rw [hTapply, hfx]
    module
  have hx0 : x ≠ 0 := (ne_zero_of_two (zmod_two_ne_zero hp2) hfx).1
  have htrans : ∀ i j : Fin n,
      coordPerm p n (Equiv.swap i.castSucc j.castSucc) x = x := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Equiv.swap_self]
      change (coordPerm p n (1 : Equiv.Perm (Fin (n + 1)))) x = x
      rw [map_one]
      rfl
    · set τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc j.castSucc with hτdef
      have hτlast : τ (Fin.last n) = Fin.last n := by
        rw [hτdef]
        exact Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last i).symm
          (Fin.castSucc_ne_last j).symm
      have hcommτ := hcomm τ hτlast
      have hTτ : T (coordPerm p n τ x) = -(coordPerm p n τ x) := by
        have h := congrArg (fun S => S x) hcommτ
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTx, map_neg] at h
        exact h
      have hnonzero : coordPerm p n τ x ≠ 0 := by
        simpa using ((coordPerm p n τ).injective.ne hx0)
      obtain ⟨lam, hlam⟩ := IsLinRefl.anti_eq_smul hp2 hT hx0 hTx hTτ
      have hlam2 : lam * lam = 1 := by
        have hinv : coordPerm p n τ (coordPerm p n τ x) = x := by
          rw [← LinearEquiv.mul_apply, ← map_mul, hτdef, Equiv.swap_mul_self, map_one]
          rfl
        have h := congrArg (fun y => coordPerm p n τ y) hlam
        rw [hinv] at h
        rw [map_smul, hlam, smul_smul] at h
        have hzero : (lam * lam - 1) • x = 0 := by
          rw [sub_smul, one_smul, ← h, sub_self]
        have hsub : lam * lam - 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hx0
        exact sub_eq_zero.mp hsub
      rcases mul_self_eq_one_iff.mp hlam2 with hlam1 | hlamneg
      · rw [hlam1, one_smul] at hlam
        exact hlam
      · exfalso
        have hsupp : ∀ m : Fin (n + 1), m ≠ i.castSucc → m ≠ j.castSucc → x m = 0 := by
          intro m hm1 hm2
          have hfix : τ.symm m = m := by
            rw [hτdef, Equiv.symm_swap]
            exact Equiv.swap_apply_of_ne_of_ne hm1 hm2
          have h := congrArg (fun y => y m) hlam
          rw [coordPerm_apply, hfix, Pi.smul_apply, hlamneg] at h
          have h' : x m = -x m := by simpa using h
          have h2' : x m + x m = 0 := eq_neg_iff_add_eq_zero.mp h'
          have h2 : (2 : ZMod p) * x m = 0 := by rw [two_mul]; exact h2'
          exact (mul_eq_zero.mp h2).resolve_left (zmod_two_ne_zero hp2)
        have hxj : x j.castSucc = -x i.castSucc := by
          have h := congrArg (fun y => y i.castSucc) hlam
          rw [coordPerm_apply, Pi.smul_apply, hlamneg] at h
          rw [hτdef, Equiv.symm_swap, Equiv.swap_apply_left] at h
          simpa using h
        have hxi : x i.castSucc ≠ 0 := by
          intro h0
          apply hx0
          funext m
          by_cases hm1 : m = i.castSucc
          · subst hm1
            exact h0
          · by_cases hm2 : m = j.castSucc
            · subst hm2
              calc x j.castSucc = -x i.castSucc := hxj
                _ = 0 := by rw [h0, neg_zero]
            · exact hsupp m hm1 hm2
        obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
        set τ' : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc k.castSucc with hτ'def
        have hτ'last : τ' (Fin.last n) = Fin.last n := by
          rw [hτ'def]
          exact Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last i).symm
            (Fin.castSucc_ne_last k).symm
        have hcommτ' := hcomm τ' hτ'last
        have hTτ' : T (coordPerm p n τ' x) = -(coordPerm p n τ' x) := by
          have h := congrArg (fun S => S x) hcommτ'
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTx, map_neg] at h
          exact h
        obtain ⟨mu, hmu⟩ := IsLinRefl.anti_eq_smul hp2 hT hx0 hTx hTτ'
        have hk0 : x k.castSucc = 0 := hsupp k.castSucc (by simpa using hki) (by simpa using hkj)
        have hval := congrArg (fun y => y k.castSucc) hmu
        rw [coordPerm_apply, Pi.smul_apply] at hval
        rw [hτ'def, Equiv.symm_swap, Equiv.swap_apply_right] at hval
        rw [hk0, smul_zero] at hval
        exact hxi hval
  intro i j
  by_cases hij : i = j
  · subst hij
    rfl
  · have h := htrans i j
    have hval := congrArg (fun y => y i.castSucc) h
    rw [coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left] at hval
    exact hval.symm

private theorem coordPerm_swap_single {a b : Fin (n + 1)} (hab : a ≠ b) (c : ZMod p) :
    coordPerm p n (Equiv.swap a b) (Pi.single a c) = Pi.single b c := by
  funext i
  rw [coordPerm_apply, Pi.single_apply, Pi.single_apply, Equiv.symm_swap a b]
  by_cases hib : i = b
  · subst hib
    rw [Equiv.swap_apply_right]
    simp
  · by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left]
      simp [hab, hab.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      simp [hia, hib]

theorem exists_shape_of_comm_braid (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (j : Fin n) (hj : j.val + 1 = n)
    {T : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)} (hT : IsLinRefl T)
    (hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      T * coordPerm p n σ = coordPerm p n σ * T)
    (hbraid : T * coordPerm p n (Equiv.swap j.castSucc j.succ) * T =
      coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ))
    (hne : T ≠ coordPerm p n (Equiv.swap j.castSucc j.succ)) :
    ∃ c u : ZMod p, u * (((n : ZMod p) + 1) * c + 1) = 1 - c ∧
      ∀ v, T v = v - (c * (∑ i : Fin n, v i.castSucc) + (c + 1) * v (Fin.last n)) •
        (kThreeRoot p n + u • (1 : Fin (n + 1) → ZMod p)) := by
  obtain ⟨x, f, hfx, hTapply⟩ := hT
  have hT' : IsLinRefl T := ⟨x, f, hfx, hTapply⟩
  have hcoord := root_coord_eq_of_comm hp2 hn hT' hfx hTapply hcomm
  let i0 : Fin n := ⟨0, by omega⟩
  let b : ZMod p := x i0.castSucc
  let a : ZMod p := x (Fin.last n) - b
  have hxdecomp : x = a • kThreeRoot p n + b • (1 : Fin (n + 1) → ZMod p) := by
    funext m
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    rcases Fin.eq_castSucc_or_eq_last m with ⟨k, rfl⟩ | rfl
    · have hk : x k.castSucc = x i0.castSucc := hcoord k i0
      rw [hk, kThreeRoot, Pi.single_apply, if_neg (Fin.castSucc_ne_last k), Pi.one_apply]
      simp [b]
    · rw [kThreeRoot, Pi.single_eq_same, Pi.one_apply]
      simp [a, b]
  have htrans : ∀ i j : Fin n, i ≠ j →
      coordPerm p n (Equiv.swap i.castSucc j.castSucc) x = x := by
    intro i j hij
    funext m
    rw [coordPerm_apply, Equiv.symm_swap i.castSucc j.castSucc]
    by_cases hmi : m = i.castSucc
    · subst hmi
      rw [Equiv.swap_apply_left]
      exact hcoord j i
    · by_cases hmj : m = j.castSucc
      · subst hmj
        rw [Equiv.swap_apply_right]
        exact hcoord i j
      · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
  have hfcomp : ∀ (i j : Fin n) (hij : i ≠ j) (v : Fin (n + 1) → ZMod p),
      f (coordPerm p n (Equiv.swap i.castSucc j.castSucc) v) = f v := by
    intro i j hij v
    set τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc j.castSucc with hτdef
    have hτlast : τ (Fin.last n) = Fin.last n := by
      rw [hτdef]
      exact Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last i).symm
        (Fin.castSucc_ne_last j).symm
    have hτx : coordPerm p n τ x = x := htrans i j hij
    have h := congrArg (fun S => S v) (hcomm τ hτlast)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hTapply, hTapply, map_sub, map_smul,
      hτx] at h
    have hcancel : f (coordPerm p n τ v) • x = f v • x := sub_right_inj.mp h
    have hzero : (f (coordPerm p n τ v) - f v) • x = 0 := by
      rw [sub_smul, hcancel, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (by
      have hx0 : x ≠ 0 := (ne_zero_of_two (zmod_two_ne_zero hp2) hfx).1
      exact hx0))
  let A : ZMod p := f (Pi.single i0.castSucc 1)
  let B : ZMod p := f (Pi.single (Fin.last n) 1)
  have hcoeff : ∀ i : Fin n, f (Pi.single i.castSucc 1) = A := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rfl
    · have h := hfcomp i i0 hi (Pi.single i.castSucc 1)
      rw [coordPerm_swap_single (p := p) (n := n) (show i.castSucc ≠ i0.castSucc by
        simpa using hi)] at h
      exact h.symm
  have hform : ∀ v : Fin (n + 1) → ZMod p,
      f v = A * (∑ i : Fin n, v i.castSucc) + B * v (Fin.last n) := by
    intro v
    have hsingle : ∀ i : Fin (n + 1),
        (fun j => if i = j then (1 : ZMod p) else 0) = Pi.single i 1 := by
      intro i
      funext j
      rw [Pi.single_apply]
      by_cases h : i = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [LinearMap.pi_apply_eq_sum_univ f v, Fin.sum_univ_castSucc]
    simp only [hsingle, hcoeff]
    rw [Finset.mul_sum]
    simp [smul_eq_mul, mul_comm, B]
  have hjsucc : j.succ = Fin.last n := Fin.ext (by rw [Fin.val_succ, hj]; rfl)
  have hjn : j.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  let t : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
    coordPerm p n (Equiv.swap j.castSucc j.succ)
  have ht_refl : t = reflection (swapForm_swapRoot (p := p) (n := n) hjn) := by
    ext v
    rw [coordPerm_swap_apply hjn, reflection_apply]
  have hT_refl : T = reflection hfx := by
    ext v
    rw [hTapply, reflection_apply]
  have hT2 : T * T = 1 := by
    rw [hT_refl]
    exact reflection_mul_self_of_apply hfx
  have ht2 : t * t = 1 := by
    rw [ht_refl]
    exact reflection_mul_self_of_apply _
  have h3 : (T * t) ^ 3 = 1 := by
    have hcube : (T * t) ^ 3 = (T * t * T) * (t * T * t) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      group
    have hbraid' : T * t * T = t * T * t := hbraid
    rw [hcube, hbraid']
    rw [show t * T * t * (t * T * t) = t * (T * T) * t by
      rw [show t * T * t * (t * T * t) = t * T * (t * t) * T * t by group, ht2]
      group, hT2]
    simp [ht2]
  rw [hT_refl, ht_refl] at h3
  have hdistinct : reflection hfx ≠ reflection (swapForm_swapRoot (p := p) (n := n) hjn) := by
    intro h
    apply hne
    calc T = reflection hfx := hT_refl
      _ = reflection (swapForm_swapRoot (p := p) (n := n) hjn) := h
      _ = t := ht_refl.symm
      _ = coordPerm p n (Equiv.swap j.castSucc j.succ) := rfl
  have hcross := reflection_mul_reflection_pow_three_cross (zmod_two_ne_zero hp2) hfx
    (swapForm_swapRoot (p := p) (n := n) hjn) h3 hdistinct
  have hfroot : f (swapRoot p n j.castSucc j.succ) = A - B := by
    rw [swapRoot, map_sub, hcoeff j, hjsucc]
  have hformroot : swapForm p n j.castSucc j.succ x = -a := by
    rw [swapForm, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply, hjsucc,
      hcoord j i0]
    simp [a, b]
  have hcrossAB : (A - B) * (-a) = 1 := by
    rw [← hfroot, ← hformroot]
    exact hcross
  have ha_ne : a ≠ 0 := by
    intro ha0
    have h01 : (0 : ZMod p) = 1 := by simpa [ha0] using hcrossAB
    exact zero_ne_one h01
  have hdiff : a * B - a * A = 1 := by
    rw [← hcrossAB]
    ring
  have haB : a * B = a * A + 1 := by
    linear_combination hdiff
  have hfx_sum : (2 : ZMod p) = a * B + b * (((n : ZMod p)) * A + B) := by
    have h := hfx
    rw [← h]
    rw [hform x, hxdecomp]
    simp [kThreeRoot, Pi.single_apply, Finset.sum_const, nsmul_eq_mul, Pi.add_apply,
      Pi.smul_apply]
    ring
  let c : ZMod p := a * A
  let u : ZMod p := b / a
  have hbu : b = u * a := by
    rw [show u = b / a by rfl]
    exact (div_mul_cancel₀ b ha_ne).symm
  have hb : b * (((n : ZMod p)) * A + B) = 1 - a * A := by
    have h1 : 2 - a * B = b * (((n : ZMod p)) * A + B) := by
      linear_combination hfx_sum
    rw [haB] at h1
    rw [← h1]
    ring
  have hmul : b * (((n : ZMod p) + 1) * (a * A) + 1) = a * (1 - a * A) := by
    calc b * (((n : ZMod p) + 1) * (a * A) + 1)
        = b * ((n : ZMod p) * (a * A) + (a * A + 1)) := by ring
      _ = b * ((n : ZMod p) * (a * A) + a * B) := by rw [← haB]
      _ = a * (b * ((n : ZMod p) * A + B)) := by ring
      _ = a * (1 - a * A) := by rw [hb]
  have hu : u * (((n : ZMod p) + 1) * c + 1) = 1 - c := by
    rw [show u = b / a by rfl, show c = a * A by rfl]
    field_simp [ha_ne]
    linear_combination hmul
  refine ⟨c, u, hu, fun v => ?_⟩
  have hv := hform v
  rw [hTapply, hxdecomp, hv]
  set X : ZMod p := A * (∑ i : Fin n, v i.castSucc) + B * v (Fin.last n) with hXdef
  set Y : ZMod p := c * (∑ i : Fin n, v i.castSucc) + (c + 1) * v (Fin.last n) with hYdef
  have hX : X * a = Y := by
    rw [hXdef, hYdef, show c = a * A by rfl]
    linear_combination (v (Fin.last n)) * haB
  have hY : X * b = Y * u := by
    rw [hXdef, hYdef, show c = a * A by rfl, hbu]
    linear_combination (u * v (Fin.last n)) * haB
  change v - X • (a • kThreeRoot p n + b • (1 : Fin (n + 1) → ZMod p)) =
    v - Y • (kThreeRoot p n + u • (1 : Fin (n + 1) → ZMod p))
  rw [sub_right_inj]
  calc X • (a • kThreeRoot p n + b • 1)
      = (X * a) • kThreeRoot p n + (X * b) • 1 := by
        rw [smul_add, smul_smul, smul_smul]
    _ = Y • kThreeRoot p n + (Y * u) • 1 := by rw [hX, hY]
    _ = Y • (kThreeRoot p n + u • 1) := by
        rw [smul_add, smul_smul]

theorem eq_kThreeRefl_or_transvection (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (j : Fin n) (hj : j.val + 1 = n)
    {T : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)} (hT : IsLinRefl T)
    (hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      T * coordPerm p n σ = coordPerm p n σ * T)
    (hbraid : T * coordPerm p n (Equiv.swap j.castSucc j.succ) * T =
      coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ))
    (hne : T ≠ coordPerm p n (Equiv.swap j.castSucc j.succ))
    (hpairT : (T * kRefl p n) ^ 2 = 1 ∨ (T * kRefl p n) ^ 3 = 1)
    (hpairT' : ((coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ)) * kRefl p n) ^ 2 = 1 ∨
      ((coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ)) * kRefl p n) ^ 3 = 1)
    (hneB : T ≠ kRefl p n) :
    (p ∣ n + 3 ∧ T = kThreeRefl p n) ∨
      ∃ β : Module.Dual (ZMod p) (Fin (n + 1) → ZMod p), β ≠ 0 ∧
        β (kRoot p n) = 0 ∧
        ∀ v, T (kRefl p n v) = v + β v • kRoot p n := by
  obtain ⟨c, u, hu, hshape⟩ :=
    exists_shape_of_comm_braid hp2 hn j hj hT hcomm hbraid hne
  let V := Fin (n + 1) → ZMod p
  let kSum : Module.Dual (ZMod p) V := ∑ i : Fin n, LinearMap.proj i.castSucc
  let h : V := kThreeRoot p n + u • (1 : V)
  let α : Module.Dual (ZMod p) V := c • kSum + (c + 1) • kCoroot p n
  have hαval : ∀ v : V,
      α v = c * (∑ i : Fin n, v i.castSucc) + (c + 1) * v (Fin.last n) := by
    intro v
    simp only [α, kSum, kCoroot, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.sum_apply]
    change c * (∑ d : Fin n, v d.castSucc) + (c + 1) * v (Fin.last n) =
      c * (∑ i : Fin n, v i.castSucc) + (c + 1) * v (Fin.last n)
    ring
  have hsingle_cast : ∀ i : Fin n, kThreeRoot p n i.castSucc = 0 := by
    intro i
    rw [kThreeRoot, Pi.single_apply, if_neg (Fin.castSucc_ne_last i)]
  have hsum_n : (∑ i : Fin n, (kThreeRoot p n + u • (1 : V)) i.castSucc) =
      (n : ZMod p) * u := by
    rw [Finset.sum_congr rfl (fun i _ => ?_)]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Pi.add_apply, Pi.smul_apply, Pi.one_apply, hsingle_cast]
      ring
  have hlast_h : (kThreeRoot p n + u • (1 : V)) (Fin.last n) = 1 + u := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.one_apply, kThreeRoot, Pi.single_eq_same]
    ring
  have hαh : α h = 2 := by
    rw [hαval]
    simp only [h]
    rw [hsum_n, hlast_h]
    linear_combination hu
  have hT_refl : T = reflection hαh := by
    apply LinearEquiv.ext
    intro v
    rw [reflection_apply, hshape v, sub_right_inj, hαval]
  let t : V ≃ₗ[ZMod p] V := coordPerm p n (Equiv.swap j.castSucc j.succ)
  have ht2 : t * t = 1 := by
    rw [show t = coordPerm p n (Equiv.swap j.castSucc j.succ) by rfl]
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have ht_apply : ∀ v : V, t (t v) = v := by
    intro v
    rw [← LinearEquiv.mul_apply, ht2]
    rfl
  have hjsucc : j.succ = Fin.last n := Fin.ext (by rw [Fin.val_succ, hj]; rfl)
  let h' : V := t h
  let α' : Module.Dual (ZMod p) V := α.comp t.toLinearMap
  have hα' : α' h' = 2 := by
    rw [show α' h' = α (t (t h)) by rfl, ht_apply, hαh]
  let T' : V ≃ₗ[ZMod p] V := t * T * t
  have hT'_apply : ∀ v : V, T' v = v - α' v • h' := by
    intro v
    rw [show T' v = t (T (t v)) by
      rw [show T' = t * T * t by rfl, LinearEquiv.mul_apply, LinearEquiv.mul_apply]]
    rw [hT_refl, reflection_apply, map_sub, map_smul, ht_apply]
    rfl
  have hT'_refl : T' = reflection hα' := by
    apply LinearEquiv.ext
    intro v
    rw [reflection_apply, hT'_apply]
  have hzero_ne : (0 : Fin (n + 1)) ≠ j.castSucc ∧ (0 : Fin (n + 1)) ≠ j.succ := by
    constructor
    · intro h0
      have hv := congrArg Fin.val h0
      rw [Fin.val_zero, Fin.val_castSucc] at hv
      omega
    · intro h0
      have hv := congrArg Fin.val h0
      rw [Fin.val_zero, Fin.val_succ] at hv
      omega
  have h0last : (0 : Fin (n + 1)) ≠ Fin.last n := by
    simpa [hjsucc] using hzero_ne.2
  have h_coord : ∀ i : Fin (n + 1), i ≠ Fin.last n → h i = u := by
    intro i hi
    change (kThreeRoot p n + u • (1 : V)) i = u
    rw [Pi.add_apply, Pi.smul_apply, Pi.one_apply, kThreeRoot, Pi.single_apply,
      if_neg hi]
    ring
  have hhj0 : h' 0 = u := by
    rw [show h' = t h by rfl, show t = coordPerm p n (Equiv.swap j.castSucc j.succ) by rfl,
      coordPerm_apply, Equiv.symm_swap]
    rw [Equiv.swap_apply_of_ne_of_ne hzero_ne.1 hzero_ne.2]
    exact h_coord 0 h0last
  have hhj : h' j.castSucc = 1 + u := by
    rw [show h' = t h by rfl, show t = coordPerm p n (Equiv.swap j.castSucc j.succ) by rfl,
      coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left, hjsucc]
    simpa [h] using hlast_h
  have hhlast : h' (Fin.last n) = u := by
    rw [show h' = t h by rfl, show t = coordPerm p n (Equiv.swap j.castSucc j.succ) by rfl,
      coordPerm_apply, Equiv.symm_swap, ← hjsucc, Equiv.swap_apply_right]
    exact h_coord j.castSucc (Fin.castSucc_ne_last j)
  have hk0 : kRoot p n 0 = 1 := by
    rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_apply, if_neg h0last]
    ring
  have hkj : kRoot p n j.castSucc = 1 := by
    rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_apply,
      if_neg (Fin.castSucc_ne_last j)]
    ring
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hαh
    exact (zmod_two_ne_zero hp2) hαh.symm
  have hh'0 : h' ≠ 0 := by
    intro h0
    have ht_h' : t h' = h := by
      rw [show h' = t h by rfl]
      exact ht_apply h
    rw [h0, map_zero] at ht_h'
    exact hh0 ht_h'.symm
  have hT'_lin : IsLinRefl T' := ⟨h', α', hα', hT'_apply⟩
  have hT'h' : T' h' = -h' := by
    rw [hT'_apply, hα']
    module
  have hkroot : kRoot p n (Fin.last n) = 2 := by
    rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
    norm_num
  have hne' : T' ≠ kRefl p n := by
    intro hEq
    have hT'h0 : T' (kRoot p n) = -kRoot p n := by
      rw [hEq, kRefl_apply, hkroot, two_smul]
      abel
    obtain ⟨mu, hmu⟩ := IsLinRefl.anti_eq_smul hp2 hT'_lin hh'0 hT'h' hT'h0
    have e0 := congrArg (fun w => w 0) hmu
    have ej := congrArg (fun w => w j.castSucc) hmu
    rw [Pi.smul_apply, hhj0, hk0] at e0
    rw [Pi.smul_apply, hhj, hkj] at ej
    have hmu0 : mu ≠ 0 := by
      intro hm
      rw [hm] at e0
      norm_num at e0
    have hueq : u = 1 + u := by
      have h : mu * u = mu * (1 + u) := by linear_combination -e0 + ej
      exact mul_left_cancel₀ hmu0 h
    have h10 : (1 : ZMod p) = 0 := by linear_combination -hueq
    exact one_ne_zero h10
  have hpair' : (reflection hα' * reflection (kCoroot_kRoot p n)) ^ 2 = 1 ∨
      (reflection hα' * reflection (kCoroot_kRoot p n)) ^ 3 = 1 := by
    change (T' * kRefl p n) ^ 2 = 1 ∨ (T' * kRefl p n) ^ 3 = 1 at hpairT'
    simpa [hT'_refl, kRefl] using hpairT'
  have hjn : j.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hα'k : α' (kRoot p n) = ((n : ZMod p) + 2) * c + 1 := by
    have htkr : t (kRoot p n) = (1 : V) + Pi.single j.castSucc 1 := by
      funext i
      rw [show t = coordPerm p n (Equiv.swap j.castSucc j.succ) by rfl, coordPerm_apply,
        Equiv.symm_swap]
      by_cases hi : i = j.castSucc
      · subst hi
        rw [Equiv.swap_apply_left, hjsucc]
        rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
        rw [Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
      · by_cases hi' : i = j.succ
        · subst hi'
          rw [Equiv.swap_apply_right, hjsucc, hkj]
          rw [Pi.add_apply, Pi.one_apply, Pi.single_apply,
            if_neg (Fin.castSucc_ne_last j).symm]
          norm_num
        · have hil : i ≠ Fin.last n := by rwa [hjsucc] at hi'
          rw [Equiv.swap_apply_of_ne_of_ne hi hi', kRoot, Pi.add_apply, Pi.one_apply,
            Pi.single_apply, if_neg hil]
          rw [Pi.add_apply, Pi.one_apply, Pi.single_apply, if_neg hi]
          ring
    have hsum1 : (∑ i : Fin n,
        (((1 : V) + Pi.single j.castSucc (1 : ZMod p)) : V) i.castSucc) =
        (n : ZMod p) + 1 := by
      have hcongr : (∑ i : Fin n,
          (((1 : V) + Pi.single j.castSucc (1 : ZMod p)) : V) i.castSucc) =
          ∑ i : Fin n, ((1 : ZMod p) +
            if j = i then 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => by
          change (1 : ZMod p) +
            (Pi.single j.castSucc (1 : ZMod p) : V) i.castSucc =
            1 + if j = i then 1 else 0
          by_cases h : j = i
          · rw [h]
            simp [Pi.single_apply]
          · have hc : ¬ j.castSucc = i.castSucc := by
              simpa [Fin.castSucc_inj] using h
            simp [Pi.single_apply, h, hc])
      rw [hcongr, Finset.sum_add_distrib]
      congr 1
      · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      · rw [Finset.sum_eq_single j]
        · rw [if_pos rfl]
        · intro b _ hb
          rw [if_neg (Ne.symm hb)]
        · intro hj
          simp at hj
    have hlast1 : (((1 : V) + Pi.single j.castSucc (1 : ZMod p)) : V)
        (Fin.last n) = 1 := by
      rw [Pi.add_apply, Pi.one_apply, Pi.single_apply,
        if_neg (Fin.castSucc_ne_last j).symm]
      norm_num
    rw [show α' (kRoot p n) = α (t (kRoot p n)) by rfl, htkr, hαval, hsum1, hlast1]
    ring
  have hα'u : kCoroot p n h' = u := by
    rw [kCoroot_apply, hhlast]
  have hne'' : reflection hα' ≠ reflection (kCoroot_kRoot p n) := by
    intro h
    apply hne'
    rw [hT'_refl, kRefl]
    exact h
  rcases hpair' with hsq | hcube
  ·
    have hcross := reflection_mul_reflection_pow_two_cross (zmod_two_ne_zero hp2) hα'
      (kCoroot_kRoot p n) hsq hne''
    have hu0 : u = 0 := by
      have := hcross.2
      rwa [hα'u] at this
    have hc : ((n : ZMod p) + 2) * c + 1 = 0 := by
      have := hcross.1
      rwa [hα'k] at this
    have hc1 : c = 1 := by
      have h := hu
      rw [hu0, zero_mul] at h
      linear_combination h
    left
    refine ⟨?_, ?_⟩
    · have h3 : ((n + 3 : ℕ) : ZMod p) = 0 := by
        have h1 : (n : ZMod p) + 3 = 0 := by
          calc (n : ZMod p) + 3 = ((n : ZMod p) + 2) * c + 1 := by rw [hc1]; ring
            _ = 0 := hc
        simpa using h1
      exact (CharP.cast_eq_zero_iff (ZMod p) p (n + 3)).mp h3
    · apply LinearEquiv.ext
      intro v
      rw [hshape v, hc1, hu0, kThreeRefl_apply]
      simp
      ring
  ·
    have hcross := reflection_mul_reflection_pow_three_cross (zmod_two_ne_zero hp2) hα'
      (kCoroot_kRoot p n) hcube hne''
    have hu_eq : u * (((n : ZMod p) + 2) * c + 1) = 1 := by
      rw [← hα'k, ← hα'u, mul_comm]
      exact hcross
    have hcu : c * (u - 1) = 0 := by
      have h1 := hu
      linear_combination hu_eq - h1
    have hu1 : u = 1 := by
      rcases mul_eq_zero.mp hcu with hc0 | hu0
      ·
        have h1 := hu
        rw [hc0] at h1
        simpa using h1
      · linear_combination hu0
    have hnc : ((n : ZMod p) + 2) * c = 0 := by
      have h1 := hu
      rw [hu1, one_mul] at h1
      linear_combination h1
    have hhroot : h = kRoot p n := by
      change kThreeRoot p n + u • (1 : V) = kRoot p n
      rw [hu1, one_smul]
      rfl
    have hαroot : α (kRoot p n) = 2 := by
      rw [← hhroot]
      exact hαh
    right
    refine ⟨kCoroot p n - α, ?_, ?_, ?_⟩
    · intro hzero
      have hα_eq : α = kCoroot p n := (sub_eq_zero.mp hzero).symm
      apply hneB
      apply LinearEquiv.ext
      intro v
      rw [hT_refl, kRefl_apply, reflection_apply, hα_eq, hhroot, kCoroot_apply]
    · rw [LinearMap.sub_apply, kCoroot_apply]
      have hkroot : kRoot p n (Fin.last n) = 2 := by
        simp [kRoot, kThreeRoot, Pi.single_apply, Pi.add_apply]
        norm_num
      rw [hkroot, hαroot]
      ring
    · intro v
      have hTh0 : T (kRoot p n) = -kRoot p n := by
        rw [hT_refl, reflection_apply, hαroot, hhroot, two_smul]
        abel
      rw [kRefl_apply, map_sub, map_smul, hTh0, hT_refl, reflection_apply, hhroot,
        LinearMap.sub_apply, kCoroot_apply]
      module

end StepOne

end CFSG.StandardType.TypeAReflOver

end

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.TypeAReflOver
open CFSG.LieType.Universal.SpecialLinear Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section BStarForm

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {n : ℕ} {F : Type}
  [Field F] {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.eq_kThreeRefl_of_pairings (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (j : Fin n) (hj : j.val + 1 = n)
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hC.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs,
      κ (Additive.ofMul (hC.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
        kRefl p n (κ (Additive.ofMul b)))
    (r : MulAut ↥Bs) (hr : GGIsReflection p r) (hr_ind : r ∈ ggInduced ⊤ Bs)
    (hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      r * hC.permAut₁ σ = hC.permAut₁ σ * r)
    (hbraid : r * hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r =
      hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
        hC.permAut₁ (Equiv.swap j.castSucc j.succ))
    (hrnet : r ≠ hC.permAut₁ (Equiv.swap j.castSucc j.succ))
    (hpairr : (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) ^ 2 = 1 ∨
      (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) ^ 3 = 1)
    (hpairr' : ((hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
        hC.permAut₁ (Equiv.swap j.castSucc j.succ)) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ)) ^ 2 = 1 ∨
      ((hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
        hC.permAut₁ (Equiv.swap j.castSucc j.succ)) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ)) ^ 3 = 1)
    (hrne : r ≠ hC.permAut₂ (Equiv.swap j.castSucc j.succ))
    (hNT : GGNoTransvection p Bs) :
    p ∣ n + 3 ∧ ∀ b : ↥Bs,
      κ (Additive.ofMul (r b)) = kThreeRefl p n (κ (Additive.ofMul b)) := by
  let T : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) := ggLin (p := p) κ r
  have hT : IsLinRefl T := by
    obtain ⟨x, f, hfx, hTapply⟩ := exists_of_ggIsReflection κ hr
    exact ⟨x, f, hfx, hTapply⟩
  have hbκ : ∀ v : Fin (n + 1) → ZMod p,
      κ (Additive.ofMul (Additive.toMul (κ.symm v))) = v := by
    intro v
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hggt_all : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ggLin (p := p) κ (hC.permAut₁ σ) = coordPerm p n σ := by
    intro σ
    apply LinearEquiv.ext
    intro v
    set b : ↥Bs := Additive.toMul (κ.symm v) with hb
    have hbv : κ (Additive.ofMul b) = v := hbκ v
    rw [← hbv, ggLin_apply_ofMul, hκ₁]
  have hggt : ggLin (p := p) κ (hC.permAut₁ (Equiv.swap j.castSucc j.succ)) =
      coordPerm p n (Equiv.swap j.castSucc j.succ) := hggt_all _
  have hbaeq : ggLin (p := p) κ (hC.permAut₂ (Equiv.swap j.castSucc j.succ)) =
      kRefl p n := by
    apply LinearEquiv.ext
    intro v
    set b : ↥Bs := Additive.toMul (κ.symm v) with hb
    have hbv : κ (Additive.ofMul b) = v := hbκ v
    rw [← hbv, ggLin_apply_ofMul, hκ₂]
  have hcommT : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      T * coordPerm p n σ = coordPerm p n σ * T := by
    intro σ hσ
    rw [show T = ggLin (p := p) κ r by rfl, ← hggt_all σ]
    rw [← map_mul, ← map_mul]
    rw [hcomm σ hσ]
  have hbraidT : T * coordPerm p n (Equiv.swap j.castSucc j.succ) * T =
      coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ) := by
    rw [show T = ggLin (p := p) κ r by rfl,
      show coordPerm p n (Equiv.swap j.castSucc j.succ) =
        ggLin (p := p) κ (hC.permAut₁ (Equiv.swap j.castSucc j.succ)) from hggt.symm]
    simp only [← map_mul]
    rw [hbraid]
  have hneT : T ≠ coordPerm p n (Equiv.swap j.castSucc j.succ) := by
    intro h
    apply hrnet
    apply ggLin_injective (p := p) κ
    rw [← hggt] at h
    exact h
  have hneB : T ≠ kRefl p n := by
    intro h
    apply hrne
    apply ggLin_injective (p := p) κ
    rw [← hbaeq] at h
    exact h
  have hmap_pow : ∀ (a : MulAut ↥Bs) (m : ℕ) (h : a ^ m = 1),
      (ggLin (p := p) κ a) ^ m = 1 := by
    intro a m h
    simpa [← map_pow] using congrArg (ggLin (p := p) κ) h
  have hpairT : (T * kRefl p n) ^ 2 = 1 ∨ (T * kRefl p n) ^ 3 = 1 := by
    rcases hpairr with h2 | h3
    · left
      simpa [T, hbaeq] using hmap_pow (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) 2 h2
    · right
      simpa [T, hbaeq] using hmap_pow (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) 3 h3
  have hpairT' : ((coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ)) * kRefl p n) ^ 2 = 1 ∨
      ((coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
        coordPerm p n (Equiv.swap j.castSucc j.succ)) * kRefl p n) ^ 3 = 1 := by
    have hrefl : ggLin (p := p) κ
        (hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
          hC.permAut₁ (Equiv.swap j.castSucc j.succ)) =
        coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
          coordPerm p n (Equiv.swap j.castSucc j.succ) := by
      rw [map_mul, map_mul, hggt]
    have hrefl' : ggLin (p := p) κ
        ((hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
          hC.permAut₁ (Equiv.swap j.castSucc j.succ)) *
          hC.permAut₂ (Equiv.swap j.castSucc j.succ)) =
        (coordPerm p n (Equiv.swap j.castSucc j.succ) * T *
          coordPerm p n (Equiv.swap j.castSucc j.succ)) * kRefl p n := by
      rw [map_mul, hrefl, hbaeq]
    rcases hpairr' with h2 | h3
    · left
      have := hmap_pow (hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
        hC.permAut₁ (Equiv.swap j.castSucc j.succ) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ)) 2 h2
      rwa [hrefl'] at this
    · right
      have := hmap_pow (hC.permAut₁ (Equiv.swap j.castSucc j.succ) * r *
        hC.permAut₁ (Equiv.swap j.castSucc j.succ) *
        hC.permAut₂ (Equiv.swap j.castSucc j.succ)) 3 h3
      rwa [hrefl'] at this
  have hstep := eq_kThreeRefl_or_transvection hC.odd hC.three_le j hj hT hcommT hbraidT hneT
    hpairT hpairT' hneB
  rcases hstep with ⟨hdiv, hTk⟩ | ⟨β, hβne, hβroot, hβapply⟩
  · refine ⟨hdiv, fun b => ?_⟩
    have h1 : ggLin (p := p) κ r = kThreeRefl p n := hTk
    have h := ggLin_apply_ofMul (p := p) κ r b
    rw [h1] at h
    exact h.symm
  · exfalso
    have hba_ind : hC.permAut₂ (Equiv.swap j.castSucc j.succ) ∈ ggInduced ⊤ Bs := by
      refine ⟨φ₂ (slPerm hC.two (Equiv.swap j.castSucc j.succ)), trivial,
        hC.perm_mem_normalizer₂ _, ?_⟩
      intro b
      exact hC.permAut₂_apply (Equiv.swap j.castSucc j.succ) b
    have happly : ∀ v : Fin (n + 1) → ZMod p, ggLin (p := p) κ
        (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) v =
        v + β v • kRoot p n := by
      intro v
      rw [map_mul, LinearEquiv.mul_apply, hbaeq]
      exact hβapply v
    have hkw : kRoot p n ≠ 0 := by
      intro hkw0
      have h2 : kRoot p n (Fin.last n) = 2 := by
        rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
        norm_num
      rw [hkw0, Pi.zero_apply] at h2
      exact (zmod_two_ne_zero hC.odd) h2.symm
    have htrans : GGIsTransvection p (r * hC.permAut₂ (Equiv.swap j.castSucc j.succ)) :=
      ggIsTransvection_of_apply κ hkw hβne hβroot happly
    exact hNT _ (mul_mem_ggInduced hr_ind hba_ind) htrans

end BStarForm

end CFSG.StandardType

end
