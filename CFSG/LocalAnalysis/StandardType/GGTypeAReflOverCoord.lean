module

public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverDefs
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueInj
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueSwap

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ReflAux

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  {x y z : M} {f g k : Module.Dual K M}

theorem reflection_mul_reflection_mul_self_apply (hf : f x = 2) (hg : g y = 2) (z : M) :
    (reflection hf * reflection hg * reflection hf) z =
      z - ((g - (g x) • f) z) • (y - (f y) • x) := by
  rw [mul_assoc, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hf, hg]
  module

theorem reflection_mul_reflection_mul_self_apply' (hf : f x = 2) (hg : g y = 2) (z : M) :
    (reflection hg * reflection hf * reflection hg) z =
      z - ((f - (f y) • g) z) • (x - (g x) • y) :=
  reflection_mul_reflection_mul_self_apply hg hf z

theorem reflection_cross_eq_zero_of_commute (hfx : f x = 2) (hgy : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (h2 : (2 : K) ≠ 0)
    (hcomm : reflection hfx * reflection hgy = reflection hgy * reflection hfx) : f y = 0 := by
  have hy := congrArg (fun T : M ≃ₗ[K] M => T y) hcomm
  rw [reflection_mul_reflection_apply' hfx hgy,
    reflection_mul_reflection_apply' hgy hfx, hgy] at hy
  have key : (y - (2 : K) • y - (f y - f y * (2 : K)) • x) -
      (y - f y • x - ((2 : K) - g x * f y) • y)
      = (2 * f y) • x + (-(g x * f y)) • y := by module
  have h0 : (2 * f y) • x + (-(g x * f y)) • y = 0 := by
    rw [← key, sub_eq_zero]
    exact hy
  obtain ⟨h1, -⟩ := LinearIndependent.pair_iff.mp hxy (2 * f y) (-(g x * f y)) h0
  exact (mul_eq_zero.mp h1).resolve_left h2

theorem linearIndependent_of_commute [NeZero (2 : K)] (hfx : f x = 2) (hgy : g y = 2)
    (hne : reflection hfx ≠ reflection hgy)
    (hcomm : reflection hfx * reflection hgy = reflection hgy * reflection hfx) :
    LinearIndependent K ![x, y] ∧ LinearIndependent K ![f, g] := by
  rcases linearIndependent_and_or_exists_transvection hfx hgy with h | ⟨w, φ, hφw, hφ⟩
  · exact h
  · exfalso
    have h2 : (2 : K) ≠ 0 := NeZero.ne 2
    have hr : reflection hfx * reflection hfx = 1 := by
      have h := mul_inv_cancel (reflection hfx)
      rwa [reflection_inv hfx] at h
    have ht : reflection hgy * reflection hgy = 1 := by
      have h := mul_inv_cancel (reflection hgy)
      rwa [reflection_inv hgy] at h
    have hsq : ((reflection hfx * reflection hgy) ^ 2) = 1 := by
      rw [pow_two]
      calc (reflection hfx * reflection hgy) * (reflection hfx * reflection hgy)
          = reflection hfx * (reflection hgy * reflection hfx) * reflection hgy := by group
        _ = reflection hfx * (reflection hfx * reflection hgy) * reflection hgy := by rw [hcomm]
        _ = (reflection hfx * reflection hfx) * (reflection hgy * reflection hgy) := by group
        _ = 1 := by rw [hr, ht, one_mul]
    have hsq' : ∀ z : M, φ z • w + φ z • w = 0 := by
      intro z
      have hz := congrArg (fun T : M ≃ₗ[K] M => T z) hsq
      rw [pow_two, LinearEquiv.mul_apply, hφ, hφ] at hz
      simp only [map_add, map_smul, hφw, smul_eq_mul, mul_zero, zero_smul, add_zero,
        LinearEquiv.coe_one, id] at hz
      have h : z + 0 = z + (φ z • w + φ z • w) := by
        rw [add_zero]
        simpa [add_assoc] using hz.symm
      exact (add_left_cancel h).symm
    have hrt : reflection hfx * reflection hgy = 1 := by
      by_cases hw : w = 0
      · refine LinearEquiv.ext fun z => ?_
        rw [hφ z, hw, smul_zero, add_zero]
        rfl
      · have hφ0 : φ = 0 := by
          refine LinearMap.ext fun z => ?_
          have hsm : ((2 : K) * φ z) • w = 0 := by
            have h := hsq' z
            rw [← two_smul K (φ z • w), smul_smul] at h
            exact h
          have h2z : (2 : K) * φ z = 0 := by
            by_contra hne
            apply hw
            have h := congrArg (fun v : M => ((2 : K) * φ z)⁻¹ • v) hsm
            rw [smul_zero] at h
            rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
          rcases mul_eq_zero.mp h2z with h' | h'
          · exact absurd h' h2
          · simpa using h'
        refine LinearEquiv.ext fun z => ?_
        rw [hφ z, hφ0, LinearMap.zero_apply, zero_smul, add_zero]
        rfl
    have hfin : reflection hfx = reflection hgy := by
      have := mul_eq_one_iff_eq_inv.mp hrt
      rwa [reflection_inv hgy] at this
    exact hne hfin

theorem reflection_cross_mul_eq_one_of_braid [NeZero (2 : K)] (hfx : f x = 2) (hgy : g y = 2)
    (hxy : LinearIndependent K ![x, y])
    (h : reflection hfx * reflection hgy * reflection hfx =
      reflection hgy * reflection hfx * reflection hgy) : f y * g x = 1 := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  have hy := congrArg (fun T : M ≃ₗ[K] M => T y) h
  rw [reflection_mul_reflection_mul_self_apply hfx hgy,
    reflection_mul_reflection_mul_self_apply' hfx hgy] at hy
  have hA : (g - (g x) • f) y = 2 - (g x) * (f y) := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hgy]
  have hB : (f - (f y) • g) y = -(f y) := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hgy]
    ring
  rw [hA, hB] at hy
  have hstep : (2 - (g x) * (f y)) • (y - (f y) • x) = (-(f y)) • (x - (g x) • y) :=
    sub_right_inj.mp hy
  simp only [smul_sub, smul_smul] at hstep
  have h2' : (2 - (g x) * (f y)) • y - ((2 - (g x) * (f y)) * (f y)) • x
      - (-(f y)) • x + ((-(f y)) * (g x)) • y = 0 := by
    rw [hstep]
    abel
  have hrel : (2 - 2 * ((f y) * (g x))) • y + ((f y) ^ 2 * (g x) - (f y)) • x = 0 := by
    rw [← h2']
    module
  have hcoef := (LinearIndependent.pair_iff.mp hxy ((f y) ^ 2 * (g x) - (f y))
    (2 - 2 * ((f y) * (g x))) (by rw [add_comm]; exact hrel)).2
  rw [sub_eq_zero] at hcoef
  exact (mul_left_cancel₀ h2 (by rw [mul_one]; exact hcoef)).symm

private theorem linearIndependent_pair_swap {a b : M} (h : LinearIndependent K ![a, b]) :
    LinearIndependent K ![b, a] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h t s (by rw [add_comm]; exact hst)
  exact ⟨h2, h1⟩

theorem linearIndependent_of_braid_of_commute [NeZero (2 : K)]
    (hfx : f x = 2) (hgy : g y = 2) (hkz : k z = 2)
    (hbraid : reflection hfx * reflection hgy * reflection hfx =
      reflection hgy * reflection hfx * reflection hgy)
    (hcomm : reflection hfx * reflection hkz = reflection hkz * reflection hfx)
    (hne' : reflection hfx ≠ reflection hkz)
    (hbraid' : reflection hgy * reflection hkz * reflection hgy =
      reflection hkz * reflection hgy * reflection hkz) :
    LinearIndependent K ![x, y] ∧ LinearIndependent K ![f, g] := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  obtain ⟨hxz, -⟩ := linearIndependent_of_commute hfx hkz hne' hcomm
  have hkx : k x = 0 :=
    reflection_cross_eq_zero_of_commute hkz hfx (linearIndependent_pair_swap hxz) h2 hcomm.symm
  have hfz : f z = 0 := reflection_cross_eq_zero_of_commute hfx hkz hxz h2 hcomm
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hfx; exact h2 hfx.symm
  have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hkz; exact h2 hkz.symm
  have hf0 : f ≠ 0 := by rintro rfl; rw [LinearMap.zero_apply] at hfx; exact h2 hfx.symm
  have braidPair : ∀ (hyz : LinearIndependent K ![y, z]), g z * k y = 1 :=
    fun hyz => reflection_cross_mul_eq_one_of_braid (x := y) (y := z) (f := g) (g := k)
      hgy hkz hyz hbraid'
  constructor
  · by_contra hind
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_not_linearIndependent (a := x) (b := y) hx0 hind
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, map_zero] at hgy
      exact h2 hgy.symm
    have hyz : LinearIndependent K ![(c : K) • x, z] := by
      rw [LinearIndependent.pair_iff] at hxz ⊢
      intro s t hst
      rw [← mul_smul] at hst
      obtain ⟨h1, h2'⟩ := hxz (s * c) t hst
      exact ⟨(mul_eq_zero.mp h1).resolve_right hc0, h2'⟩
    have hky : k ((c : K) • x) ≠ 0 := by
      intro h0
      have h1 := braidPair hyz
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    rw [map_smul, hkx, smul_zero] at hky
    exact hky rfl
  · by_contra hind
    obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent (a := f) (b := g) hf0 hind
    by_cases hyz : LinearIndependent K ![y, z]
    · have hgz0 : g z = 0 := by
        simp only [hc, LinearMap.smul_apply, smul_eq_mul, hfz, mul_zero]
      have h1 := braidPair hyz
      rw [hgz0, zero_mul] at h1
      exact zero_ne_one h1
    · have hyz' : ¬ LinearIndependent K ![z, y] := fun h => hyz (linearIndependent_pair_swap h)
      obtain ⟨c', rfl⟩ := exists_eq_smul_of_not_linearIndependent (a := z) (b := y) hz0 hyz'
      have hgz : g z = 0 := by
        simp only [hc, LinearMap.smul_apply, smul_eq_mul, hfz, mul_zero]
      have hzero : g (c' • z) = 0 := by rw [map_smul, hgz, smul_zero]
      rw [hzero] at hgy
      exact h2 hgy.symm

end ReflAux

namespace TypeAReflOver

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}

private theorem val_castSucc_fin {k : Fin n} : ((k.castSucc : Fin (n + 1))).val = k.val :=
  Fin.val_castSucc k

private theorem val_succ_fin {k : Fin n} : ((k.succ : Fin (n + 1))).val = k.val + 1 :=
  Fin.val_succ k

private theorem val_last_fin : ((Fin.last n : Fin (n + 1))).val = n :=
  Fin.val_last n

private theorem val_zero_fin : ((0 : Fin (n + 1))).val = 0 :=
  Fin.val_zero (n + 1)

private theorem val_one_fin (h : 1 ≤ n) : ((1 : Fin (n + 1))).val = 1 := by
  rw [Fin.val_one' (n + 1)]
  exact Nat.mod_eq_of_lt (by omega)

@[expose] def cartanA (i j : Fin (n + 1)) : ZMod p :=
  if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

theorem cartanA_comm (i j : Fin (n + 1)) : cartanA (p := p) i j = cartanA j i := by
  have key : (i.val + 1 = j.val ∨ j.val + 1 = i.val) =
      (j.val + 1 = i.val ∨ i.val + 1 = j.val) := propext or_comm
  simp only [cartanA, key]
  by_cases h : i = j
  · subst h; rfl
  · have h' : ¬ (j = i) := fun hh => h hh.symm
    simp only [if_neg h, if_neg h']

@[expose] def cartanCol (i : Fin (n + 1)) : Fin (n + 1) → ZMod p := fun j => cartanA j i

theorem cartanA_self (i : Fin (n + 1)) : cartanA (p := p) i i = 2 := by
  simp [cartanA]

theorem cartanA_succ (i : Fin n) : cartanA (p := p) i.castSucc i.succ = -1 := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hval : (i.castSucc : Fin (n + 1)).val + 1 = (i.succ : Fin (n + 1)).val := by
    rw [val_castSucc_fin, val_succ_fin]
  simp [cartanA, hne, hval]

theorem cartanA_castSucc (i : Fin n) : cartanA (p := p) i.succ i.castSucc = -1 := by
  have hne : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ (i := i)).ne.symm
  have hval : (i.succ : Fin (n + 1)).val + 1 ≠ (i.castSucc : Fin (n + 1)).val := by
    rw [val_castSucc_fin, val_succ_fin]
    omega
  simp [cartanA, hne, hval]

theorem cartanA_of_ne {i j : Fin (n + 1)} (hij : i ≠ j)
    (hadj : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) : cartanA (p := p) i j = 0 := by
  have h1 : i.val + 1 ≠ j.val := fun h => hadj (Or.inl h)
  have h2 : j.val + 1 ≠ i.val := fun h => hadj (Or.inr h)
  simp [cartanA, hij, h1, h2]

@[expose] noncomputable def reflScale (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) : Fin (n + 1) → ZMod p :=
  Fin.induction (motive := fun _ => ZMod p) 1
    fun i prev => -(f i.succ (h i.castSucc)) * prev

theorem reflScale_zero (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V) :
    reflScale (p := p) f h 0 = 1 :=
  Fin.induction_zero ..

theorem reflScale_succ (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V)
    (i : Fin n) :
    reflScale (p := p) f h i.succ = -(f i.succ (h i.castSucc)) * reflScale f h i.castSucc :=
  Fin.induction_succ ..

theorem reflScale_ne_zero (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V)
    (hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1) :
    ∀ i, reflScale (p := p) f h i ≠ 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rw [reflScale_zero]; exact one_ne_zero
  | succ k ih =>
      rw [reflScale_succ]
      refine mul_ne_zero (neg_ne_zero.mpr ?_) ih
      intro h0
      have h1 := hcross k
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1

@[expose] noncomputable def scaledRoot (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (i : Fin (n + 1)) : V :=
  reflScale (p := p) f h i • h i

@[expose] noncomputable def scaledCoroot (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (i : Fin (n + 1)) : Module.Dual (ZMod p) V :=
  (reflScale (p := p) f h i)⁻¹ • f i

theorem scaledCoroot_scaledRoot_self (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (hf : ∀ i, f i (h i) = 2) (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (i : Fin (n + 1)) : scaledCoroot f h i (scaledRoot f h i) = 2 := by
  simp only [scaledCoroot, scaledRoot, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul]
  rw [hf i, ← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]

theorem eq_scaled_smul (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V)
    (hc : ∀ i, reflScale (p := p) f h i ≠ 0) (i : Fin (n + 1)) (v : V) :
    scaledCoroot f h i v • scaledRoot f h i = f i v • h i := by
  have hsc : (reflScale f h i)⁻¹ * (f i v) * reflScale f h i = f i v := by
    rw [mul_assoc, mul_comm (f i v) (reflScale f h i), ← mul_assoc, inv_mul_cancel₀ (hc i),
      one_mul]
  simp only [scaledCoroot, scaledRoot, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul]
  rw [hsc]

theorem eq_reflection_scaled (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V)
    (hc : ∀ i, reflScale (p := p) f h i ≠ 0) (s : Fin (n + 1) → (V ≃ₗ[ZMod p] V))
    (hrepr : ∀ i v, s i v = v - f i v • h i) (i : Fin (n + 1)) (v : V) :
    s i v = v - scaledCoroot f h i v • scaledRoot f h i := by
  rw [hrepr i v, eq_scaled_smul f h hc i v]

theorem scaledCoroot_scaledRoot_succ (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1) (i : Fin n) :
    scaledCoroot f h i.succ (scaledRoot f h i.castSucc) = -1 := by
  have hci : reflScale f h i.castSucc ≠ 0 := hc i.castSucc
  have hu : f i.succ (h i.castSucc) ≠ 0 := by
    intro h0
    have h1 := hcross i
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  simp only [scaledCoroot, scaledRoot, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul]
  rw [reflScale_succ]
  field_simp

theorem scaledCoroot_scaledRoot_castSucc (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1) (i : Fin n) :
    scaledCoroot f h i.castSucc (scaledRoot f h i.succ) = -1 := by
  have hci : reflScale f h i.castSucc ≠ 0 := hc i.castSucc
  have hu : f i.succ (h i.castSucc) ≠ 0 := by
    intro h0
    have h1 := hcross i
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have hprod : f i.succ (h i.castSucc) * f i.castSucc (h i.succ) = 1 := by
    rw [mul_comm]
    exact hcross i
  simp only [scaledCoroot, scaledRoot, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul]
  rw [reflScale_succ]
  field_simp
  rw [hprod]

theorem scaledCoroot_scaledRoot_of_far (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) {i j : Fin (n + 1)} (hzero : f j (h i) = 0) :
    scaledCoroot f h j (scaledRoot f h i) = 0 := by
  simp only [scaledCoroot, scaledRoot, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_smul,
    hzero, mul_zero]

theorem cartanA_eq_scaledCoroot (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) (hf : ∀ i, f i (h i) = 2)
    (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1)
    (hzero : ∀ i j : Fin (n + 1), i ≠ j →
      ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) → f j (h i) = 0)
    (i j : Fin (n + 1)) : cartanA (p := p) i j = scaledCoroot f h j (scaledRoot f h i) := by
  by_cases hji : j = i
  · subst hji
    rw [cartanA_self, scaledCoroot_scaledRoot_self f h hf hc]
  · by_cases h1 : i.val + 1 = j.val
    · have hi : i.val < n := by omega
      obtain ⟨k, hk⟩ : ∃ k : Fin n, k.castSucc = i ∧ k.succ = j := by
        refine ⟨⟨i.val, hi⟩, Fin.ext ?_, Fin.ext ?_⟩
        · rw [val_castSucc_fin]
        · rw [val_succ_fin]; omega
      obtain ⟨rfl, rfl⟩ := hk
      rw [cartanA_succ, scaledCoroot_scaledRoot_succ f h hc hcross]
    · by_cases h2 : j.val + 1 = i.val
      · have hj : j.val < n := by omega
        obtain ⟨k, hk⟩ : ∃ k : Fin n, k.castSucc = j ∧ k.succ = i := by
          refine ⟨⟨j.val, hj⟩, Fin.ext ?_, Fin.ext ?_⟩
          · rw [val_castSucc_fin]
          · rw [val_succ_fin]; omega
        obtain ⟨rfl, rfl⟩ := hk
        rw [cartanA_castSucc, scaledCoroot_scaledRoot_castSucc f h hc hcross]
      · have hnot : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        have hne : i ≠ j := fun h => hji h.symm
        rw [cartanA_of_ne (i := i) (j := j) hne hnot,
          scaledCoroot_scaledRoot_of_far f h (hzero i j hne hnot)]

@[expose] noncomputable def shiftFun (w : Fin (n + 1) → ZMod p) : Fin (n + 1) → ZMod p :=
  Fin.lastCases 0 fun i => w i.succ

@[expose] noncomputable def diffFun (w : Fin (n + 1) → ZMod p) : Fin (n + 1) → ZMod p :=
  w - shiftFun w

theorem shiftFun_castSucc (w : Fin (n + 1) → ZMod p) (i : Fin n) :
    shiftFun w i.castSucc = w i.succ :=
  Fin.lastCases_castSucc i

theorem shiftFun_last (w : Fin (n + 1) → ZMod p) : shiftFun w (Fin.last n) = 0 :=
  Fin.lastCases_last

theorem diffFun_castSucc (w : Fin (n + 1) → ZMod p) (i : Fin n) :
    diffFun w i.castSucc = w i.castSucc - w i.succ := by
  simp [diffFun, shiftFun_castSucc]

theorem diffFun_last (w : Fin (n + 1) → ZMod p) : diffFun w (Fin.last n) = w (Fin.last n) := by
  simp [diffFun, shiftFun_last]

theorem diffFun_add (w w' : Fin (n + 1) → ZMod p) :
    diffFun (w + w') = diffFun w + diffFun w' := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [diffFun, shiftFun, Pi.add_apply]
  · simp only [diffFun, Pi.add_apply, Pi.sub_apply, shiftFun_castSucc]
    ring

theorem diffFun_smul (c : ZMod p) (w : Fin (n + 1) → ZMod p) :
    diffFun (c • w) = c • diffFun w := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [diffFun, shiftFun, Pi.smul_apply]
  · simp only [diffFun, Pi.smul_apply, Pi.sub_apply, shiftFun_castSucc, smul_eq_mul]
    ring

@[expose] noncomputable def diff : (Fin (n + 1) → ZMod p) →ₗ[ZMod p] (Fin (n + 1) → ZMod p) where
  toFun := diffFun
  map_add' := diffFun_add
  map_smul' := diffFun_smul

theorem diff_apply (w : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) :
    diff (p := p) (n := n) w j = diffFun w j := rfl

theorem diff_eq_zero {w : Fin (n + 1) → ZMod p} (hw : ∀ j, diffFun w j = 0) : w = 0 := by
  funext j
  induction j using Fin.reverseInduction with
  | last =>
      have h := hw (Fin.last n)
      rwa [diffFun_last] at h
  | cast k ih =>
      have h := hw k.castSucc
      rw [diffFun_castSucc, sub_eq_zero] at h
      rw [h, ih]
      rfl

theorem diff_injective : Function.Injective (diff (p := p) (n := n)) := by
  intro u v huv
  have hz : diff (p := p) (n := n) (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hw : ∀ j, diffFun (u - v) j = 0 := fun j => by
    have := congrFun hz j
    simpa [diff] using this
  exact sub_eq_zero.mp (diff_eq_zero hw)

@[expose] noncomputable def diffEquiv : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p]
    (Fin (n + 1) → ZMod p) :=
  LinearEquiv.ofBijective diff
    ⟨diff_injective, Finite.injective_iff_surjective.mp diff_injective⟩

private theorem castSucc_eq_succ_of_val {k i : Fin n} (h : k.val = i.val + 1) :
    (k.castSucc : Fin (n + 1)) = i.succ :=
  Fin.ext (by rw [val_castSucc_fin, val_succ_fin, h])

theorem cartanA_castSucc_castSucc_of_val {k i : Fin n} (h : k.val = i.val + 1) :
    cartanA (p := p) k.castSucc i.castSucc = -1 := by
  have hne : (k.castSucc : Fin (n + 1)) ≠ i.castSucc := by
    intro h'
    have hh := congrArg Fin.val h'
    rw [val_castSucc_fin, val_castSucc_fin] at hh
    omega
  have h1 : ¬ ((k.castSucc : Fin (n + 1)).val + 1 = (i.castSucc : Fin (n + 1)).val) := by
    rw [val_castSucc_fin, val_castSucc_fin]; omega
  have h2 : (i.castSucc : Fin (n + 1)).val + 1 = (k.castSucc : Fin (n + 1)).val := by
    rw [val_castSucc_fin, val_castSucc_fin]; omega
  unfold cartanA
  rw [if_neg hne, if_pos (Or.inr h2)]

theorem cartanA_castSucc_castSucc_of_val' {k i : Fin n} (h : k.val + 1 = i.val) :
    cartanA (p := p) k.castSucc i.castSucc = -1 := by
  have hne : (k.castSucc : Fin (n + 1)) ≠ i.castSucc := by
    intro h'
    have hh := congrArg Fin.val h'
    rw [val_castSucc_fin, val_castSucc_fin] at hh
    omega
  have hval : (k.castSucc : Fin (n + 1)).val + 1 = (i.castSucc : Fin (n + 1)).val := by
    rw [val_castSucc_fin, val_castSucc_fin]; omega
  unfold cartanA
  rw [if_neg hne, if_pos (Or.inl hval)]

theorem diffFun_coordPerm (i : Fin n) (y : Fin (n + 1) → ZMod p) :
    diffFun (coordPerm p n (Equiv.swap i.castSucc i.succ) y) =
      diffFun y - (diffFun y i.castSucc) • cartanCol i.castSucc := by
  have hsymm : (Equiv.swap i.castSucc i.succ).symm = Equiv.swap i.castSucc i.succ :=
    Equiv.symm_swap i.castSucc i.succ
  have hfix : ∀ j : Fin (n + 1), j ≠ i.castSucc → j ≠ i.succ →
      (Equiv.swap i.castSucc i.succ) j = j := fun j h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [diffFun_last, coordPerm_apply, hsymm, Pi.sub_apply, diffFun_last, diffFun_castSucc,
      Pi.smul_apply, smul_eq_mul, cartanCol]
    by_cases hb : i.val + 1 = n
    · have hsucc : i.succ = (Fin.last n : Fin (n + 1)) :=
        Fin.ext (by rw [val_succ_fin, val_last_fin]; exact hb)
      have hCl : cartanA (p := p) (Fin.last n) i.castSucc = -1 := by
        rw [← hsucc]
        exact cartanA_castSucc i
      rw [hsucc, Equiv.swap_apply_right, hCl]
      ring
    · have hlast_ne : (Fin.last n : Fin (n + 1)) ≠ i.castSucc := by
        intro h
        have h1 := congrArg Fin.val h
        rw [val_last_fin, val_castSucc_fin] at h1
        omega
      have hlast_ne2 : (Fin.last n : Fin (n + 1)) ≠ i.succ := by
        intro h
        have h1 := congrArg Fin.val h
        rw [val_last_fin, val_succ_fin] at h1
        omega
      have hCl : cartanA (p := p) (Fin.last n) i.castSucc = 0 := by
        refine cartanA_of_ne (i := Fin.last n) (j := i.castSucc) hlast_ne ?_
        rintro (h | h)
        · rw [val_last_fin, val_castSucc_fin] at h
          omega
        · rw [val_castSucc_fin, val_last_fin] at h
          exact hb h
      rw [hfix _ hlast_ne hlast_ne2, hCl]
      ring
  · have hstep : ∀ a : Fin (n + 1),
        ((coordPerm p n (Equiv.swap i.castSucc i.succ)) y) a =
          y ((Equiv.swap i.castSucc i.succ) a) := by
      intro a
      rw [coordPerm_apply, hsymm]
    simp only [diffFun_castSucc, hstep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cartanCol]
    by_cases h1 : k = i
    · subst h1
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right, cartanA_self]
      ring
    · by_cases h2 : k.val = i.val + 1
      · have hk : (k.castSucc : Fin (n + 1)) = i.succ := castSucc_eq_succ_of_val h2
        have hk2 : (Equiv.swap i.castSucc i.succ) k.succ = k.succ := by
          refine hfix _ ?_ ?_
          · intro h
            have hh := congrArg (fun z : Fin (n + 1) => z.val) h
            simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
            omega
          · intro h
            have hh := congrArg (fun z : Fin (n + 1) => z.val) h
            simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
            omega
        rw [cartanA_castSucc_castSucc_of_val h2, hk, Equiv.swap_apply_right, hk2]
        ring
      · by_cases h3 : k.val + 1 = i.val
        · have hk : (k.succ : Fin (n + 1)) = i.castSucc := Fin.ext (by
            rw [val_succ_fin, val_castSucc_fin]; omega)
          have hk1 : (Equiv.swap i.castSucc i.succ) k.castSucc = k.castSucc := by
            refine hfix _ ?_ ?_
            · intro h
              have hh := congrArg (fun z : Fin (n + 1) => z.val) h
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
              omega
            · intro h
              have hh := congrArg (fun z : Fin (n + 1) => z.val) h
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
              omega
          rw [hk1, hk, Equiv.swap_apply_left, cartanA_castSucc_castSucc_of_val' h3]
          ring
        · have hka : (Equiv.swap i.castSucc i.succ) k.castSucc = k.castSucc := by
            refine hfix _ ?_ ?_
            · intro h
              exact h1 (Fin.castSucc_injective n h)
            · intro h
              have hh := congrArg (fun z : Fin (n + 1) => z.val) h
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
              omega
          have hkb : (Equiv.swap i.castSucc i.succ) k.succ = k.succ := by
            refine hfix _ ?_ ?_
            · intro h
              have hh := congrArg (fun z : Fin (n + 1) => z.val) h
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
              omega
            · intro h
              have hh := congrArg (fun z : Fin (n + 1) => z.val) h
              simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hh
              omega
          have hCl : cartanA (p := p) k.castSucc i.castSucc = 0 := by
            refine cartanA_of_ne (i := k.castSucc) (j := i.castSucc) ?_ ?_
            · intro h
              exact h1 (Fin.castSucc_injective n h)
            · rintro (h | h)
              · simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h
                omega
              · simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h
                omega
          rw [hka, hkb, hCl]
          ring

theorem kRoot_apply (j : Fin (n + 1)) :
    kRoot p n j = if j = Fin.last n then 2 else 1 := by
  by_cases hj : j = Fin.last n
  · subst hj
    rw [if_pos rfl]
    simp [kRoot, Pi.add_apply]
    norm_num
  · rw [if_neg hj]
    simp [kRoot, Pi.add_apply, hj, Pi.single_eq_of_ne hj]

theorem diff_kRoot : diff (p := p) (n := n) (kRoot p n) = cartanCol (Fin.last n) := by
  funext j
  rw [diff_apply, cartanCol]
  refine Fin.lastCases ?_ ?_ j
  · rw [diffFun_last, kRoot_apply, if_pos rfl, cartanA_self]
  · intro k
    rw [diffFun_castSucc]
    by_cases hk : k.succ = Fin.last n
    · have hk' : (k.castSucc : Fin (n + 1)) ≠ Fin.last n := by
        intro h
        have := congrArg Fin.val h
        simp only [val_castSucc_fin, val_last_fin] at this
        omega
      rw [kRoot_apply, kRoot_apply, if_neg hk', if_pos hk]
      have hC : cartanA (p := p) k.castSucc (Fin.last n) = -1 := by
        rw [← hk]
        exact cartanA_succ k
      rw [hC]
      ring
    · have hk' : (k.castSucc : Fin (n + 1)) ≠ Fin.last n := by
        intro h
        have := congrArg Fin.val h
        simp only [val_castSucc_fin, val_last_fin] at this
        omega
      rw [kRoot_apply, kRoot_apply, if_neg hk', if_neg hk]
      have hC : cartanA (p := p) k.castSucc (Fin.last n) = 0 := by
        refine cartanA_of_ne (i := k.castSucc) (j := Fin.last n) hk' ?_
        rintro (h | h)
        · exact hk (Fin.ext (by rw [val_succ_fin, val_last_fin]; simpa using h))
        · rw [val_last_fin, val_castSucc_fin] at h
          omega
      rw [hC]
      ring

theorem diffFun_kRefl (y : Fin (n + 1) → ZMod p) :
    diffFun (kRefl p n y) = diffFun y - (diffFun y (Fin.last n)) • cartanCol (Fin.last n) := by
  have h : diff (p := p) (n := n) (kRefl p n y) =
      diff y - (diff y (Fin.last n)) • cartanCol (Fin.last n) := by
    rw [kRefl_apply, map_sub, map_smul, diff_kRoot, diff_apply, diffFun_last]
  funext j
  have := congrFun h j
  simpa [diff_apply] using this

section Eval

variable {s : Fin (n + 1) → (V ≃ₗ[ZMod p] V)} {h : Fin (n + 1) → V}
  {f : Fin (n + 1) → Module.Dual (ZMod p) V}

theorem scaledCoroot_eq_zero_of_fixed (hp2 : p ≠ 2) (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hrepr : ∀ i v, s i v = v - f i v • h i) (hf : ∀ i, f i (h i) = 2) {i : Fin (n + 1)}
    {v : V} (hv : s i v = v) : scaledCoroot f h i v = 0 := by
  have h2 := eq_reflection_scaled f h hc s hrepr i v
  have h4 : v - scaledCoroot f h i v • scaledRoot f h i = v := by rw [← h2]; exact hv
  have h3 : scaledCoroot f h i v • scaledRoot f h i = 0 := sub_eq_self.mp h4
  have h5 : f i (scaledCoroot f h i v • scaledRoot f h i) = 0 := by rw [h3, map_zero]
  rw [map_smul, smul_eq_mul] at h5
  have h6 : f i (scaledRoot f h i) ≠ 0 := by
    rw [scaledRoot, map_smul, smul_eq_mul, hf i]
    exact mul_ne_zero (hc i) (zmod_two_ne_zero hp2)
  exact (mul_eq_zero.mp h5).resolve_right h6

theorem scaledCoroot_ne_zero_of_ne_fixed (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hrepr : ∀ i v, s i v = v - f i v • h i) {i : Fin (n + 1)} {v : V} (hv : s i v ≠ v) :
    scaledCoroot f h i v ≠ 0 := by
  intro h0
  apply hv
  rw [eq_reflection_scaled f h hc s hrepr i v, h0, zero_smul, sub_zero]

@[expose] noncomputable def evalMap (f : Fin (n + 1) → Module.Dual (ZMod p) V)
    (h : Fin (n + 1) → V) : V →ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
  LinearMap.pi fun i => scaledCoroot f h i

theorem evalMap_apply (f : Fin (n + 1) → Module.Dual (ZMod p) V) (h : Fin (n + 1) → V)
    (v : V) (i : Fin (n + 1)) : evalMap f h v i = scaledCoroot f h i v :=
  LinearMap.pi_apply _ _ _

theorem evalMap_injective (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hrepr : ∀ i v, s i v = v - f i v • h i)
    (hfix : ∀ v : V, (∀ i, s i v = v) → v = 0) : Function.Injective (evalMap f h) := by
  intro u v huv
  have hz : evalMap f h (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h0 : ∀ i, scaledCoroot f h i (u - v) = 0 := fun i => by
    have := congrFun hz i
    simpa [evalMap_apply] using this
  have hfix0 : ∀ i, s i (u - v) = u - v := by
    intro i
    rw [eq_reflection_scaled f h hc s hrepr i (u - v), h0 i, zero_smul, sub_zero]
  exact sub_eq_zero.mp (hfix (u - v) hfix0)

theorem evalMap_intertwine (hc : ∀ i, reflScale (p := p) f h i ≠ 0)
    (hrepr : ∀ i v, s i v = v - f i v • h i)
    (hcol : ∀ i j, cartanA (p := p) i j = scaledCoroot f h j (scaledRoot f h i))
    (i : Fin (n + 1)) (v : V) :
    evalMap f h (s i v) = evalMap f h v - (evalMap f h v i) • cartanCol i := by
  funext j
  rw [evalMap_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cartanCol, cartanA_comm,
    eq_reflection_scaled f h hc s hrepr i v, map_sub, map_smul, smul_eq_mul, ← hcol i j,
    evalMap_apply, evalMap_apply]

theorem coordPerm_single (σ : Equiv.Perm (Fin (n + 1))) (a : Fin (n + 1)) (c : ZMod p) :
    coordPerm p n σ (Pi.single a c) = Pi.single (σ a) c := by
  funext j
  rw [coordPerm_apply]
  by_cases hj : j = σ a
  · subst hj
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · have hj' : σ.symm j ≠ a := by
      intro hh
      apply hj
      rw [← hh, Equiv.apply_symm_apply]
    rw [Pi.single_eq_of_ne hj', Pi.single_eq_of_ne hj]

theorem diffFun_one : diffFun (p := p) (n := n) (fun _ => (1 : ZMod p)) =
    Pi.single (Fin.last n) 1 := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [diffFun_last, Pi.single_eq_same]
  · rw [diffFun_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last k)]
    ring

theorem kRefl_one : kRefl p n (fun _ => (1 : ZMod p)) = -(Pi.single (Fin.last n) 1) := by
  rw [kRefl_apply]
  funext j
  rw [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
  by_cases hj : j = Fin.last n
  · subst hj
    rw [kRoot_apply, if_pos rfl, Pi.single_eq_same]
    norm_num
  · rw [kRoot_apply, if_neg hj, Pi.single_eq_of_ne hj]
    ring

end Eval

private theorem pi_single_neg (a : Fin (n + 1)) (c : ZMod p) :
    Pi.single a (-c) = -(c • Pi.single a (1 : ZMod p)) := by
  funext j
  rw [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = a
  · subst hj
    rw [Pi.single_eq_same, Pi.single_eq_same]
    ring
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero, neg_zero]

theorem exists_linearEquiv_of_typeA_refl {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] {n : ℕ} (hn : 2 ≤ n)
    (s : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (hrefl : ∀ i, IsLinRefl (s i))
    (hdistinct : ∀ i j, i ≠ j → s i ≠ s j)
    (hcomm : ∀ i j : Fin (n + 1), i.val + 2 ≤ j.val → s i * s j = s j * s i)
    (hbraid : ∀ i j : Fin (n + 1), i.val + 1 = j.val → s i * s j * s i = s j * s i * s j)
    (hfix : ∀ v : V, (∀ i, s i v = v) → v = 0)
    (x : V) (hx : ∀ i : Fin (n + 1), i ≠ Fin.last n → s i x = x)
    (hxn : s (Fin.last n) x ≠ x) :
    ∃ κ : V ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p),
      (∀ i : Fin n, ⇑κ ∘ ⇑(s i.castSucc) =
        ⇑(coordPerm p n (Equiv.swap i.castSucc i.succ)) ∘ ⇑κ) ∧
      ⇑κ ∘ ⇑(s (Fin.last n)) = ⇑(kRefl p n) ∘ ⇑κ ∧
      κ x ∈ Submodule.span (ZMod p) {1} := by
  classical
  haveI : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp2⟩
  choose h f hf hrepr using hrefl
  have hrepr' : ∀ i, s i = reflection (hf i) := fun i => LinearEquiv.ext fun v => by
    rw [hrepr i v, reflection_apply]
  have hne2 : ∀ i j : Fin (n + 1), i ≠ j → reflection (hf i) ≠ reflection (hf j) := by
    intro i j hij h'
    exact hdistinct i j hij (by rw [hrepr' i, hrepr' j, h'])
  have hcomm2 : ∀ i j : Fin (n + 1), i.val + 2 ≤ j.val →
      reflection (hf i) * reflection (hf j) = reflection (hf j) * reflection (hf i) := by
    intro i j hij
    rw [← hrepr' i, ← hrepr' j]
    exact hcomm i j hij
  have hbraid2 : ∀ i j : Fin (n + 1), i.val + 1 = j.val →
      reflection (hf i) * reflection (hf j) * reflection (hf i) =
        reflection (hf j) * reflection (hf i) * reflection (hf j) := by
    intro i j hij
    rw [← hrepr' i, ← hrepr' j]
    exact hbraid i j hij
  have hzero : ∀ i j : Fin (n + 1), i ≠ j →
      ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) → f j (h i) = 0 := by
    intro i j hij hfar
    have hfar2 : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by
      have hval : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
      omega
    rcases hfar2 with hcell | hcell
    · have hc := hcomm2 i j hcell
      have hind := linearIndependent_of_commute (hf i) (hf j) (hne2 i j hij) hc
      exact reflection_cross_eq_zero_of_commute (hf j) (hf i) (linearIndependent_pair_swap hind.1)
        (NeZero.ne 2) hc.symm
    · have hc := hcomm2 j i hcell
      have hind := linearIndependent_of_commute (hf j) (hf i) (hne2 j i hij.symm) hc
      exact reflection_cross_eq_zero_of_commute (hf j) (hf i) hind.1 (NeZero.ne 2) hc
  have hcross : ∀ i : Fin n, f i.castSucc (h i.succ) * f i.succ (h i.castSucc) = 1 := by
    intro i
    have hbraid_rt := hbraid2 i.castSucc i.succ (by rw [val_castSucc_fin, val_succ_fin])
    by_cases hright : i.val + 2 ≤ n
    · set k : Fin (n + 1) := ⟨i.val + 2, by omega⟩ with hk
      have hkv : k.val = i.val + 2 := rfl
      have hcomm_rk : reflection (hf i.castSucc) * reflection (hf k) =
          reflection (hf k) * reflection (hf i.castSucc) := by
        refine hcomm2 i.castSucc k ?_
        rw [hkv, val_castSucc_fin]
      have hne_rk : reflection (hf i.castSucc) ≠ reflection (hf k) := by
        refine hne2 i.castSucc k ?_
        intro hh
        have := congrArg Fin.val hh
        rw [hkv, val_castSucc_fin] at this
        omega
      have hbraid_tk : reflection (hf i.succ) * reflection (hf k) * reflection (hf i.succ) =
          reflection (hf k) * reflection (hf i.succ) * reflection (hf k) := by
        refine hbraid2 i.succ k ?_
        rw [hkv, val_succ_fin]
      have hind := linearIndependent_of_braid_of_commute (hf i.castSucc) (hf i.succ) (hf k)
        hbraid_rt hcomm_rk hne_rk hbraid_tk
      exact reflection_cross_mul_eq_one_of_braid (hf i.castSucc) (hf i.succ) hind.1 hbraid_rt
    · have hleft : i.val = n - 1 := by
        have := i.isLt
        omega
      set k : Fin (n + 1) := ⟨i.val - 1, by omega⟩ with hk
      have hkv : k.val = i.val - 1 := rfl
      have hcomm_rk : reflection (hf i.succ) * reflection (hf k) =
          reflection (hf k) * reflection (hf i.succ) := by
        refine (hcomm2 k i.succ ?_).symm
        rw [hkv, val_succ_fin]
        omega
      have hne_rk : reflection (hf i.succ) ≠ reflection (hf k) := by
        refine hne2 i.succ k ?_
        intro hh
        have := congrArg Fin.val hh
        rw [hkv, val_succ_fin] at this
        omega
      have hbraid_tk : reflection (hf i.castSucc) * reflection (hf k) *
          reflection (hf i.castSucc) =
          reflection (hf k) * reflection (hf i.castSucc) * reflection (hf k) := by
        refine (hbraid2 k i.castSucc ?_).symm
        rw [hkv, val_castSucc_fin]
        omega
      have hind := linearIndependent_of_braid_of_commute (hf i.succ) (hf i.castSucc) (hf k)
        hbraid_rt.symm hcomm_rk hne_rk hbraid_tk
      have hprod := reflection_cross_mul_eq_one_of_braid (hf i.succ) (hf i.castSucc) hind.1
        hbraid_rt.symm
      rwa [mul_comm]
  have hc : ∀ i, reflScale (p := p) f h i ≠ 0 := reflScale_ne_zero f h hcross
  have hcol : ∀ i j : Fin (n + 1),
      cartanA (p := p) i j = scaledCoroot f h j (scaledRoot f h i) :=
    cartanA_eq_scaledCoroot f h hf hc hcross hzero
  let M : V →ₗ[ZMod p] (Fin (n + 1) → ZMod p) := evalMap f h
  have hM_apply : ∀ (v : V) (i : Fin (n + 1)), M v i = scaledCoroot f h i v :=
    fun v i => evalMap_apply f h v i
  have hM_inj : Function.Injective M := evalMap_injective hc hrepr hfix
  have hM_int : ∀ (i : Fin (n + 1)) (v : V),
      M (s i v) = M v - (M v i) • cartanCol i :=
    fun i v => evalMap_intertwine hc hrepr hcol i v
  let D : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) := diffEquiv
  let kap : V →ₗ[ZMod p] (Fin (n + 1) → ZMod p) := D.symm.toLinearMap.comp M
  have hD_apply : ∀ w, D w = diffFun w := fun w => rfl
  have hkap_apply : ∀ v, kap v = D.symm (M v) := fun v => rfl
  have hdiff_symm : ∀ y, diffFun (D.symm y) = y := by
    intro y
    rw [← hD_apply]
    exact D.apply_symm_apply y
  have hkap_castSucc : ∀ (i : Fin n) (v : V),
      kap (s i.castSucc v) = coordPerm p n (Equiv.swap i.castSucc i.succ) (kap v) := by
    intro i v
    refine D.injective ?_
    have h1 : D (kap (s i.castSucc v)) = M (s i.castSucc v) := by
      rw [hkap_apply]
      exact D.apply_symm_apply _
    have h2 : D (coordPerm p n (Equiv.swap i.castSucc i.succ) (kap v)) = M (s i.castSucc v) := by
      rw [hD_apply, hkap_apply, diffFun_coordPerm, hdiff_symm, hM_int]
    exact h1.trans h2.symm
  have hkap_last : ∀ v : V, kap (s (Fin.last n) v) = kRefl p n (kap v) := by
    intro v
    refine D.injective ?_
    have h1 : D (kap (s (Fin.last n) v)) = M (s (Fin.last n) v) := by
      rw [hkap_apply]
      exact D.apply_symm_apply _
    have h2 : D (kRefl p n (kap v)) = M (s (Fin.last n) v) := by
      rw [hD_apply, hkap_apply, diffFun_kRefl, hdiff_symm, hM_int]
    exact h1.trans h2.symm
  have hcne : scaledCoroot f h (Fin.last n) x ≠ 0 :=
    scaledCoroot_ne_zero_of_ne_fixed hc hrepr hxn
  have hMx : M x = scaledCoroot f h (Fin.last n) x • Pi.single (Fin.last n) 1 := by
    funext i
    rw [hM_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = Fin.last n
    · rw [hi, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hi, mul_zero]
      exact scaledCoroot_eq_zero_of_fixed hp2 hc hrepr hf (hx i hi)
  have hkappx : kap x = scaledCoroot f h (Fin.last n) x • (fun _ => (1 : ZMod p)) := by
    refine D.injective ?_
    have h1 : D (kap x) = M x := by
      rw [hkap_apply]
      exact D.apply_symm_apply _
    have h2 : D (scaledCoroot f h (Fin.last n) x • (fun _ => (1 : ZMod p))) = M x := by
      rw [hD_apply, diffFun_smul, diffFun_one, hMx]
    exact h1.trans h2.symm
  have hsingle : ∀ k : Fin (n + 1),
      Pi.single k (-(scaledCoroot f h (Fin.last n) x)) ∈ LinearMap.range kap := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
        refine ⟨s (Fin.last n) x, ?_⟩
        rw [hkap_last, hkappx, map_smul, kRefl_one, pi_single_neg, smul_neg]
    | cast m ih =>
        obtain ⟨v, hv⟩ := ih
        refine ⟨s m.castSucc v, ?_⟩
        rw [hkap_castSucc, hv, coordPerm_single, Equiv.swap_apply_right]
  have hsurj : Function.Surjective kap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun (ZMod p) (Fin (n + 1))).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    have h1 := hsingle k
    have h2 : (-(scaledCoroot f h (Fin.last n) x))⁻¹ •
        Pi.single k (-(scaledCoroot f h (Fin.last n) x)) = Pi.single k (1 : ZMod p) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases hj : j = k
      · subst hj
        rw [Pi.single_eq_same, Pi.single_eq_same, inv_mul_cancel₀ (neg_ne_zero.mpr hcne)]
      · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero]
    rw [← h2]
    exact Submodule.smul_mem _ _ h1
  have hkap_inj : Function.Injective kap := by
    intro a b hab
    refine hM_inj ?_
    have ha : D (kap a) = M a := by rw [hkap_apply]; exact D.apply_symm_apply _
    have hb : D (kap b) = M b := by rw [hkap_apply]; exact D.apply_symm_apply _
    rw [← ha, ← hb, hab]
  let κ : V ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
    LinearEquiv.ofBijective kap ⟨hkap_inj, hsurj⟩
  have hκ : ∀ v, κ v = kap v := fun v => rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro i
    funext v
    simpa only [Function.comp_apply, hκ] using hkap_castSucc i v
  · funext v
    simpa only [Function.comp_apply, hκ] using hkap_last v
  · rw [hκ, hkappx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

end TypeAReflOver

section Boundary

theorem isLinRefl_ggLin {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V)
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) : IsLinRefl (ggLin (p := p) ι φ) := by
  obtain ⟨x, f, hfx, hrepr⟩ := exists_of_ggIsReflection (p := p) ι h
  rw [ggLin_eq_reflection ι hfx hrepr]
  exact ⟨x, f, hfx, fun v => reflection_apply v hfx⟩

private theorem swap_commute_of_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b :=
  CFSG.Permutation.SymmetricCoxeter.swap_mul_swap_comm hac had hbc hbd

private theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
  CFSG.Permutation.SymmetricCoxeter.swap_braid hab hac hbc

end Boundary

section Centralizer

theorem GGFarCtx.commute_of_permAut₁_fixed {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ}
    {F : Type} [Field F] {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {b : G} (hb : b ∈ Bs)
    (hfix : ∀ π, hC.permAut₁ π ⟨b, hb⟩ = ⟨b, hb⟩) : ∀ s, b * φ₁ s = φ₁ s * b := by
  obtain ⟨h, hv⟩ := hC.lifts.diag₁ b hb
  have hv' : GGActsVec φ₁ b h := hv
  have key : ∀ π : Equiv.Perm (Fin (n + 1)), GGVecEq h (h ∘ π.symm) := by
    intro π
    have hcomm : φ₁ (slPerm hC.two π) * b * (φ₁ (slPerm hC.two π))⁻¹ = b := by
      have := congrArg Subtype.val (hfix π)
      rw [GGFarCtx.permAut₁_apply] at this
      exact this
    have h2 := GGActsVec.conj_perm hC.two hv' π
    rw [hcomm] at h2
    exact GGActsVec.vecEq hC.lifts.ker₁ hv' h2
  have hconst : GGVecEq h 1 := by
    rw [ggVecEq_one_iff]
    intro k l
    by_cases hkl : k = l
    · rw [hkl]
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp (key (Equiv.swap k l))
    have hs : ({k, l} : Finset (Fin (n + 1))).card <
        (Finset.univ : Finset (Fin (n + 1))).card := by
      have hle : ({k, l} : Finset (Fin (n + 1))).card ≤ 2 := by
        have h' := Finset.card_insert_le k ({l} : Finset (Fin (n + 1)))
        simpa using h'
      have := hC.three_le
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hci : h i = c * h i := by
      have := hc i
      simpa [Function.comp, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2] using this
    have hc1 : c = 1 := by
      have : c * h i = 1 * h i := by rw [one_mul, ← hci]
      exact mul_right_cancel this
    have hk := hc k
    simpa [Function.comp, hc1] using hk
  intro s
  exact hv'.commute_of_vecEq_one hconst s

theorem GGFarCtx.commute_of_permAut₂_fixed {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ}
    {F : Type} [Field F] {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {b : G} (hb : b ∈ Bs)
    (hfix : ∀ π, hC.permAut₂ π ⟨b, hb⟩ = ⟨b, hb⟩) : ∀ s, b * φ₂ s = φ₂ s * b := by
  obtain ⟨h, hv⟩ := hC.lifts.diag₂ b hb
  have hv' : GGActsVec φ₂ b h := hv
  have key : ∀ π : Equiv.Perm (Fin (n + 1)), GGVecEq h (h ∘ π.symm) := by
    intro π
    have hcomm : φ₂ (slPerm hC.two π) * b * (φ₂ (slPerm hC.two π))⁻¹ = b := by
      have := congrArg Subtype.val (hfix π)
      rw [GGFarCtx.permAut₂_apply] at this
      exact this
    have h2 := GGActsVec.conj_perm hC.two hv' π
    rw [hcomm] at h2
    exact GGActsVec.vecEq hC.lifts.ker₂ hv' h2
  have hconst : GGVecEq h 1 := by
    rw [ggVecEq_one_iff]
    intro k l
    by_cases hkl : k = l
    · rw [hkl]
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp (key (Equiv.swap k l))
    have hs : ({k, l} : Finset (Fin (n + 1))).card <
        (Finset.univ : Finset (Fin (n + 1))).card := by
      have hle : ({k, l} : Finset (Fin (n + 1))).card ≤ 2 := by
        have h' := Finset.card_insert_le k ({l} : Finset (Fin (n + 1)))
        simpa using h'
      have := hC.three_le
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hci : h i = c * h i := by
      have := hc i
      simpa [Function.comp, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2] using this
    have hc1 : c = 1 := by
      have : c * h i = 1 * h i := by rw [one_mul, ← hci]
      exact mul_right_cancel this
    have hk := hc k
    simpa [Function.comp, hc1] using hk
  intro s
  exact hv'.commute_of_vecEq_one hconst s

end Centralizer

section Fixed

theorem permAut_fixed_of_swaps {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}
    {P : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs} {b : ↥Bs}
    (h : ∀ k : Fin n, P (Equiv.swap k.castSucc k.succ) b = b) : ∀ π, P π b = b := by
  have htop : Subgroup.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  intro π
  have hmem : π ∈ Subgroup.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) := by
    rw [htop]
    exact Subgroup.mem_top π
  let H : Subgroup (Equiv.Perm (Fin (n + 1))) :=
    { carrier := {σ | P σ b = b}
      one_mem' := by show P 1 b = b; rw [map_one]; rfl
      mul_mem' := fun {x y} hx hy => by
        show P (x * y) b = b
        rw [map_mul, MulAut.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        show P x⁻¹ b = b
        rw [map_inv]
        have h2 : ((P x)⁻¹ : MulAut ↥Bs) ((P x) b) = b := by simp
        rwa [hx] at h2 }
  have hH : Subgroup.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) ≤ H := by
    rw [Subgroup.closure_le]
    rintro σ ⟨k, rfl⟩
    exact h k
  exact hH hmem

end Fixed

section Far

open CFSG.Assembly TypeAReflOver

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  [Finite F] {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.exists_coordEquiv (hC : GGFarCtx p Bs φ₁ φ₂ x y) (hBs : IsElemAbelian p Bs)
    (j : Fin n) (hj : j.val + 1 = n)
    (hfar : hC.permAut₁ (Equiv.swap 0 1) * hC.permAut₂ (Equiv.swap j.castSucc j.succ) =
      hC.permAut₂ (Equiv.swap j.castSucc j.succ) * hC.permAut₁ (Equiv.swap 0 1)) :
    ∃ κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p),
      (∀ σ b, κ (Additive.ofMul (hC.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b))) ∧
      (∀ b, κ (Additive.ofMul (hC.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
        kRefl p n (κ (Additive.ofMul b))) ∧
      κ (Additive.ofMul ⟨x, hC.x_mem⟩) ∈ Submodule.span (ZMod p) {1} := by
  classical
  haveI : Fact p.Prime := ⟨hC.prime⟩
  have hn3 : 3 ≤ n := hC.three_le
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Fintype V := Fintype.ofEquiv (Additive ↥Bs) ι.toEquiv
  let slast : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ))
  let s : Fin (n + 1) → (V ≃ₗ[ZMod p] V) :=
    Fin.lastCases slast (fun k => ggLin (p := p) ι (hC.permAut₁ (Equiv.swap k.castSucc k.succ)))
  have hs_last : s (Fin.last n) = slast := Fin.lastCases_last
  have hs_cast : ∀ k : Fin n, s k.castSucc =
      ggLin (p := p) ι (hC.permAut₁ (Equiv.swap k.castSucc k.succ)) := fun k =>
    Fin.lastCases_castSucc k
  have hrefl : ∀ i, IsLinRefl (s i) := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [hs_last]
      exact isLinRefl_ggLin ι (hC.permAut₂_swap_isReflection (Fin.castSucc_lt_succ (i := j)).ne)
    · rw [hs_cast]
      exact isLinRefl_ggLin ι (hC.permAut₁_swap_isReflection (Fin.castSucc_lt_succ (i := k)).ne)
  have hxvec : ι (Additive.ofMul ⟨x, hC.x_mem⟩) = ι (Additive.ofMul ⟨x, hC.x_mem⟩) := rfl
  have hs_fix (k : Fin n) : s k.castSucc (ι (Additive.ofMul ⟨x, hC.x_mem⟩)) =
      ι (Additive.ofMul ⟨x, hC.x_mem⟩) := by
    rw [hs_cast, ggLin_apply_ofMul, hC.permAut₁_fix_x]
  have hs_last_ne : s (Fin.last n) (ι (Additive.ofMul ⟨x, hC.x_mem⟩)) ≠
      ι (Additive.ofMul ⟨x, hC.x_mem⟩) := by
    rw [hs_last, ggLin_apply_ofMul]
    intro h
    exact hC.permAut₂_swap_ne_x hj (Additive.ofMul.injective (ι.injective h))
  have hdistinct : ∀ i i' : Fin (n + 1), i ≠ i' → s i ≠ s i' := by
    intro i i' hii' hEq
    revert hii' hEq
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) i'
      · intro hii' _
        exact hii' rfl
      · intro hii' hEq
        exact hs_last_ne (by rw [hEq]; exact hs_fix b)
    · refine Fin.lastCases ?_ (fun b => ?_) i'
      · intro hii' hEq
        exact hs_last_ne (by rw [← hEq]; exact hs_fix a)
      · intro hii' hEq
        have h2 : hC.permAut₁ (Equiv.swap a.castSucc a.succ) =
            hC.permAut₁ (Equiv.swap b.castSucc b.succ) := by
          apply ggLin_injective (p := p) ι
          rw [← hs_cast a, ← hs_cast b]
          exact hEq
        have h4 : Equiv.swap a.castSucc a.succ = Equiv.swap b.castSucc b.succ :=
          hC.permAut₁_injective h2
        by_cases hab : a = b
        · exact hii' (by rw [hab])
        · exfalso
          have h5 : (Equiv.swap a.castSucc a.succ) a.castSucc =
              (Equiv.swap b.castSucc b.succ) a.castSucc := by rw [h4]
          rw [Equiv.swap_apply_left] at h5
          have h6 : (a.castSucc : Fin (n + 1)) ≠ b.castSucc := fun h =>
            hab (Fin.castSucc_injective n h)
          by_cases h7 : (a.castSucc : Fin (n + 1)) = b.succ
          · rw [h7, Equiv.swap_apply_right] at h5
            have h8 := congrArg Fin.val h5
            rw [val_succ_fin, val_castSucc_fin] at h8
            have h9 := congrArg Fin.val h7
            rw [val_castSucc_fin, val_succ_fin] at h9
            omega
          · rw [Equiv.swap_apply_of_ne_of_ne h6 h7] at h5
            have h8 := congrArg Fin.val h5
            rw [val_succ_fin, val_castSucc_fin] at h8
            omega
  have hcomm_s : ∀ i i' : Fin (n + 1), i.val + 2 ≤ i'.val → s i * s i' = s i' * s i := by
    intro i i'
    induction i using Fin.lastCases with
    | last =>
        intro hii'
        exfalso
        rw [val_last_fin] at hii'
        have h2 : i'.val ≤ n := by have := i'.isLt; omega
        omega
    | cast a =>
        induction i' using Fin.lastCases with
        | last =>
            intro hii'
            by_cases ha : a.val = 0
            · have hi0 : a.castSucc = (0 : Fin (n + 1)) :=
                Fin.ext (by rw [val_castSucc_fin, val_zero_fin]; exact ha)
              have hi1 : a.succ = (1 : Fin (n + 1)) :=
                Fin.ext (by rw [val_succ_fin, val_one_fin (by omega)]; omega)
              have hswap : Equiv.swap a.castSucc a.succ = Equiv.swap (0 : Fin (n + 1)) 1 := by
                rw [hi0, hi1]
              calc s a.castSucc * s (Fin.last n)
                  = ggLin (p := p) ι (hC.permAut₁ (Equiv.swap (0 : Fin (n + 1)) 1)) *
                      ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ)) := by
                    rw [hs_cast, hs_last, hswap]
                _ = ggLin (p := p) ι (hC.permAut₁ (Equiv.swap (0 : Fin (n + 1)) 1) *
                      hC.permAut₂ (Equiv.swap j.castSucc j.succ)) := by rw [map_mul]
                _ = ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ) *
                      hC.permAut₁ (Equiv.swap (0 : Fin (n + 1)) 1)) := by rw [hfar]
                _ = s (Fin.last n) * s a.castSucc := by rw [map_mul, hs_cast, hs_last, hswap]
            · have ha1 : 1 ≤ a.val := by omega
              have hale : a.val ≤ n - 2 := by
                rw [val_castSucc_fin, val_last_fin] at hii'
                omega
              set a' : Fin n := ⟨a.val - 1, by omega⟩ with ha'
              have ha'v : a'.val = a.val - 1 := rfl
              have ha'succ : a'.succ = a.castSucc :=
                Fin.ext (by rw [val_succ_fin, val_castSucc_fin]; simp only [ha'v]; omega)
              have hcompat : hC.permAut₁ (Equiv.swap a.castSucc a.succ) =
                  hC.permAut₂ (Equiv.swap a'.castSucc a.castSucc) := by
                rw [show Equiv.swap a.castSucc a.succ = Equiv.swap a'.succ a.succ from by
                  rw [ha'succ]]
                exact hC.permAut_compat a' a
              have hne1 : a'.castSucc ≠ (a.castSucc : Fin (n + 1)) := by
                intro h
                have hh := congrArg Fin.val h
                rw [val_castSucc_fin, val_castSucc_fin] at hh
                simp only [ha'v] at hh
                omega
              have hne2 : j.castSucc ≠ (j.succ : Fin (n + 1)) :=
                (Fin.castSucc_lt_succ (i := j)).ne
              have hne3 : a'.castSucc ≠ (j.castSucc : Fin (n + 1)) := by
                intro h
                have hh := congrArg Fin.val h
                rw [val_castSucc_fin, val_castSucc_fin] at hh
                simp only [ha'v] at hh
                omega
              have hne4 : a'.castSucc ≠ (j.succ : Fin (n + 1)) := by
                intro h
                have hh := congrArg Fin.val h
                rw [val_castSucc_fin, val_succ_fin] at hh
                simp only [ha'v] at hh
                omega
              have hne5 : a.castSucc ≠ (j.castSucc : Fin (n + 1)) := by
                intro h
                have hh := congrArg Fin.val h
                rw [val_castSucc_fin, val_castSucc_fin] at hh
                omega
              have hne6 : a.castSucc ≠ (j.succ : Fin (n + 1)) := by
                intro h
                have hh := congrArg Fin.val h
                rw [val_castSucc_fin, val_succ_fin] at hh
                omega
              have hswapc : Equiv.swap a'.castSucc a.castSucc * Equiv.swap j.castSucc j.succ =
                  Equiv.swap j.castSucc j.succ * Equiv.swap a'.castSucc a.castSucc :=
                swap_commute_of_ne hne3 hne4 hne5 hne6
              calc s a.castSucc * s (Fin.last n)
                  = ggLin (p := p) ι (hC.permAut₂ (Equiv.swap a'.castSucc a.castSucc)) *
                      ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ)) := by
                    rw [hs_cast, hs_last, hcompat]
                _ = ggLin (p := p) ι (hC.permAut₂ (Equiv.swap a'.castSucc a.castSucc) *
                      hC.permAut₂ (Equiv.swap j.castSucc j.succ)) := by rw [map_mul]
                _ = ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ) *
                      hC.permAut₂ (Equiv.swap a'.castSucc a.castSucc)) := by
                  rw [← map_mul, ← map_mul, hswapc, map_mul, map_mul]
                _ = s (Fin.last n) * s a.castSucc := by rw [map_mul, hs_cast, hs_last, hcompat]
        | cast c =>
            intro hii'
            rw [val_castSucc_fin, val_castSucc_fin] at hii'
            have hne1 : a.castSucc ≠ (a.succ : Fin (n + 1)) :=
              (Fin.castSucc_lt_succ (i := a)).ne
            have hne2 : c.castSucc ≠ (c.succ : Fin (n + 1)) :=
              (Fin.castSucc_lt_succ (i := c)).ne
            have hne3 : a.castSucc ≠ (c.castSucc : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_castSucc_fin, val_castSucc_fin] at hh
              omega
            have hne4 : a.castSucc ≠ (c.succ : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_castSucc_fin, val_succ_fin] at hh
              omega
            have hne5 : a.succ ≠ (c.castSucc : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_succ_fin, val_castSucc_fin] at hh
              omega
            have hne6 : a.succ ≠ (c.succ : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_succ_fin, val_succ_fin] at hh
              omega
            have hswapc : Equiv.swap a.castSucc a.succ * Equiv.swap c.castSucc c.succ =
                Equiv.swap c.castSucc c.succ * Equiv.swap a.castSucc a.succ :=
              swap_commute_of_ne hne3 hne4 hne5 hne6
            calc s a.castSucc * s c.castSucc
                = ggLin (p := p) ι (hC.permAut₁ (Equiv.swap a.castSucc a.succ)) *
                    ggLin (p := p) ι (hC.permAut₁ (Equiv.swap c.castSucc c.succ)) := by
                  rw [hs_cast, hs_cast]
              _ = ggLin (p := p) ι (hC.permAut₁ (Equiv.swap a.castSucc a.succ) *
                    hC.permAut₁ (Equiv.swap c.castSucc c.succ)) := by rw [map_mul]
              _ = ggLin (p := p) ι (hC.permAut₁ (Equiv.swap c.castSucc c.succ) *
                    hC.permAut₁ (Equiv.swap a.castSucc a.succ)) := by
                rw [← map_mul, ← map_mul, hswapc, map_mul, map_mul]
              _ = s c.castSucc * s a.castSucc := by rw [map_mul, hs_cast, hs_cast]

  have hbraid_s : ∀ i i' : Fin (n + 1), i.val + 1 = i'.val →
      s i * s i' * s i = s i' * s i * s i' := by
    intro i i'
    induction i using Fin.lastCases with
    | last =>
        intro hii'
        exfalso
        rw [val_last_fin] at hii'
        have h2 : i'.val ≤ n := by have := i'.isLt; omega
        omega
    | cast a =>
        induction i' using Fin.lastCases with
        | last =>
            intro hii'
            rw [val_castSucc_fin, val_last_fin] at hii'
            have ha : a.val = n - 1 := by omega
            have ha1 : 1 ≤ a.val := by omega
            have hjs : j = a := Fin.ext (by
              have h1 : j.val + 1 = a.val + 1 := by rw [hj]; omega
              omega)
            set a' : Fin n := ⟨a.val - 1, by omega⟩ with ha'
            have ha'v : a'.val = a.val - 1 := rfl
            have ha'succ : a'.succ = a.castSucc :=
              Fin.ext (by rw [val_succ_fin, val_castSucc_fin]; simp only [ha'v]; omega)
            have hcompat : hC.permAut₁ (Equiv.swap a.castSucc a.succ) =
                hC.permAut₂ (Equiv.swap a'.castSucc a.castSucc) := by
              rw [show Equiv.swap a.castSucc a.succ = Equiv.swap a'.succ a.succ from by
                rw [ha'succ]]
              exact hC.permAut_compat a' a
            have hne1 : a'.castSucc ≠ (a.castSucc : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_castSucc_fin, val_castSucc_fin] at hh
              simp only [ha'v] at hh
              omega
            have hne2 : a.castSucc ≠ (a.succ : Fin (n + 1)) :=
              (Fin.castSucc_lt_succ (i := a)).ne
            have hne3 : a'.castSucc ≠ (a.succ : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_castSucc_fin, val_succ_fin] at hh
              simp only [ha'v] at hh
              omega
            have hswapc : Equiv.swap a'.castSucc a.castSucc * Equiv.swap a.castSucc a.succ *
                Equiv.swap a'.castSucc a.castSucc =
                Equiv.swap a.castSucc a.succ * Equiv.swap a'.castSucc a.castSucc *
                  Equiv.swap a.castSucc a.succ :=
              swap_braid hne1 hne3 hne2
            have hslast : slast = ggLin (p := p) ι
                (hC.permAut₂ (Equiv.swap a.castSucc a.succ)) := by
              rw [show slast = ggLin (p := p) ι (hC.permAut₂ (Equiv.swap j.castSucc j.succ))
                from rfl, hjs]
            rw [hs_cast, hs_last, hcompat, hslast]
            simp only [← map_mul]
            rw [hswapc]
        | cast c =>
            intro hii'
            rw [val_castSucc_fin, val_castSucc_fin] at hii'
            have hcs : (c.castSucc : Fin (n + 1)) = a.succ :=
              Fin.ext (by rw [val_castSucc_fin, val_succ_fin]; omega)
            have hne1 : a.castSucc ≠ (a.succ : Fin (n + 1)) :=
              (Fin.castSucc_lt_succ (i := a)).ne
            have hne2 : a.castSucc ≠ (c.succ : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_castSucc_fin, val_succ_fin] at hh
              omega
            have hne3 : a.succ ≠ (c.succ : Fin (n + 1)) := by
              intro h
              have hh := congrArg Fin.val h
              rw [val_succ_fin, val_succ_fin] at hh
              omega
            have hswapc : Equiv.swap a.castSucc a.succ * Equiv.swap c.castSucc c.succ *
                Equiv.swap a.castSucc a.succ =
                Equiv.swap c.castSucc c.succ * Equiv.swap a.castSucc a.succ *
                  Equiv.swap c.castSucc c.succ := by
              rw [hcs]
              exact swap_braid hne1 hne2 hne3
            rw [hs_cast, hs_cast]
            simp only [← map_mul]
            rw [hswapc]

  have hfix : ∀ v : V, (∀ i, s i v = v) → v = 0 := by
    intro v hv
    set b : ↥Bs := Additive.toMul (ι.symm v) with hbdef
    have hbval : ι (Additive.ofMul b) = v := by
      rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hfix₁ : ∀ k : Fin n, hC.permAut₁ (Equiv.swap k.castSucc k.succ) b = b := by
      intro k
      have h1 : s k.castSucc (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
        rw [hbval]; exact hv k.castSucc
      rw [hs_cast, ggLin_apply_ofMul] at h1
      exact Additive.ofMul.injective (ι.injective h1)
    have hfix₂ : ∀ k : Fin n, hC.permAut₂ (Equiv.swap k.castSucc k.succ) b = b := by
      intro k
      by_cases hk : k.val = n - 1
      · have hkc : (k.castSucc : Fin (n + 1)) = j.castSucc :=
          Fin.ext (by rw [val_castSucc_fin, val_castSucc_fin]; omega)
        have hks : (k.succ : Fin (n + 1)) = j.succ :=
          Fin.ext (by rw [val_succ_fin, val_succ_fin]; omega)
        rw [hkc, hks]
        have h1 : s (Fin.last n) (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
          rw [hbval]
          exact hv (Fin.last n)
        rw [hs_last, ggLin_apply_ofMul] at h1
        exact Additive.ofMul.injective (ι.injective h1)
      · have hk' : k.val + 1 < n := by omega
        have h1 : hC.permAut₂ (Equiv.swap k.castSucc k.succ) =
            hC.permAut₁ (Equiv.swap k.succ (⟨k.val + 1, hk'⟩ : Fin n).succ) :=
          (hC.permAut_compat k ⟨k.val + 1, hk'⟩).symm
        rw [h1]
        have h2 : (⟨k.val + 1, hk'⟩ : Fin n).castSucc = k.succ :=
          Fin.ext (by rw [val_castSucc_fin, val_succ_fin])
        rw [← h2]
        exact hfix₁ ⟨k.val + 1, hk'⟩
    have hall₁ : ∀ π, hC.permAut₁ π b = b := permAut_fixed_of_swaps hfix₁
    have hall₂ : ∀ π, hC.permAut₂ π b = b := permAut_fixed_of_swaps hfix₂
    have hc₁ := hC.commute_of_permAut₁_fixed b.2 hall₁
    have hc₂ := hC.commute_of_permAut₂_fixed b.2 hall₂
    have hb1 : b = 1 := Subtype.ext (hC.inj b b.2 hc₁ hc₂)
    rw [← hbval, hb1, ofMul_one, map_zero]
  have hx_core : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      s i (ι (Additive.ofMul ⟨x, hC.x_mem⟩)) = ι (Additive.ofMul ⟨x, hC.x_mem⟩) := by
    intro i hi
    induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast k => exact hs_fix k
  obtain ⟨κ₀, hκ₀₁, hκ₀₂, hκ₀x⟩ := exists_linearEquiv_of_typeA_refl (p := p) hC.odd
    (n := n) (by have := hC.three_le; omega) s hrefl
    hdistinct hcomm_s hbraid_s hfix (ι (Additive.ofMul ⟨x, hC.x_mem⟩)) hx_core
    (by
      rw [hs_last, ggLin_apply_ofMul]
      intro h
      exact hC.permAut₂_swap_ne_x hj (Additive.ofMul.injective (ι.injective h)))
  have hmain : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ b : ↥Bs,
      (ι.trans κ₀.toAddEquiv) (Additive.ofMul (hC.permAut₁ σ b)) =
        coordPerm p n σ ((ι.trans κ₀.toAddEquiv) (Additive.ofMul b)) := by
    have htop : Subgroup.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) = ⊤ :=
      Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
    let H : Subgroup (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {τ | ∀ b : ↥Bs,
            (ι.trans κ₀.toAddEquiv) (Additive.ofMul (hC.permAut₁ τ b)) =
              coordPerm p n τ ((ι.trans κ₀.toAddEquiv) (Additive.ofMul b))}
        one_mem' := by
          intro b
          rw [map_one, MulAut.one_apply, map_one]
          rfl
        mul_mem' := fun {u v} hu hv => by
          intro b
          rw [map_mul, MulAut.mul_apply, hu, hv, map_mul]
          rfl
        inv_mem' := fun {u} hu => by
          intro b
          have h1 := hu (hC.permAut₁ u⁻¹ b)
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
          rw [map_inv]
          simpa using (congrArg (fun w => (coordPerm p n u)⁻¹ w) h1).symm }
    have hH : Subgroup.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) ≤ H := by
      rw [Subgroup.closure_le]
      rintro σ ⟨k, rfl⟩
      intro b
      rw [show (ι.trans κ₀.toAddEquiv)
            (Additive.ofMul (hC.permAut₁ (Equiv.swap k.castSucc k.succ) b))
          = κ₀ (s k.castSucc (ι (Additive.ofMul b))) from by
        rw [hs_cast, ggLin_apply_ofMul]
        rfl]
      exact congrFun (hκ₀₁ k) _
    intro σ
    have hmem : σ ∈ Subgroup.closure
        (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) := by
      rw [htop]
      exact Subgroup.mem_top σ
    exact hH hmem
  refine ⟨ι.trans κ₀.toAddEquiv, hmain, ?_, ?_⟩
  · intro b
    rw [show (ι.trans κ₀.toAddEquiv)
        (Additive.ofMul (hC.permAut₂ (Equiv.swap j.castSucc j.succ) b))
        = κ₀ (s (Fin.last n) (ι (Additive.ofMul b))) from by
      rw [hs_last, ggLin_apply_ofMul]
      rfl]
    exact congrFun hκ₀₂ _
  · exact hκ₀x

end Far

end CFSG.StandardType

end
