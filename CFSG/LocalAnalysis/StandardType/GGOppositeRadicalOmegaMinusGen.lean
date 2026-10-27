module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusTrans
public import CFSG.LieType.Universal.Spin.Twisted.Generation
public import CFSG.LieType.Universal.Spin.Generation.Frame
public import CFSG.LieType.Universal.Spin.Chevalley.Commutator

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal GGOppRad GGOppRadSpU
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def mIdx (i : Fin (n - 1)) : Bool → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  | true => .inl i
  | false => .inr (.inl i)

omit [Finite K] in
theorem minusVec_eq_single (i : Fin (n - 1)) (s : Bool) :
    minusVec n (K := K) i s = Pi.single (mIdx i s) 1 := by
  cases s <;> rfl

omit [Finite K] in
theorem mpr_mIdx (i : Fin (n - 1)) (s : Bool) : mpr (mIdx (n := n) i s) = mIdx i (!s) := by
  cases s <;> rfl

omit [Finite K] in
theorem mIdx_eq_iff {i j : Fin (n - 1)} {s t : Bool} :
    mIdx (n := n) i s = mIdx j t ↔ i = j ∧ s = t := by
  cases s <;> cases t <;> simp [mIdx]

omit [Finite K] in
theorem polar_single_minusVec [CharP K 2] (b' : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (j : Fin (n - 1)) (t : Bool) :
    polar (quadMinus n K b c) (Pi.single b' 1) (minusVec n j t) =
      if b' = mIdx j (!t) then 1 else 0 := by
  classical
  rw [polar_single_minus, minusVec_eq_single]
  rcases b' with k | k | k
  · by_cases h : k = j ∧ true = !t
    · obtain ⟨rfl, ht⟩ := h
      have : t = false := by cases t <;> simp_all
      subst this
      simp [mg, mpr, mIdx]
    · rw [ite_eq_right fun h' => h (by
        cases t <;> simp_all [mIdx])]
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h'
      cases t <;> simp_all [mIdx, mpr]
  · by_cases h : k = j ∧ false = !t
    · obtain ⟨rfl, ht⟩ := h
      have : t = true := by cases t <;> simp_all
      subst this
      simp [mg, mpr, mIdx]
    · rw [ite_eq_right fun h' => h (by
        cases t <;> simp_all [mIdx])]
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h'
      cases t <;> simp_all [mIdx, mpr]
  · rw [ite_eq_right fun h' => by cases t <;> simp [mIdx] at h']
    rw [Pi.single_eq_of_ne (by cases t <;> simp [mpr, mIdx]), mul_zero]

variable [CharP K 2]

include hirr in
theorem longRoot_mem_minusU {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (c' : K)
    (h : ℓ (mIdx i s) + ℓ (mIdx j t) < M) :
    (minusFrame n b c).longRoot hij s t (.ofAdd c') ∈ minusU (b := b) (c := c) ℓ := by
  classical
  refine (mem_minusU_iff_isUniTriM hirr).mpr fun b' => ?_
  rw [minusRep_apply, HypFrame.spinAction_longRoot]
  change Pi.single b' 1 + (c' * polar (quadMinus n K b c) (Pi.single b' 1) (minusVec n j t)) •
      minusVec n i s - (c' * polar (quadMinus n K b c) (Pi.single b' 1) (minusVec n i s)) •
      minusVec n j t - Pi.single b' 1 ∈ stdFlag ℓ (ℓ b')
  rw [polar_single_minusVec, polar_single_minusVec, minusVec_eq_single, minusVec_eq_single]
  have h1 := hℓ.1 (mIdx i s)
  have h2 := hℓ.1 (mIdx j t)
  rw [mpr_mIdx] at h1 h2
  have e : ∀ x y : Vm n K, Pi.single b' 1 + x - y - Pi.single b' 1 = x - y :=
    fun x y => by abel
  rw [e]
  refine sub_mem ?_ ?_
  · split_ifs with hb
    · subst hb
      rw [mul_one]
      exact Submodule.smul_mem _ _ (single_mem_stdFlag.mpr (by omega))
    · rw [mul_zero, zero_smul]
      exact zero_mem _
  · split_ifs with hb
    · subst hb
      rw [mul_one]
      exact Submodule.smul_mem _ _ (single_mem_stdFlag.mpr (by omega))
    · rw [mul_zero, zero_smul]
      exact zero_mem _

theorem twShortRoot_mem_minusU {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K)
    (h : 2 * ℓ (mIdx i s) < M) :
    twShortRoot n hirr i s (.ofAdd p) ∈ minusU (b := b) (c := c) ℓ := by
  classical
  refine (mem_minusU_iff_isUniTriM hirr).mpr fun b' => ?_
  rw [minusRep_apply, spinAction_twShortRoot]
  rw [polar_comm (quadMinus n K b c) (Pi.single b' 1) (minusVec n i s),
    polar_comm (quadMinus n K b c) (Pi.single b' 1) (planeVec n p)]
  have h1 := hℓ.1 (mIdx i s)
  rw [mpr_mIdx] at h1
  have hpl : ∀ t : Fin 2, 2 * ℓ (.inr (.inr t)) = M := fun t => hℓ.plane t
  have hplane : planeVec n p ∈ stdFlag (K := K) ℓ (ℓ b') ∨ ¬ (b' = mIdx i (!s)) := by
    by_cases hb : b' = mIdx i (!s)
    · left
      intro a ha
      rcases a with k | k | t
      · rfl
      · rfl
      · subst hb
        have := hpl t
        omega
    · exact Or.inr hb
  have hvec : (minusVec n i s : Vm n K) ∈ stdFlag (K := K) ℓ (ℓ b') ∨
      (polar (quadMinus n K b c) (minusVec n i s) (Pi.single b' 1) = 0 ∧
        polar (quadMinus n K b c) (planeVec n p) (Pi.single b' 1) = 0) := by
    rcases b' with k | k | t
    · by_cases hb : (Sum.inl k : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = mIdx i (!s)
      · left
        rw [minusVec_eq_single]
        refine single_mem_stdFlag.mpr ?_
        rw [hb]
        omega
      · right
        refine ⟨?_, ?_⟩
        · rw [polar_comm, polar_single_minusVec, ite_eq_right hb]
        · rw [polar_comm, polar_single_minus]
          simp [planeVec, mpr]
    · by_cases hb : (Sum.inr (Sum.inl k) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = mIdx i (!s)
      · left
        rw [minusVec_eq_single]
        refine single_mem_stdFlag.mpr ?_
        rw [hb]
        omega
      · right
        refine ⟨?_, ?_⟩
        · rw [polar_comm, polar_single_minusVec, ite_eq_right hb]
        · rw [polar_comm, polar_single_minus]
          simp [planeVec, mpr]
    · left
      rw [minusVec_eq_single]
      refine single_mem_stdFlag.mpr ?_
      have := hpl t
      omega
  have e : ∀ x y z : Vm n K, Pi.single b' 1 + x - y - z - Pi.single b' 1 = x - y - z :=
    fun x y z => by abel
  rw [e]
  rcases hvec with hv | ⟨hv1, hv2⟩
  · refine sub_mem (sub_mem ?_ (Submodule.smul_mem _ _ hv)) (Submodule.smul_mem _ _ hv)
    rcases hplane with hp | hp
    · exact Submodule.smul_mem _ _ hp
    · rw [polar_comm, polar_single_minusVec, ite_eq_right hp, zero_smul]
      exact zero_mem _
  · rw [hv1, hv2, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero]
    exact zero_mem _

omit [Finite K] [CharP K 2] in
theorem exists_mIdx (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (∃ i s, a = mIdx i s) ∨ ∃ t, a = .inr (.inr t) := by
  rcases a with i | i | t
  · exact Or.inl ⟨i, true, rfl⟩
  · exact Or.inl ⟨i, false, rfl⟩
  · exact Or.inr ⟨t, rfl⟩

include hirr in
theorem sup_minusU_comp_mpr (hn : 4 ≤ n) {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) (hne : ∃ a a', ℓ a < ℓ a') :
    minusU (b := b) (c := c) ℓ ⊔ minusU (ℓ ∘ mpr) = ⊤ := by
  have := isPerfect_spinGroup_quadMinus hn hirr
  have hsw : IsMinusLevel M (ℓ ∘ mpr) := hℓ.comp_mpr
  have hpl : ∀ t : Fin 2, 2 * ℓ (.inr (.inr t)) = M := fun t => hℓ.plane t
  have hpair : ∀ i s, ℓ (mIdx i s) + ℓ (mIdx i (!s)) = M := fun i s => by
    have := hℓ.1 (mIdx i s)
    rwa [mpr_mIdx] at this
  have hnc : ¬ ∀ a, ℓ a = M / 2 := by
    intro h
    obtain ⟨a, a', hab⟩ := hne
    rw [h a, h a'] at hab
    exact lt_irrefl _ hab
  have hroot : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (c' : K),
      ℓ (mIdx i s) + ℓ (mIdx j t) ≠ M →
      (minusFrame n b c).longRoot hij s t (.ofAdd c') ∈
        minusU (b := b) (c := c) ℓ ⊔ minusU (ℓ ∘ mpr) := by
    intro i j hij s t c' hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact Subgroup.mem_sup_left (longRoot_mem_minusU hirr hℓ hij s t c' h)
    · refine Subgroup.mem_sup_right (longRoot_mem_minusU hirr hsw hij s t c' ?_)
      simp only [Function.comp_apply, mpr_mIdx]
      have := hpair i s
      have := hpair j t
      omega
  have hlong : ∀ {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (c' : K),
      (minusFrame n b c).longRoot hij s t (.ofAdd c') ∈
        minusU (b := b) (c := c) ℓ ⊔ minusU (ℓ ∘ mpr) := by
    intro i j hij s t c'
    by_cases hlevi : ℓ (mIdx i s) + ℓ (mIdx j t) = M
    · obtain ⟨k, v, hki, hkj, hkv⟩ : ∃ k v, k ≠ i ∧ k ≠ j ∧ ℓ (mIdx k v) ≠ ℓ (mIdx j t) := by
        by_contra! hcon
        obtain ⟨k₀, hk₀i, hk₀j⟩ : ∃ k : Fin (n - 1), k ≠ i ∧ k ≠ j := by
          by_contra! h
          have h0 := h ⟨0, by omega⟩
          have h1 := h ⟨1, by omega⟩
          have h2 := h ⟨2, by omega⟩
          simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
          omega
        have hkt := hcon k₀ true hk₀i hk₀j
        have hkf := hcon k₀ false hk₀i hk₀j
        have hk := hpair k₀ true
        have hjt := hpair j t
        have his := hpair i s
        refine hnc fun a => ?_
        rcases exists_mIdx a with ⟨k, r, rfl⟩ | ⟨u, rfl⟩
        · simp only [Bool.not_true] at hk
          by_cases hki : k = i
          · subst hki
            rcases (show r = s ∨ r = !s by cases r <;> cases s <;> simp) with rfl | rfl
            · omega
            · omega
          by_cases hkj : k = j
          · subst hkj
            rcases (show r = t ∨ r = !t by cases r <;> cases t <;> simp) with rfl | rfl
            · omega
            · omega
          have := hcon k r hki hkj
          omega
        · have := hpl u
          omega
      have hc := (minusFrame n b c).toHypFrame.commutator_longRoot_longRoot (Ne.symm hki) hkj hij
        s v t c' 1
      rw [mul_one] at hc
      change ⁅(minusFrame n b c).longRoot (Ne.symm hki) s v (.ofAdd c'),
        (minusFrame n b c).longRoot hkj (!v) t (.ofAdd 1)⁆ =
          (minusFrame n b c).longRoot hij s t (.ofAdd c') at hc
      rw [← hc, commutatorElement_def]
      have hkv' := hpair k v
      have ha := hroot (Ne.symm hki) s v c' (by omega)
      have hb := hroot hkj (!v) t 1 (by omega)
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · exact hroot hij s t c' hlevi
  have hshort : ∀ (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K),
      twShortRoot n hirr i s (.ofAdd p) ∈ minusU (b := b) (c := c) ℓ ⊔ minusU (ℓ ∘ mpr) := by
    have hoff : ∀ (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K), 2 * ℓ (mIdx i s) ≠ M →
        twShortRoot n hirr i s (.ofAdd p) ∈ minusU (b := b) (c := c) ℓ ⊔ minusU (ℓ ∘ mpr) := by
      intro i s p hne'
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact Subgroup.mem_sup_left (twShortRoot_mem_minusU hirr hℓ i s p h)
      · refine Subgroup.mem_sup_right (twShortRoot_mem_minusU hirr hsw i s p ?_)
        simp only [Function.comp_apply, mpr_mIdx]
        have := hpair i s
        omega
    intro i s p
    by_cases hmid : 2 * ℓ (mIdx i s) = M
    · obtain ⟨j, r, hjr⟩ : ∃ j r, 2 * ℓ (mIdx j r) ≠ M := by
        by_contra! hcon
        refine hnc fun a => ?_
        rcases exists_mIdx a with ⟨k, r, rfl⟩ | ⟨u, rfl⟩
        · have := hcon k r
          omega
        · have := hpl u
          omega
      have hji : j ≠ i := by
        rintro rfl
        rcases (show r = s ∨ r = !s by cases r <;> cases s <;> simp) with rfl | rfl
        · exact hjr hmid
        · have := hpair j s
          omega
      have hc := commutator_longRoot_twShortRoot n hirr (Ne.symm hji) s (!r) 1 p
      simp only [Bool.not_not, one_smul, one_mul] at hc
      have hy : twShortRoot n hirr i s (.ofAdd p) =
          ⁅(minusFrame n b c).longRoot (Ne.symm hji) s (!r) (.ofAdd 1),
            twShortRoot n hirr j r (.ofAdd p)⁆ *
          ((minusFrame n b c).longRoot (Ne.symm hji) s r (.ofAdd (planeNorm b c p)))⁻¹ := by
        rw [hc, mul_inv_cancel_right]
      rw [hy, commutatorElement_def]
      have ha := hlong (Ne.symm hji) s (!r) 1
      have hb := hoff j r p hjr
      have hd := hlong (Ne.symm hji) s r (planeNorm b c p)
      exact mul_mem (mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) (inv_mem hd)
    · exact hoff i s p hmid
  refine (minusFrame n b c).toHypFrame.eq_top_of_longRoot_mem (fun {i j} hij s t c' => hlong hij s t c')
    (fun i s v hv => ?_) (fun v hv hQ => ?_) (range_spinAction_quadMinus hn hirr).le
  · rw [eq_planeVec_of_polar_minusVec n b c hv]
    change eichler (quadMinus n K b c) (minusVec n i s) _ ∈ _
    rw [← spinAction_twShortRoot_eq_eichler n hirr i s]
    exact Subgroup.mem_map_of_mem _ (hshort i s _)
  · rw [eq_planeVec_of_polar_minusVec n b c hv] at hQ ⊢
    rw [quadMinus_planeVec'] at hQ
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQ
    rw [hw, planeVec_zero]

end GGOppRadOmega

end CFSG.StandardType
