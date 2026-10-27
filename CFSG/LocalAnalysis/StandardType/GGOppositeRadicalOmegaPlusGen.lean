module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusTrans
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.LieType.Universal.Spin.Generation.Frame
public import CFSG.LieType.Universal.Spin.Chevalley.Commutator

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal GGOppRad GGOppRadSpU
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

@[expose] def vecIdx (i : Fin n) : Bool → Fin n ⊕ Fin n
  | true => Sum.inl i
  | false => Sum.inr i

theorem plusVec_eq_single (i : Fin n) (s : Bool) :
    plusVec n K i s = Pi.single (vecIdx i s) 1 := by
  cases s <;> rfl

theorem vecIdx_not (i : Fin n) (s : Bool) : vecIdx i (!s) = (vecIdx i s).swap := by
  cases s <;> rfl

theorem vecIdx_eq_iff {i j : Fin n} {s t : Bool} : vecIdx i s = vecIdx j t ↔ i = j ∧ s = t := by
  cases s <;> cases t <;> simp [vecIdx]

theorem exists_vecIdx (a : Fin n ⊕ Fin n) : ∃ i s, a = vecIdx i s := by
  rcases a with i | i
  · exact ⟨i, true, rfl⟩
  · exact ⟨i, false, rfl⟩

theorem polar_single_plusVec (b : Fin n ⊕ Fin n) (j : Fin n) (t : Bool) :
    polar (quadPlus n K) (Pi.single b 1) (plusVec n K j t) =
      if b = vecIdx j (!t) then 1 else 0 := by
  obtain ⟨k, r, rfl⟩ := exists_vecIdx b
  rw [← plusVec_eq_single, polar_quadPlus_plusVec]
  by_cases h : k = j ∧ r = !t
  · rw [ite_eq_left h, ite_eq_left (vecIdx_eq_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (vecIdx_eq_iff.mp h')]

variable [Finite K] [CharP K 2]

theorem longRoot_mem_plusU (hn : 3 ≤ n) {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K)
    (h : ℓ (vecIdx i s) + ℓ (vecIdx j t) < M) :
    (plusFrame n K hn).longRoot hij s t (.ofAdd c) ∈ plusU (K := K) ℓ := by
  classical
  refine mem_plusU_iff_isUniTri.mpr fun b => ?_
  rw [plusRep_apply, HypFrame.spinAction_longRoot]
  change Pi.single b 1 + (c * polar (quadPlus n K) (Pi.single b 1) (plusVec n K j t)) •
      plusVec n K i s - (c * polar (quadPlus n K) (Pi.single b 1) (plusVec n K i s)) •
      plusVec n K j t - Pi.single b 1 ∈ stdFlag ℓ (ℓ b)
  rw [polar_single_plusVec, polar_single_plusVec, plusVec_eq_single, plusVec_eq_single]
  have h1 := hℓ.add_swap (vecIdx i s)
  have h2 := hℓ.add_swap (vecIdx j t)
  rw [← vecIdx_not] at h1 h2
  have e : ∀ x y : Fin n ⊕ Fin n → K, Pi.single b 1 + x - y - Pi.single b 1 = x - y :=
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

theorem sup_plusU_comp_swap (hn : 3 ≤ n) {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    (hne : ∃ a b, ℓ a < ℓ b) : plusU (K := K) ℓ ⊔ plusU (ℓ ∘ Sum.swap) = ⊤ := by
  have := isPerfect_spinGroup_quadPlus (K := K) hn
  have hsw : IsSpLevel M (ℓ ∘ Sum.swap) := hℓ.comp_swap
  have hroot : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K),
      ℓ (vecIdx i s) + ℓ (vecIdx j t) ≠ M →
      (plusFrame n K hn).longRoot hij s t (.ofAdd c) ∈
        plusU (K := K) ℓ ⊔ plusU (ℓ ∘ Sum.swap) := by
    intro i j hij s t c hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact Subgroup.mem_sup_left (longRoot_mem_plusU hn hℓ hij s t c h)
    · refine Subgroup.mem_sup_right (longRoot_mem_plusU hn hsw hij s t c ?_)
      have h1 := hℓ.add_swap (vecIdx i s)
      have h2 := hℓ.add_swap (vecIdx j t)
      simp only [Function.comp_apply]
      omega
  refine (plusFrame n K hn).eq_top_of_longRoot_mem_of_eq_zero (fun {i j} hij s t c => ?_)
    (fun v hv => RootCentOmega.eq_zero_of_polar_plusVec fun k u => by
      rw [polar_comm]
      exact hv k u) (range_spinAction_quadPlus hn).le
  by_cases hlevi : ℓ (vecIdx i s) + ℓ (vecIdx j t) = M
  · obtain ⟨k, v, hki, hkj, hkv⟩ : ∃ k v, k ≠ i ∧ k ≠ j ∧ ℓ (vecIdx k v) ≠ ℓ (vecIdx j t) := by
      by_contra! hcon
      obtain ⟨k₀, hk₀i, hk₀j⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
        by_contra! h
        have h0 := h ⟨0, by omega⟩
        have h1 := h ⟨1, by omega⟩
        have h2 := h ⟨2, by omega⟩
        simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
        omega
      have hkt := hcon k₀ true hk₀i hk₀j
      have hkf := hcon k₀ false hk₀i hk₀j
      have hpair := hℓ k₀
      have hjt := hℓ.add_swap (vecIdx j t)
      have his := hℓ.add_swap (vecIdx i s)
      rw [← vecIdx_not] at hjt his
      change ℓ (vecIdx k₀ true) + ℓ (vecIdx k₀ false) = M at hpair
      have hall : ∀ a, ℓ a = ℓ (vecIdx j t) := by
        intro a
        obtain ⟨k, r, rfl⟩ := exists_vecIdx a
        by_cases hki : k = i
        · subst hki
          rcases (show r = s ∨ r = !s by cases r <;> cases s <;> simp) with rfl | rfl
          · omega
          · omega
        by_cases hkj : k = j
        · subst hkj
          rcases (show r = t ∨ r = !t by cases r <;> cases t <;> simp) with rfl | rfl
          · rfl
          · omega
        exact hcon k r hki hkj
      obtain ⟨a, b, hab⟩ := hne
      rw [hall a, hall b] at hab
      exact lt_irrefl _ hab
    have hc := (plusFrame n K hn).commutator_longRoot_longRoot (Ne.symm hki) hkj hij s v t c 1
    rw [mul_one] at hc
    rw [← hc, commutatorElement_def]
    have hkv' := hℓ.add_swap (vecIdx k v)
    rw [← vecIdx_not] at hkv'
    have ha := hroot (Ne.symm hki) s v c (by omega)
    have hb := hroot hkj (!v) t 1 (by omega)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact hroot hij s t c hlevi

end GGOppRadOmega

end CFSG.StandardType
