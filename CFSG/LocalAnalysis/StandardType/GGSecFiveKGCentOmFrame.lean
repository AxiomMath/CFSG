module

public import CFSG.LocalAnalysis.StandardType.GGStdPosDTorus

import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TorusM8POmegaPlus

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap

@[expose] def kgcIdx {n : ℕ} (k : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl k
  | false => .inr k

@[expose] noncomputable def kgcDiag {n : ℕ} {K : Type} [Field K] (σ : spinGroup (quadPlus n K))
    (m : Fin n ⊕ Fin n) : K :=
  spinAction (quadPlus n K) σ (Pi.single m 1) m

theorem kgcIdx_inj {n : ℕ} {k k' : Fin n} {r r' : Bool} :
    kgcIdx k r = kgcIdx k' r' ↔ k = k' ∧ r = r' := by
  cases r <;> cases r' <;> simp [kgcIdx]

theorem plusFrame_vec_eq_single_kgcIdx {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) (k : Fin n)
    (r : Bool) : (plusFrame n K hn).vec k r = Pi.single (kgcIdx k r) 1 := by
  cases r <;> rfl

theorem plusFrame_vec_apply_of_ne_kgcIdx {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {k : Fin n}
    {r : Bool} {m : Fin n ⊕ Fin n} (hm : m ≠ kgcIdx k r) : (plusFrame n K hn).vec k r m = 0 := by
  rw [plusFrame_vec_eq_single_kgcIdx, Pi.single_apply, if_neg hm]

theorem spinAction_apply_eq_kgcDiag_mul {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)}
    (hσ : σ ∈ ggTorus (plusDatum n K hn)) (x : Fin n ⊕ Fin n → K) (m : Fin n ⊕ Fin n) :
    spinAction (quadPlus n K) σ x m = kgcDiag σ m * x m := by
  have hM : ∀ a b : Fin n ⊕ Fin n, (spinMatrix (quadPlus n K) σ : Matrix _ _ K) a b =
      spinAction (quadPlus n K) σ (Pi.single b 1) a := fun a b => by
    rw [coe_spinMatrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  rw [← spinMatrix_mulVec]
  change ∑ b, (spinMatrix (quadPlus n K) σ : Matrix _ _ K) m b * x b = _
  rw [Finset.sum_eq_single m, hM]
  · rfl
  · intro b _ hb
    rw [ClassicalPosition.ggTorus_apply_eq_zero_POmegaPlus n K hn hσ (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ m) h

theorem spinAction_vec_eq_kgcDiag_smul {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)} (hσ : σ ∈ ggTorus (plusDatum n K hn)) (k : Fin n) (r : Bool) :
    spinAction (quadPlus n K) σ ((plusFrame n K hn).vec k r) =
      kgcDiag σ (kgcIdx k r) • (plusFrame n K hn).vec k r := by
  funext m
  rw [spinAction_apply_eq_kgcDiag_mul hn hσ, Pi.smul_apply, smul_eq_mul]
  by_cases hm : m = kgcIdx k r
  · rw [hm]
  · rw [plusFrame_vec_apply_of_ne_kgcIdx hn hm, mul_zero, mul_zero]

theorem kgcDiag_eq_one_of_fix {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)} (hσ : σ ∈ ggTorus (plusDatum n K hn)) {k : Fin n} {r : Bool}
    (h : spinAction (quadPlus n K) σ ((plusFrame n K hn).vec k r) = (plusFrame n K hn).vec k r) :
    kgcDiag σ (kgcIdx k r) = 1 := by
  have h1 := congrFun ((spinAction_vec_eq_kgcDiag_smul hn hσ k r).symm.trans h) (kgcIdx k r)
  rwa [plusFrame_vec_eq_single_kgcIdx, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one] at h1

theorem kgcDiag_inl_mul_inr {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {σ : spinGroup (quadPlus n K)}
    (hσ : σ ∈ ggTorus (plusDatum n K hn)) (k : Fin n) :
    kgcDiag σ (.inl k) * kgcDiag σ (.inr k) = 1 := by
  have h1 : polar (quadPlus n K) ((plusFrame n K hn).vec k true)
      ((plusFrame n K hn).vec k false) = 1 := (plusFrame n K hn).polar_vec_not k true
  have h := polar_spinAction (quadPlus n K) σ ((plusFrame n K hn).vec k true)
    ((plusFrame n K hn).vec k false)
  rw [spinAction_vec_eq_kgcDiag_smul hn hσ, spinAction_vec_eq_kgcDiag_smul hn hσ, polar_smul_left,
    polar_smul_right, h1, smul_eq_mul, smul_eq_mul, mul_one] at h
  exact h

theorem kgcDiag_mul_kgcDiag_not {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)} (hσ : σ ∈ ggTorus (plusDatum n K hn)) (k : Fin n) (r : Bool) :
    kgcDiag σ (kgcIdx k r) * kgcDiag σ (kgcIdx k (!r)) = 1 := by
  cases r
  · rw [mul_comm]
    exact kgcDiag_inl_mul_inr hn hσ k
  · exact kgcDiag_inl_mul_inr hn hσ k

theorem conj_longRoot_eq_of_kgcDiag_mul {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)}
    (hσ : σ ∈ ggTorus (plusDatum n K hn)) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h1 : kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1) (b : K) :
    σ * (plusFrame n K hn).longRoot hij s t (.ofAdd b) * σ⁻¹ =
      (plusFrame n K hn).longRoot hij s t (.ofAdd b) := by
  rw [StdPosD.conj_longRoot_of_smul (plusFrame n K hn) hij s t
    (spinAction_vec_eq_kgcDiag_smul hn hσ i s) (spinAction_vec_eq_kgcDiag_smul hn hσ j t) b, h1,
    one_mul]

theorem exists_map_vec_eq_of_commute_longRoot {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N) {g : V ≃ₗ[K] V} {i j : Fin N}
    (hij : i ≠ j) (s t : Bool)
    (hg : g * spinAction Q (F.longRoot hij s t (.ofAdd 1)) =
      spinAction Q (F.longRoot hij s t (.ofAdd 1)) * g) :
    ∃ a b : K, g (F.vec i s) = a • F.vec i s + b • F.vec j t := by
  have h2 := DFunLike.congr_fun hg (F.vec j (!t))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, F.spinAction_longRoot_vec_not_right hij s t 1,
    map_add, one_smul, F.spinAction_longRoot hij s t 1] at h2
  refine ⟨1 * polar Q (g (F.vec j (!t))) (F.vec j t),
    -(1 * polar Q (g (F.vec j (!t))) (F.vec i s)), ?_⟩
  rw [add_left_cancel (h2.trans (add_sub_assoc _ _ _)), neg_smul, sub_eq_add_neg]

theorem kgcDiag_eq_of_commute_of_apply_ne_zero {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)}
    (hσ : σ ∈ ggTorus (plusDatum n K hn)) {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g * spinAction (quadPlus n K) σ = spinAction (quadPlus n K) σ * g) (i : Fin n)
    (r : Bool) {m : Fin n ⊕ Fin n} (hm : g ((plusFrame n K hn).vec i r) m ≠ 0) :
    kgcDiag σ m = kgcDiag σ (kgcIdx i r) := by
  have h := DFunLike.congr_fun hg ((plusFrame n K hn).vec i r)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, spinAction_vec_eq_kgcDiag_smul hn hσ,
    map_smul] at h
  have h' := congrFun h m
  rw [Pi.smul_apply, smul_eq_mul, spinAction_apply_eq_kgcDiag_mul hn hσ] at h'
  exact (mul_right_cancel₀ hm h').symm

theorem exists_map_vec_eq_smul_of_commute {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    {S : Set (spinGroup (quadPlus n K))} (hST : S ⊆ ggTorus (plusDatum n K hn))
    (hgS : ∀ s ∈ S, g * spinAction (quadPlus n K) s = spinAction (quadPlus n K) s * g)
    (hgR : ∀ {i j : Fin n} (hij : i ≠ j) (s t : Bool),
      (∀ σ ∈ S, ∀ b : K, σ * (plusFrame n K hn).longRoot hij s t (.ofAdd b) * σ⁻¹ =
        (plusFrame n K hn).longRoot hij s t (.ofAdd b)) →
      ∀ b : K, g * spinAction (quadPlus n K) ((plusFrame n K hn).longRoot hij s t (.ofAdd b)) =
        spinAction (quadPlus n K) ((plusFrame n K hn).longRoot hij s t (.ofAdd b)) * g)
    (hI1 : ¬ ∃! i : Fin n, ∀ σ ∈ S,
      spinAction (quadPlus n K) σ ((plusFrame n K hn).vec i true) = (plusFrame n K hn).vec i true)
    (i : Fin n) (r : Bool) :
    ∃ a : K, g ((plusFrame n K hn).vec i r) = a • (plusFrame n K hn).vec i r := by
  have key : ∀ m, m ≠ kgcIdx i r → g ((plusFrame n K hn).vec i r) m = 0 := by
    intro m hm
    by_contra hne
    have heig : ∀ σ ∈ S, kgcDiag σ m = kgcDiag σ (kgcIdx i r) := fun σ hσ =>
      kgcDiag_eq_of_commute_of_apply_ne_zero hn (hST hσ) (hgS σ hσ) i r hne
    obtain ⟨k, r', rfl⟩ : ∃ k r', m = kgcIdx k r' := by
      rcases m with k | k
      · exact ⟨k, true, rfl⟩
      · exact ⟨k, false, rfl⟩
    by_cases hki : k = i
    · rw [hki] at hm heig hne
      have hr' : r' = !r := by
        cases r <;> cases r' <;> first | rfl | exact absurd rfl hm
      rw [hr'] at heig hne
      have hone : ∀ σ ∈ S, kgcDiag σ (kgcIdx i r) = 1 ∧ kgcDiag σ (kgcIdx i (!r)) = 1 := by
        intro σ hσ
        have h2 := kgcDiag_mul_kgcDiag_not hn (hST hσ) i r
        rw [heig σ hσ] at h2
        have hd : kgcDiag σ (kgcIdx i r) = 1 := by
          rcases mul_self_eq_one_iff.mp h2 with h | h
          · exact h
          · rw [h, CharTwo.neg_eq]
        exact ⟨hd, (heig σ hσ).trans hd⟩
      have hifix : ∀ σ ∈ S, spinAction (quadPlus n K) σ ((plusFrame n K hn).vec i true) =
          (plusFrame n K hn).vec i true := by
        intro σ hσ
        have h1 : kgcDiag σ (kgcIdx i true) = 1 := by
          cases r
          · exact (hone σ hσ).2
          · exact (hone σ hσ).1
        rw [spinAction_vec_eq_kgcDiag_smul hn (hST hσ), h1, one_smul]
      obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ ∀ σ ∈ S,
          spinAction (quadPlus n K) σ ((plusFrame n K hn).vec j true) =
            (plusFrame n K hn).vec j true := by
        by_contra hno
        refine hI1 ⟨i, hifix, fun j hjP => ?_⟩
        by_contra hji
        exact hno ⟨j, hji, hjP⟩
      have hc : ∀ σ ∈ S, ∀ b : K,
          σ * (plusFrame n K hn).longRoot hji.symm r true (.ofAdd b) * σ⁻¹ =
            (plusFrame n K hn).longRoot hji.symm r true (.ofAdd b) := fun σ hσ b =>
        conj_longRoot_eq_of_kgcDiag_mul hn (hST hσ) hji.symm r true
          (by rw [(hone σ hσ).1, kgcDiag_eq_one_of_fix hn (hST hσ) (hj σ hσ), one_mul]) b
      obtain ⟨a, b, hab⟩ := exists_map_vec_eq_of_commute_longRoot (plusFrame n K hn) hji.symm r
        true (hgR hji.symm r true hc 1)
      apply hne
      rw [hab, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        plusFrame_vec_apply_of_ne_kgcIdx hn (fun h => by cases r <;> simp [kgcIdx] at h),
        plusFrame_vec_apply_of_ne_kgcIdx hn (fun h => hji (kgcIdx_inj.1 h).1.symm), smul_zero,
        smul_zero, add_zero]
    · have hik : i ≠ k := Ne.symm hki
      have hc : ∀ σ ∈ S, ∀ b : K,
          σ * (plusFrame n K hn).longRoot hik r (!r') (.ofAdd b) * σ⁻¹ =
            (plusFrame n K hn).longRoot hik r (!r') (.ofAdd b) := fun σ hσ b =>
        conj_longRoot_eq_of_kgcDiag_mul hn (hST hσ) hik r (!r')
          (by rw [← heig σ hσ]; exact kgcDiag_mul_kgcDiag_not hn (hST hσ) k r') b
      obtain ⟨a, b, hab⟩ := exists_map_vec_eq_of_commute_longRoot (plusFrame n K hn) hik r (!r')
        (hgR hik r (!r') hc 1)
      apply hne
      rw [hab, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        plusFrame_vec_apply_of_ne_kgcIdx hn (fun h => hki (kgcIdx_inj.1 h).1),
        plusFrame_vec_apply_of_ne_kgcIdx hn (fun h => by cases r' <;> simp [kgcIdx] at h),
        smul_zero, smul_zero, add_zero]
  refine ⟨g ((plusFrame n K hn).vec i r) (kgcIdx i r), ?_⟩
  funext m
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hm : m = kgcIdx i r
  · rw [hm, plusFrame_vec_eq_single_kgcIdx hn i r, Pi.single_eq_same, mul_one]
  · rw [key m hm, plusFrame_vec_apply_of_ne_kgcIdx hn hm, mul_zero]

end CFSG.StandardType.KGCentOm

end
