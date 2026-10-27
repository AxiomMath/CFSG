module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def ggDReflSet (n : ℕ) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  {t | ∃ c : GGBCV n, ggBCWt c = 2 ∧ ∃ hc : c ⬝ᵥ c ≠ 0, t = ggBCRefl c hc}

private def ggQ2xQD_vec {n : ℕ} (i j : Fin n) (e : ZMod 3) : GGBCV n :=
  Pi.single i 1 + e • Pi.single j 1

private lemma ggQ2xQD_vec_wt {n : ℕ} {i j : Fin n} (hij : i ≠ j) {e : ZMod 3} (he : e ≠ 0) :
    ggBCWt (ggQ2xQD_vec i j e) = 2 := by
  have h : ggQ2xQD_vec i j e
      = (1 : ZMod 3) • (Pi.single i (1 : ZMod 3) : GGBCV n) + e • Pi.single j 1 := by
    rw [ggQ2xQD_vec, one_smul]
  rw [h]
  exact ggQ2x_wt_smul_single_add_single i j hij 1 e one_ne_zero he

private lemma ggQ2xQD_vec_norm {n : ℕ} {i j : Fin n} (hij : i ≠ j) {e : ZMod 3} (he : e ≠ 0) :
    ggQ2xQD_vec i j e ⬝ᵥ ggQ2xQD_vec i j e = 2 := by
  rw [ggQ2x_dot_self_eq_wt, ggQ2xQD_vec_wt hij he]
  decide

private noncomputable def ggQ2xQD_ref {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (ggQ2xQD_vec i j e) (by rw [ggQ2xQD_vec_norm hij he]; decide)

private lemma ggQ2xQD_ref_apply {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) (v : GGBCV n) :
    ggQ2xQD_ref i j e hij he v
      = v + ((ggQ2xQD_vec i j e ⬝ᵥ v) * 2) • ggQ2xQD_vec i j e := by
  rw [ggQ2xQD_ref, ggQ2x_ggBCRefl_apply, ggQ2xQD_vec_norm hij he]

private lemma ggQ2xQD_ref_mem {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQD_ref i j e hij he ∈ ggDReflSet n :=
  ⟨ggQ2xQD_vec i j e, ggQ2xQD_vec_wt hij he,
    by rw [ggQ2xQD_vec_norm hij he]; decide, rfl⟩

private lemma ggQ2xQD_zmod3_sq_eq_one {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := by
  revert hx; revert x; decide

private lemma ggQ2xQD_zmod3_cases_of_sq {x : ZMod 3} (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  revert hx; revert x; decide

private lemma ggQ2xQD_add_self (a : ZMod 3) : a + a = -a := by revert a; decide

private lemma ggQ2xQD_eq_smul_of_smul_eq {n : ℕ} {a b : ZMod 3} {c c' : GGBCV n}
    (ha : a * a = 1) (h : a • c' = b • c) : c' = (a * b) • c := by
  calc c' = (a * a) • c' := by rw [ha, one_smul]
    _ = a • (a • c') := by rw [mul_smul]
    _ = (a * b) • c := by rw [h, smul_smul]

private lemma ggQ2xQD_refl_smul {n : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hac : (a • c) ⬝ᵥ (a • c) ≠ 0) :
    ggBCRefl (a • c) hac = ggBCRefl c hc := by
  ext v
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  have h1 : (a • c) ⬝ᵥ v = a * (c ⬝ᵥ v) := by rw [smul_dotProduct, smul_eq_mul]
  have h2 : (a • c) ⬝ᵥ (a • c) = c ⬝ᵥ c := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [show a * (a * (c ⬝ᵥ c)) = c ⬝ᵥ c by
      rw [← mul_assoc, ggQ2x_mul_self_eq_one a ha, one_mul]]
  rw [h1, h2, smul_smul]
  congr 1
  rw [show a * (c ⬝ᵥ v) * (c ⬝ᵥ c) * a = c ⬝ᵥ v * (c ⬝ᵥ c) by
    rw [show a * (c ⬝ᵥ v) * (c ⬝ᵥ c) * a = (a * a) * (c ⬝ᵥ v * (c ⬝ᵥ c)) by ring,
      ggQ2x_mul_self_eq_one a ha, one_mul]]

private lemma ggQ2xQD_refl_congr {n : ℕ} {c c' : GGBCV n} (h : c = c')
    (hc : c ⬝ᵥ c ≠ 0) (hc' : c' ⬝ᵥ c' ≠ 0) :
    ggBCRefl c hc = ggBCRefl c' hc' := by
  subst h
  exact rfl

private lemma ggQ2xQD_smul_norm {n : ℕ} {a : ZMod 3} (ha : a ≠ 0) (c : GGBCV n) :
    (a • c) ⬝ᵥ (a • c) = c ⬝ᵥ c := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [show a * (a * (c ⬝ᵥ c)) = c ⬝ᵥ c by
    rw [← mul_assoc, ggQ2x_mul_self_eq_one a ha, one_mul]]

private lemma ggQ2xQD_vec_norm_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) {e : ZMod 3}
    (he : e ≠ 0) : ggQ2xQD_vec i j e ⬝ᵥ ggQ2xQD_vec i j e ≠ 0 := by
  rw [ggQ2xQD_vec_norm hij he]; decide

private lemma ggQ2xQD_vec_swap {n : ℕ} (i j : Fin n) (e : ZMod 3) (he : e ≠ 0) :
    ggQ2xQD_vec j i e = e • ggQ2xQD_vec i j e := by
  rw [ggQ2xQD_vec, ggQ2xQD_vec, smul_add, smul_smul, ggQ2x_mul_self_eq_one e he, one_smul,
    add_comm]

private lemma ggQ2xQD_ref_swap {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQD_ref j i e (Ne.symm hij) he = ggQ2xQD_ref i j e hij he := by
  rw [ggQ2xQD_ref, ggQ2xQD_ref]
  have Q : (e • ggQ2xQD_vec i j e) ⬝ᵥ (e • ggQ2xQD_vec i j e) ≠ 0 := by
    rw [ggQ2xQD_smul_norm he]
    exact ggQ2xQD_vec_norm_ne hij he
  exact (ggQ2xQD_refl_congr (ggQ2xQD_vec_swap i j e he) _ Q).trans
    (ggQ2xQD_refl_smul e he (ggQ2xQD_vec i j e) _ Q)

private lemma ggQ2xQD_vec_dot_single {n : ℕ} (i j k : Fin n) (e : ZMod 3) :
    ggQ2xQD_vec i j e ⬝ᵥ Pi.single k (1 : ZMod 3)
      = (if i = k then 1 else 0) + e * (if j = k then 1 else 0) := by
  simp only [ggQ2xQD_vec, add_dotProduct, smul_dotProduct, single_one_dotProduct,
    Pi.single_apply, smul_eq_mul]

private lemma ggQ2xQD_vec_dot_vec {n : ℕ} (i j k l : Fin n) (e f : ZMod 3) :
    ggQ2xQD_vec i j e ⬝ᵥ ggQ2xQD_vec k l f
      = (if i = k then 1 else 0) + f * (if i = l then 1 else 0)
        + e * (if j = k then 1 else 0) + (e * f) * (if j = l then 1 else 0) := by
  simp only [ggQ2xQD_vec, add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
    single_one_dotProduct, Pi.single_apply, smul_eq_mul]
  ring

private lemma ggQ2xQD_ref_single_self {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQD_ref i j e hij he (Pi.single i (1 : ZMod 3))
      = (-e) • Pi.single j (1 : ZMod 3) := by
  have hcases : e = 1 ∨ e = -1 := by revert he; revert e; decide
  rw [ggQ2xQD_ref_apply, ggQ2xQD_vec_dot_single, if_pos rfl, if_neg (Ne.symm hij),
    mul_zero, add_zero, one_mul]
  rcases hcases with rfl | rfl
  · ext k
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> decide
  · ext k
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> decide

private lemma ggQ2xQD_ref_single_other {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQD_ref i j e hij he (Pi.single j (1 : ZMod 3))
      = (-e) • Pi.single i (1 : ZMod 3) := by
  have hcases : e = 1 ∨ e = -1 := by revert he; revert e; decide
  rw [ggQ2xQD_ref_apply, ggQ2xQD_vec_dot_single, if_neg hij, if_pos rfl, zero_add, mul_one]
  rcases hcases with rfl | rfl
  · ext k
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> decide
  · ext k
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> decide

private lemma ggQ2xQD_ref_single_ne {n : ℕ} {i j k : Fin n} (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) (hki : k ≠ i) (hkj : k ≠ j) :
    ggQ2xQD_ref i j e hij he (Pi.single k (1 : ZMod 3)) = Pi.single k (1 : ZMod 3) := by
  rw [ggQ2xQD_ref_apply, ggQ2xQD_vec_dot_single, if_neg (Ne.symm hki), if_neg (Ne.symm hkj),
    mul_zero, add_zero, zero_mul, zero_smul, add_zero]

private lemma ggQ2xQD_ref_eq_iff {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (hkl : k ≠ l) (he : e ≠ 0) (hf : f ≠ 0) :
    ggQ2xQD_ref i j e hij he = ggQ2xQD_ref k l f hkl hf ↔
      (i = k ∧ j = l ∨ i = l ∧ j = k) ∧ e = f := by
  constructor
  · intro h
    have h1 : ggQ2xQD_ref i j e hij he (Pi.single i (1 : ZMod 3))
        = ggQ2xQD_ref k l f hkl hf (Pi.single i (1 : ZMod 3)) :=
      congrArg (fun r : GGBCV n ≃ₗ[ZMod 3] GGBCV n => r (Pi.single i (1 : ZMod 3))) h
    rw [ggQ2xQD_ref_single_self i j e hij he] at h1
    by_cases hik : i = k
    · rw [hik] at h1
      rw [ggQ2xQD_ref_single_self k l f hkl hf] at h1
      have h2 := congrArg (fun v : GGBCV n => v j) h1
      simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_apply, smul_eq_mul, mul_one]
        at h2
      have hjl : j = l := by
        by_contra hne
        rw [if_neg hne, mul_zero] at h2
        exact (neg_ne_zero.mpr he) h2
      have hef : e = f := by
        rw [hjl, if_pos rfl, mul_one] at h2
        exact neg_inj.mp h2
      exact ⟨Or.inl ⟨hik, hjl⟩, hef⟩
    · by_cases hil : i = l
      · rw [hil] at h1
        rw [ggQ2xQD_ref_single_other k l f hkl hf] at h1
        have h2 := congrArg (fun v : GGBCV n => v j) h1
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_apply, smul_eq_mul, mul_one]
          at h2
        have hjk : j = k := by
          by_contra hne
          rw [if_neg hne, mul_zero] at h2
          exact (neg_ne_zero.mpr he) h2
        have hef : e = f := by
          rw [hjk, if_pos rfl, mul_one] at h2
          exact neg_inj.mp h2
        exact ⟨Or.inr ⟨hil, hjk⟩, hef⟩
      · rw [ggQ2xQD_ref_single_ne f hkl hf hik hil] at h1
        have h2 := congrArg (fun v : GGBCV n => v i) h1
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.single_apply, smul_eq_mul] at h2
        rw [if_neg hij, mul_zero] at h2
        exact (zero_ne_one h2).elim
  · rintro ⟨(⟨hik, hjl⟩ | ⟨hil, hjk⟩), hef⟩
    · subst hik; subst hjl; subst hef; rfl
    · subst hjk; subst hil; subst hef
      exact (ggQ2xQD_ref_swap i j e hij he).symm

private lemma ggQ2xQD_eq_neg_of_ne : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x ≠ y → y = -x := by
  decide

private lemma ggQ2xQD_refl_comm_commutator {n : ℕ} (c c' v : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hc' : c' ⬝ᵥ c' ≠ 0) :
    ggBCRefl c hc (ggBCRefl c' hc' v) - ggBCRefl c' hc' (ggBCRefl c hc v)
      = ((c ⬝ᵥ c') * (c ⬝ᵥ c) * (c' ⬝ᵥ c')) •
          ((c' ⬝ᵥ v) • c - (c ⬝ᵥ v) • c') := by
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  ext j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct_add,
    dotProduct_smul, smul_dotProduct, add_dotProduct, sub_dotProduct]
  rw [dotProduct_comm c' c]
  ring

private lemma ggQ2xQD_refl_comm_iff_wt {n : ℕ} {c c' : GGBCV n}
    (hcw : ggBCWt c = 2) (hcw' : ggBCWt c' = 2)
    (hc : c ⬝ᵥ c ≠ 0) (hc' : c' ⬝ᵥ c' ≠ 0)
    (hne : ggBCRefl c hc ≠ ggBCRefl c' hc') :
    ggBCRefl c hc * ggBCRefl c' hc' = ggBCRefl c' hc' * ggBCRefl c hc ↔
      c ⬝ᵥ c' = 0 := by
  have hc2 : c ⬝ᵥ c = 2 := by rw [ggQ2x_dot_self_eq_wt, hcw]; decide
  have hc2' : c' ⬝ᵥ c' = 2 := by rw [ggQ2x_dot_self_eq_wt, hcw']; decide
  constructor
  · intro hcomm
    by_contra hm
    have h0 : ggBCRefl c hc (ggBCRefl c' hc' c) - ggBCRefl c' hc' (ggBCRefl c hc c) = 0 := by
      have hcc := congrArg (fun r : GGBCV n ≃ₗ[ZMod 3] GGBCV n => r c) hcomm
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hcc
      rw [hcc, sub_self]
    have hkey := ggQ2xQD_refl_comm_commutator c c' c hc hc'
    rw [h0] at hkey
    have hscal : (c ⬝ᵥ c') * (c ⬝ᵥ c) * (c' ⬝ᵥ c') = c ⬝ᵥ c' := by
      rw [hc2, hc2']
      rw [show c ⬝ᵥ c' * 2 * 2 = c ⬝ᵥ c' by
        rw [show c ⬝ᵥ c' * 2 * 2 = c ⬝ᵥ c' * (2 * 2) by ring,
          show (2 : ZMod 3) * 2 = 1 by decide, mul_one]]
    have h2 : (c ⬝ᵥ c') • ((c ⬝ᵥ c') • c - (2 : ZMod 3) • c') = 0 := by
      have hh := hkey.symm
      rw [hscal, hc2, dotProduct_comm c' c] at hh
      exact hh
    rcases smul_eq_zero.mp h2 with hm0 | hm2
    · exact hm hm0
    · refine hne ?_
      have h3 : (2 : ZMod 3) • c' = (c ⬝ᵥ c') • c := (sub_eq_zero.mp hm2).symm
      have hc'e := ggQ2xQD_eq_smul_of_smul_eq (by decide : (2 : ZMod 3) * 2 = 1) h3
      have hcoef : (2 : ZMod 3) * (c ⬝ᵥ c') ≠ 0 :=
        mul_ne_zero (by decide) hm
      have hac : ((2 * (c ⬝ᵥ c')) • c) ⬝ᵥ ((2 * (c ⬝ᵥ c')) • c) ≠ 0 := by
        rw [ggQ2xQD_smul_norm hcoef]; exact hc
      exact (ggQ2xQD_refl_smul (2 * (c ⬝ᵥ c')) hcoef c hc hac).symm.trans
        (ggQ2xQD_refl_congr hc'e.symm hac hc')
  · intro hm
    apply LinearEquiv.ext
    intro v
    have hkey := ggQ2xQD_refl_comm_commutator c c' v hc hc'
    simp only [hm, zero_mul, zero_smul] at hkey
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact sub_eq_zero.mp hkey

private lemma ggQ2xQD_vec_dot_disjoint {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ggQ2xQD_vec i j e ⬝ᵥ ggQ2xQD_vec k l f = 0 := by
  rw [ggQ2xQD_vec_dot_vec, if_neg hik, if_neg hil, if_neg hjk, if_neg hjl]
  simp

private lemma ggQ2xQD_vec_dot_ne_share {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (hkl : k ≠ l) (he : e ≠ 0) (hf : f ≠ 0)
    (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)))
    (hdis : ¬ (i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l)) :
    ggQ2xQD_vec i j e ⬝ᵥ ggQ2xQD_vec k l f ≠ 0 := by
  rw [ggQ2xQD_vec_dot_vec]
  by_cases hik : i = k
  · have hkil : i ≠ l := fun h => hkl (by rw [← hik, h])
    have hkij : j ≠ k := fun h => hij (by rw [hik, h])
    have hjl : j ≠ l := fun h => hne (Or.inl ⟨hik, h⟩)
    rw [if_pos hik, if_neg hkil, if_neg hkij, if_neg hjl]
    simpa using (by decide : (1 : ZMod 3) ≠ 0)
  · by_cases hil : i = l
    · have hjl : j ≠ l := fun h => hij (by rw [hil, h])
      have hjk : j ≠ k := fun h => hne (Or.inr ⟨hil, h⟩)
      rw [if_neg hik, if_pos hil, if_neg hjk, if_neg hjl]
      simpa using hf
    · by_cases hjk : j = k
      · have hjl : j ≠ l := fun h => hkl (by rw [← hjk, h])
        rw [if_neg hik, if_neg hil, if_pos hjk, if_neg hjl]
        simpa using he
      · have hjl : j = l := by
          by_contra h
          exact hdis ⟨hik, hil, hjk, h⟩
        rw [if_neg hik, if_neg hil, if_neg hjk, if_pos hjl]
        simpa using mul_ne_zero he hf

private lemma ggQ2xQD_ref_same_pair_comm {n : ℕ} (i j : Fin n) (e f : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) (hf : f ≠ 0) :
    ggQ2xQD_ref i j e hij he * ggQ2xQD_ref i j f hij hf =
      ggQ2xQD_ref i j f hij hf * ggQ2xQD_ref i j e hij he := by
  by_cases hef : e = f
  · subst hef; rfl
  · have hne : ggQ2xQD_ref i j e hij he ≠ ggQ2xQD_ref i j f hij hf := by
      intro h
      exact hef ((ggQ2xQD_ref_eq_iff hij hij he hf).mp h).2
    simp only [ggQ2xQD_ref]
    rw [ggQ2xQD_refl_comm_iff_wt (ggQ2xQD_vec_wt hij he) (ggQ2xQD_vec_wt hij hf)
      (ggQ2xQD_vec_norm_ne hij he) (ggQ2xQD_vec_norm_ne hij hf) hne]
    rw [ggQ2xQD_vec_dot_vec, if_pos rfl, if_neg hij, if_neg (Ne.symm hij), if_pos rfl]
    simp only [mul_zero, add_zero, mul_one]
    rcases ggQ2xQD_zmod3_cases_of_sq (ggQ2xQD_zmod3_sq_eq_one he) with rfl | rfl
    · rcases ggQ2xQD_zmod3_cases_of_sq (ggQ2xQD_zmod3_sq_eq_one hf) with hf1 | hf1
      · exact (hef hf1.symm).elim
      · subst hf1; decide
    · rcases ggQ2xQD_zmod3_cases_of_sq (ggQ2xQD_zmod3_sq_eq_one hf) with hf1 | hf1
      · subst hf1; decide
      · exact (hef hf1.symm).elim

private lemma ggQ2xQD_ref_comm_iff {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (hkl : k ≠ l) (he : e ≠ 0) (hf : f ≠ 0) :
    ggQ2xQD_ref i j e hij he * ggQ2xQD_ref k l f hkl hf =
        ggQ2xQD_ref k l f hkl hf * ggQ2xQD_ref i j e hij he ↔
      (i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) ∨ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  by_cases heq : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  · constructor
    · intro _; exact Or.inr heq
    · intro _; rcases heq with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
      · subst hik; subst hjl
        exact ggQ2xQD_ref_same_pair_comm i j e f hij he hf
      · subst hjk; subst hil
        rw [ggQ2xQD_ref_swap i j f hij hf]
        exact ggQ2xQD_ref_same_pair_comm i j e f hij he hf
  · have hne : ggQ2xQD_ref i j e hij he ≠ ggQ2xQD_ref k l f hkl hf := by
      intro h
      exact heq ((ggQ2xQD_ref_eq_iff hij hkl he hf).mp h).1
    simp only [ggQ2xQD_ref]
    rw [ggQ2xQD_refl_comm_iff_wt (ggQ2xQD_vec_wt hij he) (ggQ2xQD_vec_wt hkl hf)
      (ggQ2xQD_vec_norm_ne hij he) (ggQ2xQD_vec_norm_ne hkl hf) hne]
    constructor
    · intro hdot
      by_contra hdis
      exact ggQ2xQD_vec_dot_ne_share hij hkl he hf heq (fun hd => hdis (Or.inl hd)) hdot
    · intro hdis
      rcases hdis with hd | hd
      · exact ggQ2xQD_vec_dot_disjoint hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      · exact absurd hd heq

private lemma ggQ2xQD_wt_two_repr {n : ℕ} {v : GGBCV n} (h : ggBCWt v = 2) :
    ∃ (a b : Fin n), a ≠ b ∧ ∃ c d : ZMod 3, c ≠ 0 ∧ d ≠ 0 ∧
      v = c • Pi.single a 1 + d • Pi.single b 1 := by
  unfold ggBCWt at h
  obtain ⟨a, b, hab, ha⟩ : ∃ a b : Fin n, a ≠ b ∧
      Finset.univ.filter (fun i => v i ≠ 0) = {a, b} := Finset.card_eq_two.mp h
  have hma : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hmb : b ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
  have hva : v a ≠ 0 := by simpa using hma
  have hvb : v b ≠ 0 := by simpa using hmb
  refine ⟨a, b, hab, v a, v b, hva, hvb, ?_⟩
  funext i
  by_cases hia : i = a
  · subst hia
    simp [Pi.single_eq_of_ne (Ne.symm hab), hab]
  · by_cases hib : i = b
    · subst hib
      simp [Pi.single_eq_of_ne hab, hab]
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia, hib]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, hvi]

private lemma ggQ2xQD_exists_repr {n : ℕ} (t : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ht : t ∈ ggDReflSet n) :
    ∃ (i j : Fin n) (e : ZMod 3) (hij : i ≠ j) (he : e ≠ 0),
      t = ggQ2xQD_ref i j e hij he := by
  obtain ⟨c, hcw, hc, rfl⟩ := ht
  obtain ⟨i, j, hij, a, b, ha, hb, hceq⟩ := ggQ2xQD_wt_two_repr hcw
  have he : b * a ≠ 0 := mul_ne_zero hb ha
  refine ⟨i, j, b * a, hij, he, ?_⟩
  have hvec : c = a • ggQ2xQD_vec i j (b * a) := by
    rw [hceq, ggQ2xQD_vec, smul_add, smul_smul]
    congr 1
    rw [show a * (b * a) = b by
      rw [mul_comm b a, ← mul_assoc, ggQ2x_mul_self_eq_one a ha, one_mul]]
  have hac : (a • ggQ2xQD_vec i j (b * a)) ⬝ᵥ (a • ggQ2xQD_vec i j (b * a)) ≠ 0 := by
    rw [ggQ2xQD_smul_norm ha]
    exact ggQ2xQD_vec_norm_ne hij he
  rw [ggQ2xQD_ref]
  exact (ggQ2xQD_refl_congr hvec hc hac).trans
    (ggQ2xQD_refl_smul a ha (ggQ2xQD_vec i j (b * a)) _ hac)

private def ggQ2xQD_nbhd {n : ℕ} (t : GGBCV n ≃ₗ[ZMod 3] GGBCV n) :
    Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  {r | r ∈ ggDReflSet n ∧ r * t = t * r}

private lemma ggQ2xQD_nbhd_determines {n : ℕ} (hn : 5 ≤ n)
    {t u : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (ht : t ∈ ggDReflSet n) (hu : u ∈ ggDReflSet n)
    (h : ggQ2xQD_nbhd t = ggQ2xQD_nbhd u) :
    ∃ (i j : Fin n) (e f : ZMod 3) (hij : i ≠ j) (he : e ≠ 0) (hf : f ≠ 0),
      t = ggQ2xQD_ref i j e hij he ∧ u = ggQ2xQD_ref i j f hij hf := by
  obtain ⟨i, j, e, hij, he, hteq⟩ := ggQ2xQD_exists_repr t ht
  obtain ⟨k, l, f, hkl, hf, hueq⟩ := ggQ2xQD_exists_repr u hu
  have hpair : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    by_contra hne
    by_cases hdis : i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l
    · obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j, k, l} : Finset (Fin n))) (t := Finset.univ)
        (by
          rw [Finset.card_fin]
          have h4 : ({i, j, k, l} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
          omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      have hmk : k ≠ m := Ne.symm hm.2.2.1
      have hmem : ggQ2xQD_ref k m 1 hmk (by decide) ∈ ggQ2xQD_nbhd t := by
        simp only [ggQ2xQD_nbhd, Set.mem_setOf_eq]
        refine ⟨ggQ2xQD_ref_mem k m 1 hmk (by decide), ?_⟩
        rw [hteq]
        rw [ggQ2xQD_ref_comm_iff hmk hij (by decide) he]
        exact Or.inl ⟨Ne.symm hdis.1, Ne.symm hdis.2.2.1, hm.1, hm.2.1⟩
      have hnotmem : ggQ2xQD_ref k m 1 hmk (by decide) ∉ ggQ2xQD_nbhd u := by
        simp only [ggQ2xQD_nbhd, Set.mem_setOf_eq]
        rintro ⟨-, hcomm⟩
        rw [hueq] at hcomm
        rw [ggQ2xQD_ref_comm_iff hmk hkl (by decide) hf] at hcomm
        rcases hcomm with hh | hh | hh
        · exact absurd rfl hh.1
        · exact hm.2.2.2 hh.2
        · exact hkl hh.1
      rw [h] at hmem
      exact hnotmem hmem
    · have hmem : ggQ2xQD_ref i j e hij he ∈ ggQ2xQD_nbhd t := by
        simp only [ggQ2xQD_nbhd, Set.mem_setOf_eq]
        exact ⟨ggQ2xQD_ref_mem i j e hij he, by rw [hteq]⟩
      have hnotmem : ggQ2xQD_ref i j e hij he ∉ ggQ2xQD_nbhd u := by
        simp only [ggQ2xQD_nbhd, Set.mem_setOf_eq]
        rintro ⟨-, hcomm⟩
        rw [hueq] at hcomm
        rw [ggQ2xQD_ref_comm_iff hij hkl he hf] at hcomm
        rcases hcomm with hh | hh | hh
        · exact hdis hh
        · exact hne (Or.inl hh)
        · exact hne (Or.inr hh)
      rw [h] at hmem
      exact hnotmem hmem
  rcases hpair with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
  · subst hik; subst hjl
    exact ⟨i, j, e, f, hij, he, hf, hteq, hueq⟩
  · subst hjk; subst hil
    exact ⟨i, j, e, f, hij, he, hf, hteq,
      hueq.trans (ggQ2xQD_ref_swap i j f hij hf)⟩

private lemma ggQ2xQD_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + p * d * q + q * d * (p + p * d * d) = r := by decide

private lemma ggQ2xQD_nat_eq_two_of_le_four {m : ℕ} (h4 : m ≤ 4) (h2 : (m : ZMod 3) = 2) :
    m = 2 := by
  interval_cases m
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · rfl
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

private lemma ggQ2xQD_refl_isometry {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (x y : GGBCV n) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := ggQ2xQD_zmod3_sq_eq_one hc
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm c x, dotProduct_comm c y]
  rw [ggQ2xQD_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggQ2xQD_refl_wt_two {n : ℕ} {a c : GGBCV n}
    (haw : ggBCWt a = 2) (hcw : ggBCWt c = 2)
    (ha : a ⬝ᵥ a ≠ 0) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCWt (ggBCRefl a ha c) = 2 := by
  have hnorm : (ggBCRefl a ha c) ⬝ᵥ (ggBCRefl a ha c) = 2 := by
    rw [ggQ2xQD_refl_isometry a ha c c, ggQ2x_dot_self_eq_wt, hcw]; decide
  have hbound : ggBCWt (ggBCRefl a ha c) ≤ 4 := by
    rw [ggQ2x_ggBCRefl_apply]
    unfold ggBCWt
    have hsub : (Finset.univ.filter
        (fun i => (c + (a ⬝ᵥ c * (a ⬝ᵥ a)) • a) i ≠ 0))
        ⊆ (Finset.univ.filter (fun i => a i ≠ 0)) ∪
          (Finset.univ.filter (fun i => c i ≠ 0)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hi ⊢
      by_cases ha0 : a i = 0
      · by_cases hc0 : c i = 0
        · exact absurd hi (by simp [ha0, hc0])
        · exact Or.inr hc0
      · exact Or.inl ha0
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le (Finset.univ.filter (fun i => a i ≠ 0))
      (Finset.univ.filter (fun i => c i ≠ 0))).trans ?_
    change ggBCWt a + ggBCWt c ≤ 4
    omega
  have hwmod : (ggBCWt (ggBCRefl a ha c) : ZMod 3) = 2 := by
    rw [← ggQ2x_dot_self_eq_wt]
    exact hnorm
  exact ggQ2xQD_nat_eq_two_of_le_four hbound hwmod

private lemma ggQ2xQD_conj_reflection {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {ψ : Dual K V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[K] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xQD_isReflLin_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (a t : V ≃ₗ[ZMod 3] V) (ht : IsReflLin t) : IsReflLin (a * t * a⁻¹) := by
  obtain ⟨cc, ψ, hψ, rfl⟩ := ht
  refine ⟨a cc, ψ.comp (a.symm : V →ₗ[ZMod 3] V), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hψ
  · rw [show a⁻¹ = a.symm from rfl]
    exact ggQ2xQD_conj_reflection a hψ

private lemma ggQ2xQD_conj_refl {n : ℕ} (g : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (hg : ∀ x y : GGBCV n, (g x) ⬝ᵥ (g y) = x ⬝ᵥ y)
    (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (hgc : (g c) ⬝ᵥ (g c) ≠ 0) :
    g * ggBCRefl c hc * g⁻¹ = ggBCRefl (g c) hgc := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsym : g (g⁻¹ v) = v := LinearEquiv.apply_symm_apply g v
  rw [hsym]
  have hv : (g c) ⬝ᵥ v = c ⬝ᵥ (g⁻¹ v) := by
    have h := hg c (g⁻¹ v)
    rwa [hsym] at h
  rw [hv, hg c c]

private lemma ggQ2xQD_ref_mem_W {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) : ggQ2xQD_ref i j e hij he ∈ ggBCW n := by
  rw [ggQ2xQD_ref]
  refine Subgroup.subset_closure ⟨ggQ2xQD_vec i j e, ?_, ggQ2xQD_vec_norm_ne hij he, rfl⟩
  simp only [ggBCRoots, Set.mem_setOf_eq, ggQ2xQD_vec_wt hij he]
  omega

private lemma ggQ2xQD_conj_mem {n : ℕ} {s t : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hs : s ∈ ggDReflSet n) (ht : t ∈ ggDReflSet n) :
    s * t * s⁻¹ ∈ ggDReflSet n := by
  obtain ⟨a, haw, ha, rfl⟩ := hs
  obtain ⟨c, hcw, hc, rfl⟩ := ht
  refine ⟨ggBCRefl a ha c, ggQ2xQD_refl_wt_two haw hcw ha hc, ?_, ?_⟩
  · rw [ggQ2xQD_refl_isometry a ha c c, ggQ2x_dot_self_eq_wt, hcw]; decide
  · exact ggQ2xQD_conj_refl (ggBCRefl a ha) (ggQ2xQD_refl_isometry a ha) c hc _

private lemma ggQ2xQD_comm_iff_of_quandle {G : Type} [Group G] (T : Set G)
    (hT : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T) (π : G → G)
    (hinj : Set.InjOn π T)
    (hπ : ∀ s ∈ T, ∀ t ∈ T, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {s t : G} (hs : s ∈ T) (ht : t ∈ T) :
    s * t = t * s ↔ π s * π t = π t * π s := by
  have e1 : ∀ a b : G, a * b = b * a ↔ a * b * a⁻¹ = b := fun a b => by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h]
  rw [e1, e1, ← hπ s hs t ht]
  exact ⟨fun h => by rw [h], fun h => hinj (hT s hs t ht) ht h⟩

private def ggQ2xQD_Param (n : ℕ) : Type :=
  {p : (Fin n × Fin n) × ZMod 3 // p.1.1 ≠ p.1.2 ∧ p.2 ≠ 0}

private noncomputable def ggQ2xQD_Phi {n : ℕ} (p : ggQ2xQD_Param n) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggQ2xQD_ref p.val.1.1 p.val.1.2 p.val.2 p.property.1 p.property.2

private lemma ggQ2xQD_range_Phi {n : ℕ} :
    Set.range (ggQ2xQD_Phi (n := n)) = ggDReflSet n := by
  apply Set.Subset.antisymm
  · rintro t ⟨p, rfl⟩
    exact ggQ2xQD_ref_mem p.val.1.1 p.val.1.2 p.val.2 p.property.1 p.property.2
  · intro t ht
    obtain ⟨i, j, e, hij, he, rfl⟩ := ggQ2xQD_exists_repr t ht
    exact ⟨⟨((i, j), e), ⟨hij, he⟩⟩, rfl⟩

private lemma ggQ2xQD_finite_T {n : ℕ} : (ggDReflSet n).Finite := by
  haveI : Finite (ggQ2xQD_Param n) := by
    unfold ggQ2xQD_Param
    infer_instance
  have h := Set.finite_range (ggQ2xQD_Phi (n := n))
  rwa [ggQ2xQD_range_Phi] at h

private lemma ggQ2xQD_surj {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n)
    (hinj : Set.InjOn π (ggDReflSet n)) :
    Set.SurjOn π (ggDReflSet n) (ggDReflSet n) := by
  have hfin := ggQ2xQD_finite_T (n := n)
  have hm : Set.MapsTo π (ggDReflSet n) (ggDReflSet n) := hπT
  exact ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin hm).mp hinj).2.2

private lemma ggQ2xQD_pi_comm_iff {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n)
    (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {s t : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (hs : s ∈ ggDReflSet n) (ht : t ∈ ggDReflSet n) :
    s * t = t * s ↔ π s * π t = π t * π s :=
  ggQ2xQD_comm_iff_of_quandle (ggDReflSet n) (fun s hs t ht => ggQ2xQD_conj_mem hs ht)
    π hinj hπ hs ht

private lemma ggQ2xQD_pi_nbhd {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n)
    (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    (hsurj : Set.SurjOn π (ggDReflSet n) (ggDReflSet n))
    {t : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (ht : t ∈ ggDReflSet n) :
    ggQ2xQD_nbhd (π t) = π '' ggQ2xQD_nbhd t := by
  apply Set.ext
  intro r
  constructor
  · intro hr
    obtain ⟨s, hsT, hEq⟩ := hsurj hr.1
    refine ⟨s, ⟨hsT, ?_⟩, hEq⟩
    have hr2 := hr.2
    rw [← hEq] at hr2
    exact (ggQ2xQD_pi_comm_iff π hπT hinj hπ hsT ht).mpr hr2
  · rintro ⟨s, hs, hEq⟩
    rw [← hEq]
    exact ⟨hπT s hs.1, (ggQ2xQD_pi_comm_iff π hπT hinj hπ hs.1 ht).mp hs.2⟩

private lemma ggQ2xQD_mul_ne_zero : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  decide

private lemma ggQ2xQD_neg_ne_zero : ∀ a : ZMod 3, a ≠ 0 → -a ≠ 0 := by decide

private lemma ggQ2xQD_ref_conj_vec {n : ℕ} (i j k : Fin n) (r s : ZMod 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hr : r ≠ 0) (hs : s ≠ 0) :
    ggQ2xQD_ref i j r hij hr (ggQ2xQD_vec j k s)
      = (-r) • ggQ2xQD_vec i k (-(r * s)) := by
  rcases ggQ2xQD_zmod3_cases_of_sq (ggQ2x_mul_self_eq_one r hr) with rfl | rfl
  · rw [ggQ2xQD_ref_apply, ggQ2xQD_vec_dot_vec]
    rw [if_neg hij, if_neg hik, if_pos rfl, if_neg hjk]
    ext m
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> fin_cases s <;> decide
  · rw [ggQ2xQD_ref_apply, ggQ2xQD_vec_dot_vec]
    rw [if_neg hij, if_neg hik, if_pos rfl, if_neg hjk]
    ext m
    simp only [ggQ2xQD_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> fin_cases s <;> decide

private lemma ggQ2xQD_ref_conj {n : ℕ} (i j k : Fin n) (r s : ZMod 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hr : r ≠ 0) (hs : s ≠ 0) :
    ggQ2xQD_ref i j r hij hr * ggQ2xQD_ref j k s hjk hs * (ggQ2xQD_ref i j r hij hr)⁻¹
      = ggQ2xQD_ref i k (-(r * s)) hik
          (ggQ2xQD_neg_ne_zero (r * s) (ggQ2xQD_mul_ne_zero r s hr hs)) := by
  have hmid : ggQ2xQD_ref j k s hjk hs
      = ggBCRefl (ggQ2xQD_vec j k s) (ggQ2xQD_vec_norm_ne hjk hs) := rfl
  rw [hmid]
  rw [ggQ2xQD_conj_refl (ggQ2xQD_ref i j r hij hr)
    (ggQ2xQD_refl_isometry (ggQ2xQD_vec i j r) (ggQ2xQD_vec_norm_ne hij hr))
    (ggQ2xQD_vec j k s) (ggQ2xQD_vec_norm_ne hjk hs)
    (by
      rw [ggQ2xQD_ref]
      rw [ggQ2xQD_refl_isometry (ggQ2xQD_vec i j r) (ggQ2xQD_vec_norm_ne hij hr)
        (ggQ2xQD_vec j k s) (ggQ2xQD_vec j k s)]
      exact ggQ2xQD_vec_norm_ne hjk hs)]
  simp only [ggQ2xQD_ref_conj_vec i j k r s hij hjk hik hr hs]
  exact ggQ2xQD_refl_smul (-r) (neg_ne_zero.mpr hr)
    (ggQ2xQD_vec i k (-(r * s))) _ _

private noncomputable def ggQ2xQDa_refT {n : ℕ} (i j : Fin n) (e : ZMod 3) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  if h : i ≠ j ∧ e ≠ 0 then ggQ2xQD_ref i j e h.1 h.2 else 1

private lemma ggQ2xQDa_refT_eq {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQDa_refT i j e = ggQ2xQD_ref i j e hij he :=
  dif_pos ⟨hij, he⟩

private lemma ggQ2xQDa_refT_mem {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) : ggQ2xQDa_refT i j e ∈ ggDReflSet n := by
  rw [ggQ2xQDa_refT_eq i j e hij he]
  exact ggQ2xQD_ref_mem i j e hij he

private lemma ggQ2xQDa_refT_swap {n : ℕ} (i j : Fin n) (e : ZMod 3) :
    ggQ2xQDa_refT j i e = ggQ2xQDa_refT i j e := by
  by_cases h : i ≠ j ∧ e ≠ 0
  · rw [ggQ2xQDa_refT_eq j i e (Ne.symm h.1) h.2, ggQ2xQDa_refT_eq i j e h.1 h.2,
      ggQ2xQD_ref_swap i j e h.1 h.2]
  · have h' : ¬ (j ≠ i ∧ e ≠ 0) := fun hh => h ⟨Ne.symm hh.1, hh.2⟩
    unfold ggQ2xQDa_refT
    rw [dif_neg h', dif_neg h]

private lemma ggQ2xQDa_ref_congr {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (hkl : k ≠ l) (he : e ≠ 0) (hf : f ≠ 0)
    (h1 : i = k) (h2 : j = l) (h3 : e = f) :
    ggQ2xQD_ref i j e hij he = ggQ2xQD_ref k l f hkl hf := by
  subst h1 h2 h3
  rfl

private lemma ggQ2xQDa_Pexists {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) (hij : i ≠ j) :
    ∃ p : (Fin n × Fin n) × ZMod 3,
      p.1.1 ≠ p.1.2 ∧ p.2 ≠ 0 ∧
        π (ggQ2xQDa_refT i j 1) = ggQ2xQDa_refT p.1.1 p.1.2 p.2 := by
  have ht : ggQ2xQDa_refT i j 1 ∈ ggDReflSet n :=
    ggQ2xQDa_refT_mem i j 1 hij one_ne_zero
  obtain ⟨k, l, e, hkl, he, hEq⟩ := ggQ2xQD_exists_repr _ (hπT _ ht)
  exact ⟨((k, l), e), hkl, he, by rw [hEq, ggQ2xQDa_refT_eq k l e hkl he]⟩

private noncomputable def ggQ2xQDa_wit {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) :
    (Fin n × Fin n) × ZMod 3 :=
  if hij : i ≠ j then Classical.choose (ggQ2xQDa_Pexists π hπT i j hij) else ((i, j), 1)

private noncomputable def ggQ2xQDa_P {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) : Fin n × Fin n :=
  (ggQ2xQDa_wit π hπT i j).1

private noncomputable def ggQ2xQDa_S {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) : ZMod 3 :=
  (ggQ2xQDa_wit π hπT i j).2

private lemma ggQ2xQDa_wit_spec {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) (hij : i ≠ j) :
    (ggQ2xQDa_P π hπT i j).1 ≠ (ggQ2xQDa_P π hπT i j).2 ∧
      ggQ2xQDa_S π hπT i j ≠ 0 ∧
      π (ggQ2xQDa_refT i j 1)
        = ggQ2xQDa_refT (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2
            (ggQ2xQDa_S π hπT i j) := by
  unfold ggQ2xQDa_P ggQ2xQDa_S ggQ2xQDa_wit
  rw [dif_pos hij]
  exact Classical.choose_spec (ggQ2xQDa_Pexists π hπT i j hij)

private lemma ggQ2xQDa_P_sym {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) {i j : Fin n} (hij : i ≠ j) :
    ((ggQ2xQDa_P π hπT j i).1 = (ggQ2xQDa_P π hπT i j).1 ∧
        (ggQ2xQDa_P π hπT j i).2 = (ggQ2xQDa_P π hπT i j).2) ∨
      ((ggQ2xQDa_P π hπT j i).1 = (ggQ2xQDa_P π hπT i j).2 ∧
        (ggQ2xQDa_P π hπT j i).2 = (ggQ2xQDa_P π hπT i j).1) := by
  have h1 := ggQ2xQDa_wit_spec π hπT i j hij
  have h2 := ggQ2xQDa_wit_spec π hπT j i (Ne.symm hij)
  have hEq : ggQ2xQDa_refT (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2
        (ggQ2xQDa_S π hπT i j)
      = ggQ2xQDa_refT (ggQ2xQDa_P π hπT j i).1 (ggQ2xQDa_P π hπT j i).2
        (ggQ2xQDa_S π hπT j i) := by
    rw [← h1.2.2, ← h2.2.2, ggQ2xQDa_refT_swap j i 1]
  rw [ggQ2xQDa_refT_eq _ _ _ h1.1 h1.2.1,
      ggQ2xQDa_refT_eq _ _ _ h2.1 h2.2.1] at hEq
  rcases (ggQ2xQD_ref_eq_iff h1.1 h2.1 h1.2.1 h2.2.1).mp hEq with ⟨hpair, -⟩
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨ha.symm, hb.symm⟩
  · exact Or.inr ⟨hb.symm, ha.symm⟩

private lemma ggQ2xQDa_nbhd_refT_eq {n : ℕ} (i j : Fin n) (e : ZMod 3)
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQD_nbhd (ggQ2xQDa_refT i j e) = ggQ2xQD_nbhd (ggQ2xQDa_refT i j 1) := by
  apply Set.ext
  intro r
  simp only [ggQ2xQD_nbhd, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hrT, hcomm⟩
    obtain ⟨k, l, f, hkl, hf, rfl⟩ := ggQ2xQD_exists_repr r hrT
    refine ⟨ggQ2xQD_ref_mem k l f hkl hf, ?_⟩
    rw [ggQ2xQDa_refT_eq i j e hij he, ggQ2xQD_ref_comm_iff hkl hij hf he] at hcomm
    rw [ggQ2xQDa_refT_eq i j 1 hij one_ne_zero,
      ggQ2xQD_ref_comm_iff hkl hij hf one_ne_zero]
    exact hcomm
  · rintro ⟨hrT, hcomm⟩
    obtain ⟨k, l, f, hkl, hf, rfl⟩ := ggQ2xQD_exists_repr r hrT
    refine ⟨ggQ2xQD_ref_mem k l f hkl hf, ?_⟩
    rw [ggQ2xQDa_refT_eq i j 1 hij one_ne_zero,
      ggQ2xQD_ref_comm_iff hkl hij hf one_ne_zero] at hcomm
    rw [ggQ2xQDa_refT_eq i j e hij he, ggQ2xQD_ref_comm_iff hkl hij hf he]
    exact hcomm

private lemma ggQ2xQDa_P_same_pair {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {i j : Fin n} (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0) :
    ∃ f : ZMod 3, f ≠ 0 ∧
      π (ggQ2xQDa_refT i j e)
        = ggQ2xQDa_refT (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 f := by
  have hsurj := ggQ2xQD_surj π hπT hinj
  have hmemE : ggQ2xQDa_refT i j e ∈ ggDReflSet n := ggQ2xQDa_refT_mem i j e hij he
  have hmem1 : ggQ2xQDa_refT i j 1 ∈ ggDReflSet n :=
    ggQ2xQDa_refT_mem i j 1 hij one_ne_zero
  have hnb : ggQ2xQD_nbhd (ggQ2xQDa_refT i j e) = ggQ2xQD_nbhd (ggQ2xQDa_refT i j 1) :=
    ggQ2xQDa_nbhd_refT_eq i j e hij he
  have hnbhd : ggQ2xQD_nbhd (π (ggQ2xQDa_refT i j e))
      = ggQ2xQD_nbhd (π (ggQ2xQDa_refT i j 1)) := by
    rw [ggQ2xQD_pi_nbhd π hπT hinj hπ hsurj hmemE,
        ggQ2xQD_pi_nbhd π hπT hinj hπ hsurj hmem1, hnb]
  obtain ⟨k, l, f1, f2, hkl, hf1, hf2, hEqE, hEq1⟩ :=
    ggQ2xQD_nbhd_determines hn (hπT _ hmemE) (hπT _ hmem1) hnbhd
  have hspec := ggQ2xQDa_wit_spec π hπT i j hij
  have hpair : (k = (ggQ2xQDa_P π hπT i j).1 ∧ l = (ggQ2xQDa_P π hπT i j).2) ∨
      (k = (ggQ2xQDa_P π hπT i j).2 ∧ l = (ggQ2xQDa_P π hπT i j).1) := by
    have hEq' : ggQ2xQD_ref k l f2 hkl hf2
        = ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2
            (ggQ2xQDa_S π hπT i j) hspec.1 hspec.2.1 := by
      calc ggQ2xQD_ref k l f2 hkl hf2
          = π (ggQ2xQDa_refT i j 1) := hEq1.symm
        _ = ggQ2xQDa_refT (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2
              (ggQ2xQDa_S π hπT i j) := hspec.2.2
        _ = ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2
              (ggQ2xQDa_S π hπT i j) hspec.1 hspec.2.1 :=
              ggQ2xQDa_refT_eq _ _ _ hspec.1 hspec.2.1
    exact (ggQ2xQD_ref_eq_iff hkl hspec.1 hf2 hspec.2.1).mp hEq' |>.1
  have hmain : ggQ2xQD_ref k l f1 hkl hf1
      = ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 f1
          hspec.1 hf1 := by
    rcases hpair with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · exact ggQ2xQDa_ref_congr hkl hspec.1 hf1 hf1 hk hl rfl
    · calc ggQ2xQD_ref k l f1 hkl hf1
          = ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).2 (ggQ2xQDa_P π hπT i j).1 f1
              (Ne.symm hspec.1) hf1 :=
              ggQ2xQDa_ref_congr hkl (Ne.symm hspec.1) hf1 hf1 hk hl rfl
        _ = ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 f1
              hspec.1 hf1 := ggQ2xQD_ref_swap _ _ f1 hspec.1 hf1
  refine ⟨f1, hf1, ?_⟩
  rw [hEqE, hmain, ggQ2xQDa_refT_eq _ _ _ hspec.1 hf1]

private lemma ggQ2xQDa_swap_image_pair {n : ℕ} (a b c d : Fin n) :
    ({c, d} : Finset (Fin n)).image (Equiv.swap a b)
      = ({Equiv.swap a b c, Equiv.swap a b d} : Finset (Fin n)) := by
  rw [Finset.image_insert, Finset.image_singleton]

private lemma ggQ2xQDa_refT_pair_eq {n : ℕ} {p q k l : Fin n} {t : ZMod 3}
    (hpq : p ≠ q) (hkl : k ≠ l)
    (h : ({p, q} : Finset (Fin n)) = {k, l}) :
    ggQ2xQDa_refT p q t = ggQ2xQDa_refT k l t := by
  have hp : p = k ∨ p = l := by
    have : p ∈ ({k, l} : Finset (Fin n)) := by rw [← h]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hp with hpk | hpl
  · have hql : q = l := by
      have hq : q = k ∨ q = l := by
        have : q ∈ ({k, l} : Finset (Fin n)) := by rw [← h]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      rcases hq with hqk | hql
      · exact absurd (hpk.trans hqk.symm) hpq
      · exact hql
    rw [hpk, hql]
  · have hqk : q = k := by
      have hq : q = k ∨ q = l := by
        have : q ∈ ({k, l} : Finset (Fin n)) := by rw [← h]; simp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using this
      rcases hq with hqk | hql
      · exact hqk
      · exact absurd (hpl.trans hql.symm) hpq
    rw [hpl, hqk, ggQ2xQDa_refT_swap k l t]

private lemma ggQ2xQDa_conj_pair {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (r s : ZMod 3) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ (p q : Fin n) (hpq : p ≠ q) (t : ZMod 3), t ≠ 0 ∧
      ggQ2xQD_ref a b r hab hr * ggQ2xQD_ref c d s hcd hs * (ggQ2xQD_ref a b r hab hr)⁻¹
        = ggQ2xQDa_refT p q t ∧
      ({p, q} : Finset (Fin n)) = ({c, d} : Finset (Fin n)).image (Equiv.swap a b) := by
  have hne : -(r * s) ≠ 0 := ggQ2xQD_neg_ne_zero (r * s) (ggQ2xQD_mul_ne_zero r s hr hs)
  by_cases hca : c = a
  · by_cases hdb : d = b
    ·
      have hcomm : ggQ2xQD_ref a b r hab hr * ggQ2xQD_ref c d s hcd hs
          = ggQ2xQD_ref c d s hcd hs * ggQ2xQD_ref a b r hab hr := by
        rw [ggQ2xQD_ref_comm_iff hab hcd hr hs]
        exact Or.inr (Or.inl ⟨hca.symm, hdb.symm⟩)
      refine ⟨c, d, hcd, s, hs, ?_, ?_⟩
      · rw [ggQ2xQDa_refT_eq c d s hcd hs, hcomm]
        group
      · rw [ggQ2xQDa_swap_image_pair, hca, hdb, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        exact Finset.pair_comm a b
    ·
      have hda : d ≠ a := fun h => hcd (by rw [hca, h])
      have had : a ≠ d := Ne.symm hda
      have hdb' : d ≠ b := hdb
      refine ⟨b, d, Ne.symm hdb', -(r * s), hne, ?_, ?_⟩
      · rw [ggQ2xQDa_refT_eq b d (-(r * s)) (Ne.symm hdb') hne,
          ggQ2xQDa_ref_congr hcd had hs hs hca rfl rfl,
          ← ggQ2xQD_ref_swap a b r hab hr]
        exact ggQ2xQD_ref_conj b a d r s (Ne.symm hab) had (Ne.symm hdb') hr hs
      · rw [ggQ2xQDa_swap_image_pair, hca, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hda hdb']
  · by_cases hcb : c = b
    · by_cases hda : d = a
      ·
        have hcomm : ggQ2xQD_ref a b r hab hr * ggQ2xQD_ref c d s hcd hs
            = ggQ2xQD_ref c d s hcd hs * ggQ2xQD_ref a b r hab hr := by
          rw [ggQ2xQD_ref_comm_iff hab hcd hr hs]
          exact Or.inr (Or.inr ⟨hda.symm, hcb.symm⟩)
        refine ⟨c, d, hcd, s, hs, ?_, ?_⟩
        · rw [ggQ2xQDa_refT_eq c d s hcd hs, hcomm]
          group
        · rw [ggQ2xQDa_swap_image_pair, hcb, hda, Equiv.swap_apply_right,
            Equiv.swap_apply_left]
          exact Finset.pair_comm b a
      ·
        have hdb : d ≠ b := fun h => hcd (by rw [hcb, h])
        have had : a ≠ d := Ne.symm hda
        have hbd : b ≠ d := Ne.symm hdb
        refine ⟨a, d, had, -(r * s), hne, ?_, ?_⟩
        · rw [ggQ2xQDa_refT_eq a d (-(r * s)) had hne,
            ggQ2xQDa_ref_congr hcd hbd hs hs hcb rfl rfl]
          exact ggQ2xQD_ref_conj a b d r s hab hbd had hr hs
        · rw [ggQ2xQDa_swap_image_pair, hcb, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne hda hdb]
    · by_cases hda : d = a
      ·
        have hac : a ≠ c := fun h => hca h.symm
        have hbc : b ≠ c := Ne.symm hcb
        have hdb : d ≠ b := fun h => hab (hda.symm.trans h)
        refine ⟨b, c, hbc, -(r * s), hne, ?_, ?_⟩
        · rw [ggQ2xQDa_refT_eq b c (-(r * s)) hbc hne,
            ggQ2xQDa_ref_congr hcd hca hs hs rfl hda rfl,
            ← ggQ2xQD_ref_swap c a s hca hs,
            ← ggQ2xQD_ref_swap a b r hab hr]
          exact ggQ2xQD_ref_conj b a c r s (Ne.symm hab) (Ne.symm hca) hbc hr hs
        · rw [ggQ2xQDa_swap_image_pair, hda, Equiv.swap_apply_left,
            Equiv.swap_apply_of_ne_of_ne hca hcb]
          exact Finset.pair_comm b c
      · by_cases hdb : d = b
        ·
          have hbc : b ≠ c := Ne.symm hcb
          have hac : a ≠ c := fun h => hca h.symm
          refine ⟨a, c, hac, -(r * s), hne, ?_, ?_⟩
          · rw [ggQ2xQDa_refT_eq a c (-(r * s)) hac hne,
              ggQ2xQDa_ref_congr hcd hcb hs hs rfl hdb rfl,
              ← ggQ2xQD_ref_swap c b s hcb hs]
            exact ggQ2xQD_ref_conj a b c r s hab hbc hac hr hs
          · rw [ggQ2xQDa_swap_image_pair, hdb, Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne hca hcb]
            exact Finset.pair_comm a c
        ·
          have hcomm : ggQ2xQD_ref a b r hab hr * ggQ2xQD_ref c d s hcd hs
              = ggQ2xQD_ref c d s hcd hs * ggQ2xQD_ref a b r hab hr := by
            rw [ggQ2xQD_ref_comm_iff hab hcd hr hs]
            exact Or.inl ⟨Ne.symm hca, Ne.symm hda, Ne.symm hcb, Ne.symm hdb⟩
          refine ⟨c, d, hcd, s, hs, ?_, ?_⟩
          · rw [ggQ2xQDa_refT_eq c d s hcd hs, hcomm]
            group
          · rw [ggQ2xQDa_swap_image_pair, Equiv.swap_apply_of_ne_of_ne hca hcb,
              Equiv.swap_apply_of_ne_of_ne hda hdb]

private lemma ggQ2xQDa_P_conj {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    ({ (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).1,
       (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).2 } : Finset (Fin n))
      = ({ (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
              (ggQ2xQDa_P π hπT k l).1,
           (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
              (ggQ2xQDa_P π hπT k l).2 } : Finset (Fin n)) := by
  have hskl : Equiv.swap i j k ≠ Equiv.swap i j l := (Equiv.swap i j).injective.ne hkl
  obtain ⟨p, q, hpq, t, ht, hconj, hpair⟩ :=
    ggQ2xQDa_conj_pair hij hkl (1 : ZMod 3) (1 : ZMod 3) one_ne_zero one_ne_zero
  have hconj' : ggQ2xQD_ref i j 1 hij one_ne_zero * ggQ2xQD_ref k l 1 hkl one_ne_zero
      * (ggQ2xQD_ref i j 1 hij one_ne_zero)⁻¹
      = ggQ2xQDa_refT (Equiv.swap i j k) (Equiv.swap i j l) t := by
    rw [hconj]
    exact ggQ2xQDa_refT_pair_eq hpq hskl
      (hpair.trans (ggQ2xQDa_swap_image_pair i j k l))
  obtain ⟨f, hf, hLHS⟩ := ggQ2xQDa_P_same_pair hn π hπT hinj hπ hskl t ht
  have hspec_ij := ggQ2xQDa_wit_spec π hπT i j hij
  have hspec_kl := ggQ2xQDa_wit_spec π hπT k l hkl
  obtain ⟨p', q', hp'q', t', ht', hconjG, hpair'⟩ :=
    ggQ2xQDa_conj_pair hspec_ij.1 hspec_kl.1 (ggQ2xQDa_S π hπT i j)
      (ggQ2xQDa_S π hπT k l) hspec_ij.2.1 hspec_kl.2.1
  have hRHS : π (ggQ2xQD_ref i j 1 hij one_ne_zero)
      * π (ggQ2xQD_ref k l 1 hkl one_ne_zero)
      * (π (ggQ2xQD_ref i j 1 hij one_ne_zero))⁻¹ = ggQ2xQDa_refT p' q' t' := by
    rw [← ggQ2xQDa_refT_eq i j 1 hij one_ne_zero,
        ← ggQ2xQDa_refT_eq k l 1 hkl one_ne_zero,
        hspec_ij.2.2, hspec_kl.2.2,
        ggQ2xQDa_refT_eq _ _ _ hspec_ij.1 hspec_ij.2.1,
        ggQ2xQDa_refT_eq _ _ _ hspec_kl.1 hspec_kl.2.1]
    exact hconjG
  have hEqT : ggQ2xQDa_refT (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).1
        (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).2 f
      = ggQ2xQDa_refT p' q' t' := by
    rw [← hLHS, ← hconj']
    rw [hπ _ (ggQ2xQD_ref_mem i j 1 hij one_ne_zero)
      _ (ggQ2xQD_ref_mem k l 1 hkl one_ne_zero)]
    exact hRHS
  have hspec_sk := ggQ2xQDa_wit_spec π hπT (Equiv.swap i j k) (Equiv.swap i j l) hskl
  have hEq : ggQ2xQD_ref (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).1
        (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).2 f
        hspec_sk.1 hf
      = ggQ2xQD_ref p' q' t' hp'q' ht' := by
    rw [← ggQ2xQDa_refT_eq _ _ _ hspec_sk.1 hf,
        ← ggQ2xQDa_refT_eq _ _ _ hp'q' ht']
    exact hEqT
  have hpairfin : ({p', q'} : Finset (Fin n)) =
      ({ (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).1,
         (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).2 } : Finset (Fin n)) :=
    hpair'.trans (ggQ2xQDa_swap_image_pair _ _ _ _)
  rw [← hpairfin]
  rcases (ggQ2xQD_ref_eq_iff hspec_sk.1 hp'q' hf ht').mp hEq with ⟨hord, -⟩
  rcases hord with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb]
    exact Finset.pair_comm q' p'

private lemma ggQ2xQDa_swap_eq_swap_iff {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b = Equiv.swap c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have hne : Equiv.swap c d a ≠ a := by
        rw [← h]
        exact Equiv.swap_apply_ne_self_iff.mpr ⟨hab, Or.inl rfl⟩
      exact Equiv.eq_or_eq_of_swap_apply_ne_self hne
    have hb : Equiv.swap c d a = b := by
      rw [← h]
      exact Equiv.swap_apply_left a b
    rcases ha with hac | had
    · refine Or.inl ⟨hac, ?_⟩
      rw [hac, Equiv.swap_apply_left] at hb
      exact hb.symm
    · refine Or.inr ⟨had, ?_⟩
      rw [had, Equiv.swap_apply_right] at hb
      exact hb.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Equiv.swap_comm a b

private lemma ggQ2xQDa_pair_eq_iff {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) :
    ({i, j} : Finset (Fin n)) = {k, l} ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hi : i = k ∨ i = l := by
      have : i ∈ ({k, l} : Finset (Fin n)) := by rw [← h]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hj : j = k ∨ j = l := by
      have : j ∈ ({k, l} : Finset (Fin n)) := by rw [← h]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hi with hik | hil
    · rcases hj with hjk | hjl
      · exact absurd (hik.trans hjk.symm) hij
      · exact Or.inl ⟨hik, hjl⟩
    · rcases hj with hjk | hjl
      · exact Or.inr ⟨hil, hjk⟩
      · exact absurd (hil.trans hjl.symm) hij
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm i j

private noncomputable def ggQ2xQDa_rep1 {n : ℕ} (t : Equiv.Perm (Fin n))
    (h : ∃ a b : Fin n, a ≠ b ∧ t = Equiv.swap a b) : Fin n := Classical.choose h

private noncomputable def ggQ2xQDa_rep2 {n : ℕ} (t : Equiv.Perm (Fin n))
    (h : ∃ a b : Fin n, a ≠ b ∧ t = Equiv.swap a b) : Fin n :=
  Classical.choose (Classical.choose_spec h)

private lemma ggQ2xQDa_rep_spec {n : ℕ} (t : Equiv.Perm (Fin n))
    (h : ∃ a b : Fin n, a ≠ b ∧ t = Equiv.swap a b) :
    ggQ2xQDa_rep1 t h ≠ ggQ2xQDa_rep2 t h ∧
      t = Equiv.swap (ggQ2xQDa_rep1 t h) (ggQ2xQDa_rep2 t h) :=
  Classical.choose_spec (Classical.choose_spec h)

private lemma ggQ2xQDa_swap_P_eq {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) {a b i j : Fin n}
    (hab : a ≠ b) (hij : i ≠ j) (h : Equiv.swap a b = Equiv.swap i j) :
    Equiv.swap (ggQ2xQDa_P π hπT a b).1 (ggQ2xQDa_P π hπT a b).2
      = Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 := by
  rcases (ggQ2xQDa_swap_eq_swap_iff hab hij).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    rcases ggQ2xQDa_P_sym π hπT hij with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact (Equiv.swap_comm _ _).symm

private noncomputable def ggQ2xQDa_pi' {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) :
    Equiv.Perm (Fin n) → Equiv.Perm (Fin n) :=
  fun t =>
    if h : ∃ a b : Fin n, a ≠ b ∧ t = Equiv.swap a b then
      Equiv.swap
        (ggQ2xQDa_P π hπT (ggQ2xQDa_rep1 t h) (ggQ2xQDa_rep2 t h)).1
        (ggQ2xQDa_P π hπT (ggQ2xQDa_rep1 t h) (ggQ2xQDa_rep2 t h)).2
    else t

private lemma ggQ2xQDa_pi'_swap {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (i j : Fin n) (hij : i ≠ j) :
    ggQ2xQDa_pi' π hπT (Equiv.swap i j)
      = Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 := by
  unfold ggQ2xQDa_pi'
  rw [dif_pos ⟨i, j, hij, rfl⟩]
  have hspec := ggQ2xQDa_rep_spec (Equiv.swap i j) ⟨i, j, hij, rfl⟩
  exact ggQ2xQDa_swap_P_eq π hπT hspec.1 hij hspec.2.symm

private lemma ggQ2xQDa_nbhd_eq_of_pair {n : ℕ} {i j k l : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (hkl : k ≠ l) (he : e ≠ 0) (hf : f ≠ 0)
    (h : ({i, j} : Finset (Fin n)) = {k, l}) :
    ggQ2xQD_nbhd (ggQ2xQD_ref i j e hij he)
      = ggQ2xQD_nbhd (ggQ2xQD_ref k l f hkl hf) := by
  rw [← ggQ2xQDa_refT_eq i j e hij he, ← ggQ2xQDa_refT_eq k l f hkl hf]
  calc ggQ2xQD_nbhd (ggQ2xQDa_refT i j e)
      = ggQ2xQD_nbhd (ggQ2xQDa_refT i j 1) := ggQ2xQDa_nbhd_refT_eq i j e hij he
    _ = ggQ2xQD_nbhd (ggQ2xQDa_refT k l 1) := by
          rw [ggQ2xQDa_refT_pair_eq hij hkl h]
    _ = ggQ2xQD_nbhd (ggQ2xQDa_refT k l f) := (ggQ2xQDa_nbhd_refT_eq k l f hkl hf).symm

private lemma ggQ2xQDa_pi'_T {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) :
    ∀ t ∈ ggTransp n, ggQ2xQDa_pi' π hπT t ∈ ggTransp n := by
  intro t ht
  obtain ⟨i, j, hij, rfl⟩ := ht
  rw [ggQ2xQDa_pi'_swap π hπT i j hij]
  exact ⟨_, _, (ggQ2xQDa_wit_spec π hπT i j hij).1, rfl⟩

private lemma ggQ2xQDa_pi'_inj {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    Set.InjOn (ggQ2xQDa_pi' π hπT) (ggTransp n) := by
  intro s hs t ht hst
  obtain ⟨i, j, hij, rfl⟩ := hs
  obtain ⟨k, l, hkl, rfl⟩ := ht
  rw [ggQ2xQDa_pi'_swap π hπT i j hij,
      ggQ2xQDa_pi'_swap π hπT k l hkl] at hst
  have hspec_ij := ggQ2xQDa_wit_spec π hπT i j hij
  have hspec_kl := ggQ2xQDa_wit_spec π hπT k l hkl
  have hpair : ({ (ggQ2xQDa_P π hπT i j).1, (ggQ2xQDa_P π hπT i j).2 } : Finset (Fin n))
      = { (ggQ2xQDa_P π hπT k l).1, (ggQ2xQDa_P π hπT k l).2 } := by
    rcases (ggQ2xQDa_swap_eq_swap_iff hspec_ij.1 hspec_kl.1).mp hst with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact (Finset.pair_comm _ _).symm
  have hmem1 : ggQ2xQDa_refT i j 1 ∈ ggDReflSet n :=
    ggQ2xQDa_refT_mem i j 1 hij one_ne_zero
  have hmem2 : ggQ2xQDa_refT k l 1 ∈ ggDReflSet n :=
    ggQ2xQDa_refT_mem k l 1 hkl one_ne_zero
  have hnbhd : ggQ2xQD_nbhd (π (ggQ2xQDa_refT i j 1))
      = ggQ2xQD_nbhd (π (ggQ2xQDa_refT k l 1)) := by
    rw [hspec_ij.2.2, hspec_kl.2.2,
        ggQ2xQDa_refT_eq _ _ _ hspec_ij.1 hspec_ij.2.1,
        ggQ2xQDa_refT_eq _ _ _ hspec_kl.1 hspec_kl.2.1]
    exact ggQ2xQDa_nbhd_eq_of_pair hspec_ij.1 hspec_kl.1 hspec_ij.2.1 hspec_kl.2.1 hpair
  have hsurj := ggQ2xQD_surj π hπT hinj
  have himg : π '' ggQ2xQD_nbhd (ggQ2xQDa_refT i j 1)
      = π '' ggQ2xQD_nbhd (ggQ2xQDa_refT k l 1) := by
    rw [← ggQ2xQD_pi_nbhd π hπT hinj hπ hsurj hmem1,
        ← ggQ2xQD_pi_nbhd π hπT hinj hπ hsurj hmem2]
    exact hnbhd
  have hnb : ggQ2xQD_nbhd (ggQ2xQDa_refT i j 1)
      = ggQ2xQD_nbhd (ggQ2xQDa_refT k l 1) :=
    (Set.InjOn.image_eq_image_iff hinj (fun x hx => hx.1) (fun x hx => hx.1)).mp himg
  obtain ⟨i', j', e, f, hi'j', he, hf, hti, htk⟩ :=
    ggQ2xQD_nbhd_determines hn hmem1 hmem2 hnb
  have hparij : ({i, j} : Finset (Fin n)) = {i', j'} := by
    have h1 : ggQ2xQD_ref i j 1 hij one_ne_zero = ggQ2xQD_ref i' j' e hi'j' he := by
      rw [← ggQ2xQDa_refT_eq i j 1 hij one_ne_zero]
      exact hti
    rcases ((ggQ2xQD_ref_eq_iff hij hi'j' one_ne_zero he).mp h1).1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact (Finset.pair_comm _ _).symm
  have hparkl : ({k, l} : Finset (Fin n)) = {i', j'} := by
    have h1 : ggQ2xQD_ref k l 1 hkl one_ne_zero = ggQ2xQD_ref i' j' f hi'j' hf := by
      rw [← ggQ2xQDa_refT_eq k l 1 hkl one_ne_zero]
      exact htk
    rcases ((ggQ2xQD_ref_eq_iff hkl hi'j' one_ne_zero hf).mp h1).1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact (Finset.pair_comm _ _).symm
  exact (ggQ2xQDa_swap_eq_swap_iff hij hkl).mpr
    ((ggQ2xQDa_pair_eq_iff hij hkl).mp (hparij.trans hparkl.symm))

private lemma ggQ2xQDa_pi'_conj {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∀ s ∈ ggTransp n, ∀ t ∈ ggTransp n,
      ggQ2xQDa_pi' π hπT (s * t * s⁻¹)
        = ggQ2xQDa_pi' π hπT s * ggQ2xQDa_pi' π hπT t * (ggQ2xQDa_pi' π hπT s)⁻¹ := by
  intro s hs t ht
  obtain ⟨i, j, hij, rfl⟩ := hs
  obtain ⟨k, l, hkl, rfl⟩ := ht
  have hskl : Equiv.swap i j k ≠ Equiv.swap i j l := (Equiv.swap i j).injective.ne hkl
  have hspec_kl := ggQ2xQDa_wit_spec π hπT k l hkl
  have hdist : (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
        (ggQ2xQDa_P π hπT k l).1
      ≠ (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
        (ggQ2xQDa_P π hπT k l).2 :=
    (Equiv.swap _ _).injective.ne hspec_kl.1
  have hL : Equiv.swap i j * Equiv.swap k l * (Equiv.swap i j)⁻¹
      = Equiv.swap (Equiv.swap i j k) (Equiv.swap i j l) :=
    (Equiv.swap_apply_apply (Equiv.swap i j) k l).symm
  rw [hL, ggQ2xQDa_pi'_swap π hπT i j hij,
      ggQ2xQDa_pi'_swap π hπT k l hkl,
      ggQ2xQDa_pi'_swap π hπT (Equiv.swap i j k) (Equiv.swap i j l) hskl,
      ← Equiv.swap_apply_apply]
  have hsk := ggQ2xQDa_wit_spec π hπT (Equiv.swap i j k) (Equiv.swap i j l) hskl
  have hord : ((ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).1
        = (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).1 ∧
      (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).2
        = (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).2) ∨
      ((ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).1
        = (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).2 ∧
      (ggQ2xQDa_P π hπT (Equiv.swap i j k) (Equiv.swap i j l)).2
        = (Equiv.swap (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2)
            (ggQ2xQDa_P π hπT k l).1) :=
    (ggQ2xQDa_pair_eq_iff hsk.1 hdist).mp (ggQ2xQDa_P_conj hn π hπT hinj hπ hij hkl)
  exact (ggQ2xQDa_swap_eq_swap_iff hsk.1 hdist).mpr hord

private lemma ggQ2xQD_exists_sigma {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
      ∃ (hij' : σ i ≠ σ j) (e' : ZMod 3) (he' : e' ≠ 0),
        π (ggQ2xQD_ref i j e hij he) = ggQ2xQD_ref (σ i) (σ j) e' hij' he' := by
  obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym n hn (ggQ2xQDa_pi' π hπT)
    (ggQ2xQDa_pi'_T π hπT) (ggQ2xQDa_pi'_inj hn π hπT hinj hπ)
    (ggQ2xQDa_pi'_conj hn π hπT hinj hπ)
  refine ⟨g, fun i j hij e he => ?_⟩
  have hspec_ij := ggQ2xQDa_wit_spec π hπT i j hij
  have hgij := hg (Equiv.swap i j) ⟨i, j, hij, rfl⟩
  rw [ggQ2xQDa_pi'_swap π hπT i j hij] at hgij
  have hgi : g i ≠ g j := fun h => hij (g.injective h)
  have hPij : ({ (ggQ2xQDa_P π hπT i j).1, (ggQ2xQDa_P π hπT i j).2 } : Finset (Fin n))
      = {g i, g j} := by
    rw [← Equiv.swap_apply_apply] at hgij
    rcases (ggQ2xQDa_swap_eq_swap_iff hspec_ij.1 hgi).mp hgij with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]
      exact (Finset.pair_comm _ _).symm
  have hord := (ggQ2xQDa_pair_eq_iff hspec_ij.1 hgi).mp hPij
  obtain ⟨f, hf, hfπ⟩ := ggQ2xQDa_P_same_pair hn π hπT hinj hπ hij e he
  refine ⟨hgi, f, hf, ?_⟩
  rw [← ggQ2xQDa_refT_eq i j e hij he, hfπ,
      ggQ2xQDa_refT_eq _ _ _ hspec_ij.1 hf]
  rcases hord with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ggQ2xQDa_ref_congr hspec_ij.1 hgi hf hf ha hb rfl
  · calc ggQ2xQD_ref (ggQ2xQDa_P π hπT i j).1 (ggQ2xQDa_P π hπT i j).2 f hspec_ij.1 hf
        = ggQ2xQD_ref (g j) (g i) f (Ne.symm hgi) hf :=
            ggQ2xQDa_ref_congr hspec_ij.1 (Ne.symm hgi) hf hf ha hb rfl
      _ = ggQ2xQD_ref (g i) (g j) f hgi hf := ggQ2xQD_ref_swap (g i) (g j) f hgi hf

private def ggQ2xQDb_Hσ {n : ℕ}
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
    ∃ (hij' : σ i ≠ σ j) (e' : ZMod 3) (he' : e' ≠ 0),
      π (ggQ2xQD_ref i j e hij he) = ggQ2xQD_ref (σ i) (σ j) e' hij' he'

private noncomputable def ggQ2xQDb_refT {n : ℕ} (i j : Fin n) (e : ZMod 3) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  if h : i ≠ j ∧ e ≠ 0 then ggQ2xQD_ref i j e h.1 h.2 else 1

private lemma ggQ2xQDb_refT_eq {n : ℕ} {i j : Fin n} {e : ZMod 3}
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQDb_refT i j e = ggQ2xQD_ref i j e hij he := by
  rw [ggQ2xQDb_refT, dif_pos (show i ≠ j ∧ e ≠ 0 from ⟨hij, he⟩)]

private lemma ggQ2xQDb_refT_eq_iff {n : ℕ} {i j : Fin n} {e f : ZMod 3}
    (hij : i ≠ j) (he : e ≠ 0) (hf : f ≠ 0) :
    ggQ2xQDb_refT i j e = ggQ2xQDb_refT i j f ↔ e = f := by
  rw [ggQ2xQDb_refT_eq hij he, ggQ2xQDb_refT_eq hij hf,
    ggQ2xQD_ref_eq_iff hij hij he hf]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Or.inl ⟨rfl, rfl⟩, h⟩

private lemma ggQ2xQDb_refT_swap {n : ℕ} {i j : Fin n} {e : ZMod 3}
    (hij : i ≠ j) (he : e ≠ 0) :
    ggQ2xQDb_refT j i e = ggQ2xQDb_refT i j e := by
  rw [ggQ2xQDb_refT_eq (Ne.symm hij) he, ggQ2xQDb_refT_eq hij he]
  exact ggQ2xQD_ref_swap i j e hij he

private lemma ggQ2xQDb_refT_conj {n : ℕ} {i j k : Fin n} {r s : ZMod 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hr : r ≠ 0) (hs : s ≠ 0) :
    ggQ2xQDb_refT i j r * ggQ2xQDb_refT j k s * (ggQ2xQDb_refT i j r)⁻¹
      = ggQ2xQDb_refT i k (-(r * s)) := by
  rw [ggQ2xQDb_refT_eq hij hr, ggQ2xQDb_refT_eq hjk hs,
    ggQ2xQDb_refT_eq hik (ggQ2xQD_neg_ne_zero (r * s) (ggQ2xQD_mul_ne_zero r s hr hs))]
  exact ggQ2xQD_ref_conj i j k r s hij hjk hik hr hs

private lemma ggQ2xQDb_sigma_ne {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    {i j : Fin n} (hij : i ≠ j) : σ i ≠ σ j :=
  Classical.choose (hσ i j hij 1 one_ne_zero)

private lemma ggQ2xQDb_eps_spec {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ e' : ZMod 3, e' ≠ 0 ∧
      π (ggQ2xQDb_refT i j 1) = ggQ2xQDb_refT (σ i) (σ j) e' := by
  obtain ⟨hij', e', he', heq⟩ := hσ i j hij 1 one_ne_zero
  exact ⟨e', he', by
    rw [ggQ2xQDb_refT_eq hij one_ne_zero, ggQ2xQDb_refT_eq hij' he']
    exact heq⟩

private noncomputable def ggQ2xQDb_eps {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ) (i j : Fin n) : ZMod 3 :=
  if h : i ≠ j then Classical.choose (ggQ2xQDb_eps_spec hσ i j h) else 1

private lemma ggQ2xQDb_eps_ne {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    {i j : Fin n} (hij : i ≠ j) : ggQ2xQDb_eps hσ i j ≠ 0 := by
  unfold ggQ2xQDb_eps
  rw [dif_pos hij]
  exact (Classical.choose_spec (ggQ2xQDb_eps_spec hσ i j hij)).1

private lemma ggQ2xQDb_eps_one {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    {i j : Fin n} (hij : i ≠ j) :
    π (ggQ2xQDb_refT i j 1) = ggQ2xQDb_refT (σ i) (σ j) (ggQ2xQDb_eps hσ i j) := by
  unfold ggQ2xQDb_eps
  rw [dif_pos hij]
  exact (Classical.choose_spec (ggQ2xQDb_eps_spec hσ i j hij)).2

private lemma ggQ2xQDb_eps_neg_one {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    (hinj : Set.InjOn π (ggDReflSet n)) {i j : Fin n} (hij : i ≠ j) :
    π (ggQ2xQDb_refT i j (-1))
      = ggQ2xQDb_refT (σ i) (σ j) (-(ggQ2xQDb_eps hσ i j)) := by
  obtain ⟨hij', e'', he'', heq⟩ := hσ i j hij (-1) (by decide)
  have hπu : π (ggQ2xQDb_refT i j (-1)) = ggQ2xQDb_refT (σ i) (σ j) e'' := by
    rw [ggQ2xQDb_refT_eq hij (by decide), ggQ2xQDb_refT_eq hij' he'']
    exact heq
  have hπw := ggQ2xQDb_eps_one hσ hij
  have hε : ggQ2xQDb_eps hσ i j ≠ 0 := ggQ2xQDb_eps_ne hσ hij
  have hne_uw : ggQ2xQDb_refT i j (-1) ≠ ggQ2xQDb_refT i j 1 := by
    intro h
    exact absurd ((ggQ2xQDb_refT_eq_iff hij (by decide) one_ne_zero).mp h) (by decide)
  have hmem_u : ggQ2xQDb_refT i j (-1) ∈ ggDReflSet n := by
    rw [ggQ2xQDb_refT_eq hij (by decide)]
    exact ggQ2xQD_ref_mem i j (-1) hij (by decide)
  have hmem_w : ggQ2xQDb_refT i j 1 ∈ ggDReflSet n := by
    rw [ggQ2xQDb_refT_eq hij one_ne_zero]
    exact ggQ2xQD_ref_mem i j 1 hij one_ne_zero
  have hne_pi : π (ggQ2xQDb_refT i j (-1)) ≠ π (ggQ2xQDb_refT i j 1) :=
    fun h => hne_uw (hinj hmem_u hmem_w h)
  have hne_e : e'' ≠ ggQ2xQDb_eps hσ i j := by
    intro h
    exact hne_pi (by rw [hπu, hπw, h])
  have heq_neg : e'' = -(ggQ2xQDb_eps hσ i j) :=
    ggQ2xQD_eq_neg_of_ne (ggQ2xQDb_eps hσ i j) e'' hε he'' (Ne.symm hne_e)
  rw [hπu, heq_neg]

private lemma ggQ2xQDb_neg_one_mul : ∀ a : ZMod 3, (-1 : ZMod 3) * a = -a := by decide

private lemma ggQ2xQDb_eps_any {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    (hinj : Set.InjOn π (ggDReflSet n)) {i j : Fin n} (hij : i ≠ j)
    (e : ZMod 3) (he : e ≠ 0) :
    π (ggQ2xQDb_refT i j e)
      = ggQ2xQDb_refT (σ i) (σ j) (e * ggQ2xQDb_eps hσ i j) := by
  rcases ggQ2xQD_zmod3_cases_of_sq (ggQ2x_mul_self_eq_one e he) with rfl | rfl
  · rw [one_mul]
    exact ggQ2xQDb_eps_one hσ hij
  · rw [ggQ2xQDb_eps_neg_one hσ hinj hij, ggQ2xQDb_neg_one_mul]

private lemma ggQ2xQDb_eps_symm {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    {i j : Fin n} (hij : i ≠ j) :
    ggQ2xQDb_eps hσ i j = ggQ2xQDb_eps hσ j i := by
  have hji : j ≠ i := Ne.symm hij
  have hσij : σ i ≠ σ j := ggQ2xQDb_sigma_ne hσ hij
  have hσji : σ j ≠ σ i := Ne.symm hσij
  have h1 := ggQ2xQDb_eps_one hσ hij
  have h2 := ggQ2xQDb_eps_one hσ hji
  have hεij : ggQ2xQDb_eps hσ i j ≠ 0 := ggQ2xQDb_eps_ne hσ hij
  have hεji : ggQ2xQDb_eps hσ j i ≠ 0 := ggQ2xQDb_eps_ne hσ hji
  have hswap : ggQ2xQDb_refT i j 1 = ggQ2xQDb_refT j i 1 :=
    (ggQ2xQDb_refT_swap hij one_ne_zero).symm
  have key : ggQ2xQDb_refT (σ i) (σ j) (ggQ2xQDb_eps hσ i j)
      = ggQ2xQDb_refT (σ j) (σ i) (ggQ2xQDb_eps hσ j i) := by
    rw [← h1, ← h2, hswap]
  rw [← ggQ2xQDb_refT_swap hσij hεij] at key
  exact (ggQ2xQDb_refT_eq_iff hσji hεij hεji).mp key

private lemma ggQ2xQDb_scal_cocycle : ∀ a b c : ZMod 3,
    -(a * b) = (-(1 * 1)) * c → c = a * b := by decide

private lemma ggQ2xQDb_eps_cocycle {n : ℕ}
    {π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n)}
    {σ : Equiv.Perm (Fin n)} (hσ : ggQ2xQDb_Hσ π σ)
    (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ggQ2xQDb_eps hσ i k = ggQ2xQDb_eps hσ i j * ggQ2xQDb_eps hσ j k := by
  have hσij : σ i ≠ σ j := ggQ2xQDb_sigma_ne hσ hij
  have hσjk : σ j ≠ σ k := ggQ2xQDb_sigma_ne hσ hjk
  have hσik : σ i ≠ σ k := ggQ2xQDb_sigma_ne hσ hik
  have hεij : ggQ2xQDb_eps hσ i j ≠ 0 := ggQ2xQDb_eps_ne hσ hij
  have hεjk : ggQ2xQDb_eps hσ j k ≠ 0 := ggQ2xQDb_eps_ne hσ hjk
  have hεik : ggQ2xQDb_eps hσ i k ≠ 0 := ggQ2xQDb_eps_ne hσ hik
  have hs : ggQ2xQDb_refT i j 1 ∈ ggDReflSet n := by
    rw [ggQ2xQDb_refT_eq hij one_ne_zero]
    exact ggQ2xQD_ref_mem i j 1 hij one_ne_zero
  have ht : ggQ2xQDb_refT j k 1 ∈ ggDReflSet n := by
    rw [ggQ2xQDb_refT_eq hjk one_ne_zero]
    exact ggQ2xQD_ref_mem j k 1 hjk one_ne_zero
  have hconj := ggQ2xQDb_refT_conj hij hjk hik one_ne_zero one_ne_zero
  have hπconj := hπ (ggQ2xQDb_refT i j 1) hs (ggQ2xQDb_refT j k 1) ht
  have himg := ggQ2xQDb_refT_conj hσij hσjk hσik hεij hεjk
  have hleft : π (ggQ2xQDb_refT i j 1 * ggQ2xQDb_refT j k 1
        * (ggQ2xQDb_refT i j 1)⁻¹)
      = ggQ2xQDb_refT (σ i) (σ j) (ggQ2xQDb_eps hσ i j)
        * ggQ2xQDb_refT (σ j) (σ k) (ggQ2xQDb_eps hσ j k)
        * (ggQ2xQDb_refT (σ i) (σ j) (ggQ2xQDb_eps hσ i j))⁻¹ := by
    rw [hπconj, ggQ2xQDb_eps_one hσ hij, ggQ2xQDb_eps_one hσ hjk]
  have hneg : (-(1 * 1) : ZMod 3) ≠ 0 := by decide
  have hkey : ggQ2xQDb_refT (σ i) (σ k)
        (-(ggQ2xQDb_eps hσ i j * ggQ2xQDb_eps hσ j k))
      = ggQ2xQDb_refT (σ i) (σ k) ((-(1 * 1)) * ggQ2xQDb_eps hσ i k) := by
    rw [← himg, ← hleft, congrArg π hconj,
      ggQ2xQDb_eps_any hσ hinj hik (-(1 * 1)) hneg]
  have hB : -(ggQ2xQDb_eps hσ i j * ggQ2xQDb_eps hσ j k) ≠ 0 :=
    ggQ2xQD_neg_ne_zero _ (ggQ2xQD_mul_ne_zero _ _ hεij hεjk)
  have hC : (-(1 * 1)) * ggQ2xQDb_eps hσ i k ≠ 0 :=
    ggQ2xQD_mul_ne_zero _ _ hneg hεik
  exact ggQ2xQDb_scal_cocycle _ _ _ ((ggQ2xQDb_refT_eq_iff hσik hB hC).mp hkey)

private lemma ggQ2xQD_exists_theta {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
      ∃ (hij' : σ i ≠ σ j) (e' : ZMod 3) (he' : e' ≠ 0),
        π (ggQ2xQD_ref i j e hij he) = ggQ2xQD_ref (σ i) (σ j) e' hij' he') :
    ∃ θ : Fin n → ZMod 3, (∀ i, θ i ≠ 0) ∧
      ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
        ∃ (hij' : σ i ≠ σ j) (he' : e * θ i * θ j ≠ 0),
          π (ggQ2xQD_ref i j e hij he)
            = ggQ2xQD_ref (σ i) (σ j) (e * θ i * θ j) hij' he' := by
  haveI : NeZero n := ⟨by omega⟩
  have hH : ggQ2xQDb_Hσ π σ := hσ
  have theta_spec : ∃ θ : Fin n → ZMod 3,
      (∀ i, θ i ≠ 0) ∧
        ∀ (i j : Fin n) (hij : i ≠ j), ggQ2xQDb_eps hH i j = θ i * θ j := by
    refine ⟨fun i => if _hi : i = (0 : Fin n) then 1 else ggQ2xQDb_eps hH 0 i, ?_, ?_⟩
    · intro i
      dsimp only
      by_cases hi : i = (0 : Fin n)
      · rw [dif_pos hi]; exact one_ne_zero
      · rw [dif_neg hi]
        exact ggQ2xQDb_eps_ne hH (fun h => hi h.symm)
    · intro i j hij
      dsimp only
      by_cases hi : i = (0 : Fin n)
      · have h0j : (0 : Fin n) ≠ j := fun h => hij (hi.trans h)
        have hj0 : j ≠ (0 : Fin n) := fun h => h0j h.symm
        rw [hi]
        simp [hj0]
      · by_cases hj : j = (0 : Fin n)
        · have hi0 : i ≠ (0 : Fin n) := hi
          rw [hj]
          rw [ggQ2xQDb_eps_symm (i := i) (j := (0 : Fin n)) hH hi0]
          simp [hi0]
        · have h0j : (0 : Fin n) ≠ j := fun h => hj h.symm
          have hcyc := ggQ2xQDb_eps_cocycle (i := i) (j := (0 : Fin n)) (k := j)
            hH hinj hπ hi h0j hij
          rw [hcyc, ggQ2xQDb_eps_symm (i := i) (j := (0 : Fin n)) hH hi]
          simp [hi, hj]
  obtain ⟨θ, hθne, hθmul⟩ := theta_spec
  refine ⟨θ, hθne, ?_⟩
  intro i j hij e he
  have hσij : σ i ≠ σ j := ggQ2xQDb_sigma_ne hH hij
  have he' : e * θ i * θ j ≠ 0 :=
    ggQ2xQD_mul_ne_zero (e * θ i) (θ j)
      (ggQ2xQD_mul_ne_zero e (θ i) he (hθne i)) (hθne j)
  refine ⟨hσij, he', ?_⟩
  have heps : e * ggQ2xQDb_eps hH i j = e * θ i * θ j := by
    rw [hθmul i j hij, mul_assoc]
  rw [← ggQ2xQDb_refT_eq hij he, ggQ2xQDb_eps_any hH hinj hij e he, heps,
    ggQ2xQDb_refT_eq hσij he']


private lemma ggQ2xQD_exists_sigma_theta {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n)
    (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ (σ : Equiv.Perm (Fin n)) (θ : Fin n → ZMod 3),
      (∀ i, θ i ≠ 0) ∧
        ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
          ∃ (hij' : σ i ≠ σ j) (he' : e * θ i * θ j ≠ 0),
            π (ggQ2xQD_ref i j e hij he)
              = ggQ2xQD_ref (σ i) (σ j) (e * θ i * θ j) hij' he' := by
  obtain ⟨σ, hσ⟩ := ggQ2xQD_exists_sigma hn π hπT hinj hπ
  obtain ⟨θ, hθ⟩ := ggQ2xQD_exists_theta hn π hπT hinj hπ σ hσ
  exact ⟨σ, θ, hθ⟩

private noncomputable def ggQ2xQD_diag {n : ℕ} (θ : Fin n → ZMod 3) (hθ : ∀ i, θ i ≠ 0) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n where
  toFun v := fun j => θ j * v j
  invFun v := fun j => θ j * v j
  left_inv v := by
    ext j
    show θ j * (θ j * v j) = v j
    rw [← mul_assoc, ggQ2x_mul_self_eq_one (θ j) (hθ j), one_mul]
  right_inv v := by
    ext j
    show θ j * (θ j * v j) = v j
    rw [← mul_assoc, ggQ2x_mul_self_eq_one (θ j) (hθ j), one_mul]
  map_add' u v := by
    ext j
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma ggQ2xQD_diag_isometry {n : ℕ} (θ : Fin n → ZMod 3) (hθ : ∀ i, θ i ≠ 0) :
    ∀ x y : GGBCV n, (ggQ2xQD_diag θ hθ x) ⬝ᵥ (ggQ2xQD_diag θ hθ y) = x ⬝ᵥ y := by
  intro x y
  rw [dotProduct, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  show (θ j * x j) * (θ j * y j) = x j * y j
  rw [show (θ j * x j) * (θ j * y j) = (θ j * θ j) * (x j * y j) by ring,
    ggQ2x_mul_self_eq_one (θ j) (hθ j), one_mul]

private lemma ggQ2xQD_neg_one_mul : ∀ a : ZMod 3, (-1 : ZMod 3) * a = -a := by decide

private lemma ggQ2xQD_neg_one_mul_neg : ∀ a : ZMod 3, (-1 : ZMod 3) * (-a) = a := by decide

private lemma ggQ2xQD_eq_one_or_neg_one : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide

private noncomputable def ggQ2xQD_short {n : ℕ} (i : Fin n) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (Pi.single i (1 : ZMod 3)) (by
    rw [ggQ2x_dot_self_eq_wt, ggQ2x_wt_single i]; decide)

private lemma ggQ2xQD_short_apply {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ggQ2xQD_short i v = v + (v i) • Pi.single i (1 : ZMod 3) := by
  rw [ggQ2xQD_short, ggQ2x_ggBCRefl_apply, ggQ2x_dot_self_eq_wt, ggQ2x_wt_single i,
    single_one_dotProduct]
  simp

private lemma ggQ2xQD_short_apply_self {n : ℕ} (i : Fin n) :
    ggQ2xQD_short i (Pi.single i (1 : ZMod 3)) = -Pi.single i (1 : ZMod 3) := by
  rw [ggQ2xQD_short_apply, Pi.single_eq_same, one_smul]
  ext j
  rw [Pi.add_apply, Pi.neg_apply]
  by_cases hj : j = i
  · subst hj; rw [Pi.single_eq_same]; decide
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj, zero_add]; rfl

private lemma ggQ2xQD_short_apply_of_ne {n : ℕ} (i j : Fin n) (hij : j ≠ i) :
    ggQ2xQD_short i (Pi.single j (1 : ZMod 3)) = Pi.single j (1 : ZMod 3) := by
  rw [ggQ2xQD_short_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij),
    zero_smul, add_zero]

private lemma ggQ2xQD_neg_one_smul {n : ℕ} (x : GGBCV n) :
    (-1 : ZMod 3) • x = -x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2xQD_neg_one_mul (x i)

private lemma ggQ2xQD_neg_one_smul_neg {n : ℕ} (x : GGBCV n) :
    (-1 : ZMod 3) • (-x) = x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2xQD_neg_one_mul_neg (x i)

private lemma ggQ2xQD_short_mem_W {n : ℕ} (i : Fin n) : ggQ2xQD_short i ∈ ggBCW n := by
  rw [ggQ2xQD_short]
  exact Subgroup.subset_closure
    ⟨_, (by
      rw [ggBCRoots]
      simp only [Set.mem_setOf_eq]
      rw [ggQ2x_wt_single i]
      decide), (by
      rw [ggQ2x_dot_self_eq_wt, ggQ2x_wt_single i]; decide), rfl⟩

private lemma ggQ2xQD_diag_single {n : ℕ} (θ : Fin n → ZMod 3) (hθ : ∀ i, θ i ≠ 0)
    (j : Fin n) :
    ggQ2xQD_diag θ hθ (Pi.single j (1 : ZMod 3)) = θ j • Pi.single j (1 : ZMod 3) := by
  ext k
  simp only [ggQ2xQD_diag, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hkj : k = j
  · subst hkj; simp
  · simp [hkj]

private lemma ggQ2xQD_diag_mem_W_aux {n : ℕ} (k : ℕ) :
    ∀ (S : Finset (Fin n)) (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n),
      S.card ≤ k →
      (∀ j, b (Pi.single j (1 : ZMod 3)) =
        (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) →
      b ∈ ggBCW n := by
  induction k with
  | zero =>
    intro S b hk hb
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
    subst hS
    have hb1 : b = 1 := by
      apply (Pi.basisFun (ZMod 3) (Fin n)).ext'
      intro j
      rw [Pi.basisFun_apply, hb j]
      simp
    rw [hb1]; exact (ggBCW n).one_mem
  | succ k ih =>
    intro S b hk hb
    by_cases hle : S.card ≤ k
    · exact ih S b hle hb
    · have hpos : 0 < S.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hcard : (S.erase i).card ≤ k := by
        rw [Finset.card_erase_of_mem hi]; omega
      have hb' : ∀ j, (ggQ2xQD_short i * b) (Pi.single j (1 : ZMod 3)) =
          (if j ∈ S.erase i then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3) := by
        intro j
        rw [LinearEquiv.mul_apply, hb j, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [if_pos hi, ggQ2xQD_short_apply_self, if_neg (by simp)]
          calc (-1 : ZMod 3) • (-Pi.single j (1 : ZMod 3)) = Pi.single j 1 :=
                ggQ2xQD_neg_one_smul_neg _
            _ = (1 : ZMod 3) • Pi.single j (1 : ZMod 3) := (one_smul _ _).symm
        · rw [ggQ2xQD_short_apply_of_ne i j hji]
          by_cases hjS : j ∈ S
          · rw [if_pos hjS, if_pos (by rw [Finset.mem_erase]; exact ⟨hji, hjS⟩)]
          · rw [if_neg hjS, if_neg (by rw [Finset.mem_erase]; exact fun h => hjS h.2)]
      have hmem : ggQ2xQD_short i * b ∈ ggBCW n :=
        ih (S.erase i) (ggQ2xQD_short i * b) hcard hb'
      have hb_eq : b = (ggQ2xQD_short i)⁻¹ * (ggQ2xQD_short i * b) := by group
      rw [hb_eq]
      exact mul_mem (inv_mem (ggQ2xQD_short_mem_W i)) hmem

private lemma ggQ2xQD_diag_mem_W {n : ℕ} (θ : Fin n → ZMod 3) (hθ : ∀ i, θ i ≠ 0) :
    ggQ2xQD_diag θ hθ ∈ ggBCW n := by
  refine ggQ2xQD_diag_mem_W_aux (Finset.univ.filter (fun j => θ j = -1)).card
    (Finset.univ.filter (fun j => θ j = -1)) (ggQ2xQD_diag θ hθ) le_rfl ?_
  intro j
  rw [ggQ2xQD_diag_single]
  by_cases hj : θ j = -1
  · rw [if_pos (by simp [hj]), hj]
  · rw [if_neg (by simp [hj])]
    have h1 : θ j = 1 := by
      rcases ggQ2xQD_eq_one_or_neg_one (θ j) (hθ j) with h | h
      · exact h
      · exact absurd h hj
    rw [h1]

private noncomputable def ggQ2xQD_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n where
  toFun v j := v (σ.symm j)
  invFun v j := v (σ j)
  map_add' x y := by ext j; simp [add_comm]
  map_smul' c x := by ext j; simp
  left_inv v := by ext j; simp
  right_inv v := by ext j; simp

@[simp] private lemma ggQ2xQD_perm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : GGBCV n)
    (j : Fin n) : ggQ2xQD_perm σ v j = v (σ.symm j) := rfl

private lemma ggQ2xQD_perm_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ggQ2xQD_perm σ (Pi.single i (1 : ZMod 3)) = Pi.single (σ i) (1 : ZMod 3) := by
  ext m
  simp only [ggQ2xQD_perm_apply, Pi.single_apply]
  by_cases h : σ.symm m = i
  · rw [if_pos h, if_pos]
    rw [← h, Equiv.apply_symm_apply]
  · rw [if_neg h, if_neg]
    intro hm
    exact h (by rw [hm, Equiv.symm_apply_apply])

private lemma ggQ2xQD_perm_isometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ x y : GGBCV n, (ggQ2xQD_perm σ x) ⬝ᵥ (ggQ2xQD_perm σ y) = x ⬝ᵥ y := by
  intro x y
  have hx : ggQ2xQD_perm σ x = x ∘ σ.symm := by ext j; rfl
  have hy : ggQ2xQD_perm σ y = y ∘ σ.symm := by ext j; rfl
  rw [hx, hy, dotProduct, dotProduct]
  exact Equiv.sum_comp σ.symm (fun i => x i * y i)

private lemma ggQ2xQD_perm_swap {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ggQ2xQD_perm (Equiv.swap x y)
      = ggBCRefl (Pi.single x 1 - Pi.single y 1)
          (by rw [ggQ2x_sub_single_norm x y hxy]; decide) := by
  ext v j
  rw [ggQ2x_refl_sub_single x y hxy]
  change v ((Equiv.swap x y).symm j) = v (Equiv.swap x y j)
  rw [Equiv.symm_swap]

private lemma ggQ2xQD_perm_swap_mem_W {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ggQ2xQD_perm (Equiv.swap x y) ∈ ggBCW n := by
  rw [ggQ2xQD_perm_swap x y hxy]
  exact Subgroup.subset_closure
    ⟨_, (by
      rw [ggBCRoots]
      simp only [Set.mem_setOf_eq]
      rw [ggQ2x_wt_sub_single x y hxy]
      decide), (by rw [ggQ2x_sub_single_norm x y hxy]; decide), rfl⟩

private lemma ggQ2xQD_perm_one {n : ℕ} : ggQ2xQD_perm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext v j; rfl

private lemma ggQ2xQD_perm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ggQ2xQD_perm (σ * τ) = ggQ2xQD_perm σ * ggQ2xQD_perm τ := by
  ext v j
  rw [LinearEquiv.mul_apply]
  change v ((σ * τ).symm j) = v (τ.symm (σ.symm j))
  rw [show (σ * τ).symm = τ.symm * σ.symm from mul_inv_rev σ τ]
  rfl

private lemma ggQ2xQD_perm_mem_W {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ggQ2xQD_perm σ ∈ ggBCW n := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [ggQ2xQD_perm_one]; exact (ggBCW n).one_mem
  · intro f x y hxy hf
    rw [ggQ2xQD_perm_mul]
    exact mul_mem (ggQ2xQD_perm_swap_mem_W x y hxy) hf

private lemma ggQ2xQD_perm_diag_vec {n : ℕ} (σ : Equiv.Perm (Fin n)) (θ : Fin n → ZMod 3)
    (hθ : ∀ i, θ i ≠ 0) (i j : Fin n) (e : ZMod 3) :
    (ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ) (ggQ2xQD_vec i j e)
      = θ i • ggQ2xQD_vec (σ i) (σ j) (e * θ i * θ j) := by
  rw [LinearEquiv.mul_apply]
  simp only [ggQ2xQD_vec, map_add, map_smul, ggQ2xQD_diag_single, ggQ2xQD_perm_single,
    smul_add, smul_smul]
  congr 1
  rw [show e * θ j = θ i * (e * θ i * θ j) by
    rw [show θ i * (e * θ i * θ j) = (θ i * θ i) * (e * θ j) by ring,
      ggQ2x_mul_self_eq_one (θ i) (hθ i), one_mul]]

private lemma ggQ2xQD_conj_diag_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (θ : Fin n → ZMod 3)
    (hθ : ∀ i, θ i ≠ 0) (i j : Fin n) (e : ZMod 3) (hij : i ≠ j) (he : e ≠ 0)
    (hij' : σ i ≠ σ j) (he' : e * θ i * θ j ≠ 0) :
    (ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ) * ggQ2xQD_ref i j e hij he
        * (ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ)⁻¹
      = ggBCRefl (ggQ2xQD_vec (σ i) (σ j) (e * θ i * θ j))
          (by rw [ggQ2xQD_vec_norm hij' he']; decide) := by
  have hg : ∀ x y : GGBCV n,
      ((ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ) x) ⬝ᵥ
        ((ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ) y) = x ⬝ᵥ y := by
    intro x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ggQ2xQD_perm_isometry σ, ggQ2xQD_diag_isometry θ hθ]
  have hcs : ggQ2xQD_ref i j e hij he
      = ggBCRefl (ggQ2xQD_vec i j e) (ggQ2xQD_vec_norm_ne hij he) := rfl
  rw [hcs]
  rw [ggQ2xQD_conj_refl (ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ) hg
    (ggQ2xQD_vec i j e) (ggQ2xQD_vec_norm_ne hij he)
    (by rw [hg (ggQ2xQD_vec i j e) (ggQ2xQD_vec i j e)]
        exact ggQ2xQD_vec_norm_ne hij he)]
  simp only [ggQ2xQD_perm_diag_vec σ θ hθ i j e]
  exact ggQ2xQD_refl_smul (θ i) (hθ i)
    (ggQ2xQD_vec (σ i) (σ j) (e * θ i * θ j)) _ _

private lemma ggQ2xQD_assemble {n : ℕ} (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n)
    (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    (σ : Equiv.Perm (Fin n)) (θ : Fin n → ZMod 3) (hθ : ∀ i, θ i ≠ 0)
    (hrel : ∀ (i j : Fin n) (hij : i ≠ j) (e : ZMod 3) (he : e ≠ 0),
      ∃ (hij' : σ i ≠ σ j) (he' : e * θ i * θ j ≠ 0),
        π (ggQ2xQD_ref i j e hij he)
          = ggQ2xQD_ref (σ i) (σ j) (e * θ i * θ j) hij' he') :
    ∃ g ∈ ggBCW n, ∀ t ∈ ggDReflSet n, π t = g * t * g⁻¹ := by
  refine ⟨ggQ2xQD_perm σ * ggQ2xQD_diag θ hθ,
    mul_mem (ggQ2xQD_perm_mem_W σ) (ggQ2xQD_diag_mem_W θ hθ), ?_⟩
  intro t ht
  obtain ⟨i, j, e, hij, he, rfl⟩ := ggQ2xQD_exists_repr t ht
  obtain ⟨hij', he', hπ⟩ := hrel i j hij e he
  rw [hπ]
  exact (ggQ2xQD_conj_diag_perm σ θ hθ i j e hij he hij' he').symm

theorem ggQ2_quandle_aut_D (n : ℕ) (hn : 5 ≤ n)
    (π : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) → (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hπT : ∀ t ∈ ggDReflSet n, π t ∈ ggDReflSet n) (hinj : Set.InjOn π (ggDReflSet n))
    (hπ : ∀ s ∈ ggDReflSet n, ∀ t ∈ ggDReflSet n, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ g ∈ ggBCW n, ∀ t ∈ ggDReflSet n, π t = g * t * g⁻¹ := by
  obtain ⟨σ, θ, hθ, hrel⟩ := ggQ2xQD_exists_sigma_theta hn π hπT hinj hπ
  exact ggQ2xQD_assemble hn π hπT hinj hπ σ θ hθ hrel

end CFSG.StandardType

end
