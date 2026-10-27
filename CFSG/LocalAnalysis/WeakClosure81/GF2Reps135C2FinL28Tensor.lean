module

import CFSG.RankThree.PartTwo.KFacts.KS116ProofSubfield
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem finL28_frobTensor_uElt_one_apply {F : Type} [Field F] {E : Type} [Field E] [CharP E 2]
    [Algebra F E] (J : Finset ℕ) (x y : J → Fin 2) :
    frobTensor F E J (uElt (1 : F)) (Pi.single x (1 : E)) y = if y ≤ x then 1 else 0 := by
  rw [frobTensor, tensorRep_apply, Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, mul_one]
    have hprod : (∏ i : J, twistMat E ((i : ℕ)) (uElt (1 : F)) (y i) (x i)) =
        ∏ i : J, (if y i ≤ x i then (1 : E) else 0) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [twistMat_uElt]
      rcases fin2_cases (y i) with hy | hy <;> rcases fin2_cases (x i) with hx | hx <;>
        simp [hy, hx]
    rw [show tmatE E (fun i : J => (i : ℕ)) (uElt (1 : F)) y x =
        ∏ i : J, twistMat E ((i : ℕ)) (uElt (1 : F)) (y i) (x i) from rfl, hprod,
      Fintype.prod_boole]
    by_cases h : y ≤ x
    · rw [if_pos h, if_pos (Pi.le_def.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (Pi.le_def.mpr hh))]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

theorem finL28_four_le_finrank_range_uElt {F : Type} [Field F] {E : Type} [Field E] [CharP E 2]
    [Algebra F E] :
    4 ≤ Module.finrank E
      (LinearMap.range (frobTensor F E ({0, 1, 2} : Finset ℕ) (uElt (1 : F)) - 1)) := by
  classical
  let J : Finset ℕ := {0, 1, 2}
  let top : J → Fin 2 := fun _ => 1
  let xa : J → (J → Fin 2) := fun a => fun i => if i = a then 0 else 1
  let delta : J → (J → Fin 2) := fun b => fun i => if i = b then 1 else 0
  let b0 : J := ⟨0, by simp [J]⟩
  let w : Option J → ((J → Fin 2) → E) := fun o =>
    match o with
    | none => (frobTensor F E J (uElt (1 : F)) - 1) (Pi.single top (1 : E))
    | some a => (frobTensor F E J (uElt (1 : F)) - 1) (Pi.single (xa a) (1 : E))
  have hw_none : w none =
      (frobTensor F E J (uElt (1 : F)) - 1) (Pi.single top (1 : E)) := rfl
  have hw_some : ∀ a : J, w (some a) =
      (frobTensor F E J (uElt (1 : F)) - 1) (Pi.single (xa a) (1 : E)) := fun _ => rfl
  have hN : ∀ x y : J → Fin 2,
      ((frobTensor F E J (uElt (1 : F)) - 1) (Pi.single x (1 : E))) y =
        if y < x then 1 else 0 := by
    intro x y
    change (frobTensor F E J (uElt (1 : F)) (Pi.single x (1 : E))) y -
      (Pi.single x (1 : E) : (J → Fin 2) → E) y = if y < x then 1 else 0
    rw [finL28_frobTensor_uElt_one_apply, Pi.single_apply]
    by_cases hyx : y = x
    · subst hyx
      simp
    · rw [if_neg hyx]
      by_cases hle : y ≤ x
      · have hlt : y < x := lt_of_le_of_ne hle hyx
        simp [hle, hlt]
      · have hlt : ¬ y < x := fun hh => hle hh.le
        simp [hle, hlt]
  have hcardJ : Fintype.card J = 3 := by simp [J]
  have hlt_card : 1 < Fintype.card J := by rw [hcardJ]; norm_num
  have hle_top : ∀ y : J → Fin 2, y ≤ top := by
    intro y i
    rcases fin2_cases (y i) with h | h <;> simp [top, h]
  have hxa_top : ∀ b : J, xa b < top := by
    intro b
    rw [lt_iff_le_and_ne]
    refine ⟨hle_top _, ?_⟩
    intro h
    have hb := congrFun h b
    simp [xa, top] at hb
  have hxa_xa : ∀ a b : J, ¬ (xa b < xa a) := by
    intro a b h
    rw [lt_iff_le_and_ne] at h
    obtain ⟨hle, hne⟩ := h
    have ha : xa b a ≤ xa a a := hle a
    have hza : xa a a = 0 := by simp [xa]
    rw [hza] at ha
    by_cases hab : a = b
    · exact hne (by subst hab; rfl)
    · have hb1 : xa b a = 1 := by simp [xa, hab, Ne.symm hab]
      rw [hb1] at ha
      exact absurd ha (by decide)
  have hzero_top : (0 : J → Fin 2) < top := by
    rw [lt_iff_le_and_ne]
    refine ⟨hle_top _, ?_⟩
    intro h
    have hb := congrFun h b0
    simp [top] at hb
  have hzero_xa : ∀ a : J, (0 : J → Fin 2) < xa a := by
    intro a
    rw [lt_iff_le_and_ne]
    refine ⟨fun i => Fin.zero_le _, ?_⟩
    intro h
    obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card hlt_card a
    have h1 : xa a i = 1 := by simp [xa, hi, Ne.symm hi]
    have h2 := congrFun h i
    rw [h1] at h2
    change (0 : Fin 2) = 1 at h2
    exact absurd h2 (by decide)
  have hdelta_top : ∀ b : J, delta b < top := by
    intro b
    rw [lt_iff_le_and_ne]
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hib : i = b
      · subst hib; simp [delta, top]
      · simp [delta, hib, Fin.zero_le]
    · intro h
      obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card hlt_card b
      have h0 : delta b i = 0 := by simp [delta, hi]
      have h2 := congrFun h i
      rw [h0] at h2
      change (0 : Fin 2) = 1 at h2
      exact absurd h2 (by decide)
  have hdelta_xa : ∀ a b : J, delta b < xa a ↔ a ≠ b := by
    intro a b
    rw [lt_iff_le_and_ne]
    constructor
    · rintro ⟨hle, _⟩ hab
      have hb := hle b
      have h1 : delta b b = 1 := by simp [delta]
      rw [h1] at hb
      have h0 : xa a b = 0 := by
        simp only [xa]
        rw [if_pos hab.symm]
      rw [h0] at hb
      exact absurd hb (by simp only [Fin.le_def]; norm_num)
    · intro hab
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hib : i = b
        · rw [hib]
          have hba : b ≠ a := fun h => hab h.symm
          simp [delta, xa, hba]
        · simp [delta, hib, Fin.zero_le]
      · intro h
        have hcard_erase : 1 < (J.erase a).card := by
          rw [Finset.card_erase_of_mem a.2]
          simp [J]
        obtain ⟨i, hi_mem, hi_ne⟩ := Finset.exists_mem_ne hcard_erase (b : ℕ)
        have hiJ : i ∈ J := (Finset.mem_erase.mp hi_mem).2
        have hi_a : i ≠ (a : ℕ) := (Finset.mem_erase.mp hi_mem).1
        let iJ : J := ⟨i, hiJ⟩
        have hiJ_a : iJ ≠ a := fun hh => hi_a (congrArg Subtype.val hh)
        have hiJ_b : iJ ≠ b := fun hh => hi_ne (congrArg Subtype.val hh)
        have h1 : delta b iJ = 0 := by simp [delta, hiJ_b]
        have h2 : xa a iJ = 1 := by simp [xa, hiJ_a, Ne.symm hiJ_a]
        have h3 := congrFun h iJ
        rw [h1, h2] at h3
        exact absurd h3 (by decide)
  have hw : LinearIndependent E w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc_apply : ∀ y : J → Fin 2, ∑ i : Option J, c i * w i y = 0 := by
      intro y
      have h1 := congrFun hc y
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h1
    have hc_none : c none = 0 := by
      have h1 := hc_apply (xa b0)
      rw [Fintype.sum_eq_single none] at h1
      · rw [hw_none, hN top (xa b0), if_pos (hxa_top b0), mul_one] at h1
        exact h1
      · intro i hi
        cases i with
        | none => exact absurd rfl hi
        | some a => rw [hw_some, hN (xa a) (xa b0), if_neg (hxa_xa a b0), mul_zero]
    have hS : (∑ a : J, c (some a)) = 0 := by
      have h1 := hc_apply (0 : J → Fin 2)
      rw [Fintype.sum_option] at h1
      have h2 : ∀ a : J, c (some a) * w (some a) 0 = c (some a) := by
        intro a
        rw [hw_some, hN (xa a) 0, if_pos (hzero_xa a), mul_one]
      rw [hw_none, hN top 0, if_pos hzero_top, mul_one, hc_none, zero_add] at h1
      simp only [h2] at h1
      exact h1
    have hcb : ∀ b : J, c (some b) = 0 := by
      intro b
      have hT : (∑ a : J, (if a ≠ b then c (some a) else 0)) = 0 := by
        have h1 := hc_apply (delta b)
        rw [Fintype.sum_option] at h1
        have h2 : ∀ a : J, c (some a) * w (some a) (delta b) =
            (if a ≠ b then c (some a) else 0) := by
          intro a
          rw [hw_some, hN (xa a) (delta b)]
          by_cases hab : a ≠ b
          · rw [if_pos ((hdelta_xa a b).mpr hab), if_pos hab]
            simp
          · rw [if_neg (fun hh => hab ((hdelta_xa a b).mp hh)), if_neg hab]
            simp
        rw [hw_none, hN top (delta b), if_pos (hdelta_top b), mul_one,
          hc_none, zero_add] at h1
        simp only [h2] at h1
        exact h1
      have hsplit : (∑ a : J, c (some a)) =
          c (some b) + ∑ a : J, (if a ≠ b then c (some a) else 0) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
        congr 1
        rw [← Finset.filter_ne' (Finset.univ) b, Finset.sum_filter]
      rw [hS, hT, add_zero] at hsplit
      exact hsplit.symm
    intro i
    cases i with
    | none => exact hc_none
    | some b => exact hcb b
  have hmem : ∀ i : Option J, w i ∈ LinearMap.range (frobTensor F E J (uElt (1 : F)) - 1) := by
    intro i
    cases i with
    | none => exact LinearMap.mem_range_self _ _
    | some a => exact LinearMap.mem_range_self _ _
  have hspan : Submodule.span E (Set.range w) ≤
      LinearMap.range (frobTensor F E J (uElt (1 : F)) - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hcard : Fintype.card (Option J) = 4 := by
    rw [Fintype.card_option]
    simp [J]
  calc 4 = Fintype.card (Option J) := hcard.symm
    _ = Module.finrank E (Submodule.span E (Set.range w)) :=
        (finrank_span_eq_card hw).symm
    _ ≤ Module.finrank E (LinearMap.range (frobTensor F E J (uElt (1 : F)) - 1)) :=
        Submodule.finrank_mono hspan

theorem finL28_four_le_finrank_range_involution {F : Type} [Field F] [Fintype F] [CharP F 2]
    {E : Type} [Field E] [CharP E 2] [Algebra F E] {h : SL(2, F)} (hh : h * h = 1) (h1 : h ≠ 1) :
    4 ≤ Module.finrank E
      (LinearMap.range (frobTensor F E ({0, 1, 2} : Finset ℕ) h - 1)) := by
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartTwo.KFacts.KS116Proof.exists_conj_eq_uu_one hh h1
  have huu : CFSG.RankThree.PartTwo.KFacts.KS116Proof.uu (1 : F) = uElt (1 : F) :=
    Subtype.ext rfl
  have hP' : h = P * uElt (1 : F) * P⁻¹ := by rw [hP, huu]
  let V := (({0, 1, 2} : Finset ℕ) → Fin 2) → E
  let T : Representation E SL(2, F) V := frobTensor F E ({0, 1, 2} : Finset ℕ)
  have hC : T P⁻¹ * T P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hC' : T P * T P⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hsurj : LinearMap.range (T P⁻¹) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨T P y, by rw [← Module.End.mul_apply, hC, Module.End.one_apply]⟩
  have hsub : T h - 1 = T P * (T (uElt (1 : F)) - 1) * T P⁻¹ := by
    rw [hP', map_mul, map_mul, mul_sub, sub_mul, mul_one, hC']
  have hrange : LinearMap.range (T h - 1) =
      Submodule.map (T P) (LinearMap.range (T (uElt (1 : F)) - 1)) := by
    rw [hsub]
    rw [show T P * (T (uElt (1 : F)) - 1) * T P⁻¹ =
        (T P).comp ((T (uElt (1 : F)) - 1).comp (T P⁻¹)) from rfl]
    rw [LinearMap.range_comp]
    congr 1
    rw [LinearMap.range_comp (T P⁻¹) (T (uElt (1 : F)) - 1), hsurj, Submodule.map_top]
  let e : V ≃ₗ[E] V := LinearEquiv.ofLinearMap (T P) (T P⁻¹) hC' hC
  have hfin : Module.finrank E (Submodule.map (T P) (LinearMap.range (T (uElt (1 : F)) - 1))) =
      Module.finrank E (LinearMap.range (T (uElt (1 : F)) - 1)) :=
    e.finrank_map_eq (LinearMap.range (T (uElt (1 : F)) - 1))
  have h4 := finL28_four_le_finrank_range_uElt (F := F) (E := E)
  rw [hrange, hfin]
  exact h4

end CFSG.LocalAnalysis.WeakClosure81
