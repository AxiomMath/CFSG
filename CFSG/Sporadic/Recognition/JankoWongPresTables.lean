module

public import CFSG.Sporadic.Recognition.JankoWongPresInputs
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.McL CFSG.Sporadic.McL.Native
  CFSG.Sporadic.VecOrbit.Native

@[expose] noncomputable def jwGenE (neg : Bool) (k : ℕ) : J :=
  wordG genG (jwGenWord neg k)

@[expose] noncomputable def jwGen (neg : Bool) (i : Fin 6) : J :=
  jwGenE neg i.val

@[expose] noncomputable def jwImgG (neg : Bool) (z : ℤ) : J :=
  if 0 < z then jwGenE neg (z - 1).toNat else (jwGenE neg (-z - 1).toNat)⁻¹

theorem jwImgG_letterZ (neg : Bool) (l : Fin 6 × Bool) :
    jwImgG neg (jwLetterZ l) = if l.2 then jwGen neg l.1 else (jwGen neg l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [jwImgG, jwLetterZ, jwGen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [jwImgG, jwLetterZ, h0, hi, jwGen]

theorem wordG_jwImgG_map_letterZ (neg : Bool)
    (w : List (Fin 6 × Bool)) :
    wordG (jwImgG neg) (w.map jwLetterZ) = FreeGroup.lift (jwGen neg) (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      jwImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

abbrev jwT (neg : Bool) (k : ℕ) : Table := jwImg (orbitData ()) neg k

abbrev jwV (neg : Bool) (k : ℕ) : Table := invT 275 (jwT neg k)

abbrev jwL (neg : Bool) : ℤ → Table :=
  jwImgLetter (jwT neg 0) (jwT neg 1) (jwT neg 2) (jwT neg 3) (jwT neg 4) (jwT neg 5)
    (jwV neg 0) (jwV neg 1) (jwV neg 2) (jwV neg 3) (jwV neg 4) (jwV neg 5)

theorem rep_jwT (neg : Bool) (k : ℕ) :
    Rep 275 (jwT neg k) (jwGenE neg k) :=
  Rep.wordT (by norm_num) _ fun l _ => rep_gen l

theorem tab_facts (neg : Bool) (h : jwTabCheck neg = true) :
    (∀ k, k < 6 → invOK 275 (jwT neg k) (jwV neg k) = true) ∧
    (∀ r ∈ jwRels neg, wordT 275 (jwL neg) (r.map jwLetterZ) = idT 275) ∧
    wordT 275 (jwL neg) jwSurjA = (orbitData ()).alpha ∧
    wordT 275 (jwL neg) (jwSurjB neg) = (orbitData ()).beta := by
  unfold jwTabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun k hk => ?_, h6, h7, h8⟩
  interval_cases k
  exacts [h0, h1, h2, h3, h4, h5]

theorem jwImgLetter_vals (T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 : Table) :
    jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 1 = T0 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 2 = T1 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 3 = T2 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 4 = T3 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 5 = T4 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 6 = T5 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-1) = V0 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-2) = V1 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-3) = V2 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-4) = V3 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-5) = V4 ∧
      jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 (-6) = V5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rep_jwL (neg : Bool) (h : jwTabCheck neg = true) {z : ℤ}
    (hz0 : z ≠ 0) (hz : z.natAbs ≤ 6) : Rep 275 (jwL neg z) (jwImgG neg z) := by
  have hinv := (tab_facts neg h).1
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨ z = -4 ∨
      z = -5 ∨ z = -6 := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := jwImgLetter_vals (jwT neg 0)
    (jwT neg 1) (jwT neg 2) (jwT neg 3) (jwT neg 4) (jwT neg 5) (jwV neg 0) (jwV neg 1)
    (jwV neg 2) (jwV neg 3) (jwV neg 4) (jwV neg 5)
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show jwL neg 1 = jwT neg 0 from e1]; exact rep_jwT neg 0
  · rw [show jwL neg 2 = jwT neg 1 from e2]; exact rep_jwT neg 1
  · rw [show jwL neg 3 = jwT neg 2 from e3]; exact rep_jwT neg 2
  · rw [show jwL neg 4 = jwT neg 3 from e4]; exact rep_jwT neg 3
  · rw [show jwL neg 5 = jwT neg 4 from e5]; exact rep_jwT neg 4
  · rw [show jwL neg 6 = jwT neg 5 from e6]; exact rep_jwT neg 5
  · rw [show jwL neg (-1) = jwV neg 0 from e7]
    exact Rep.inv_of_invOK (rep_jwT neg 0) (hinv 0 (by norm_num))
  · rw [show jwL neg (-2) = jwV neg 1 from e8]
    exact Rep.inv_of_invOK (rep_jwT neg 1) (hinv 1 (by norm_num))
  · rw [show jwL neg (-3) = jwV neg 2 from e9]
    exact Rep.inv_of_invOK (rep_jwT neg 2) (hinv 2 (by norm_num))
  · rw [show jwL neg (-4) = jwV neg 3 from e10]
    exact Rep.inv_of_invOK (rep_jwT neg 3) (hinv 3 (by norm_num))
  · rw [show jwL neg (-5) = jwV neg 4 from e11]
    exact Rep.inv_of_invOK (rep_jwT neg 4) (hinv 4 (by norm_num))
  · rw [show jwL neg (-6) = jwV neg 5 from e12]
    exact Rep.inv_of_invOK (rep_jwT neg 5) (hinv 5 (by norm_num))

theorem eq_of_rep_eq {g h : J} {X : Table} (hg : Rep 275 X g)
    (hh : Rep 275 X h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := J) (α := Fin 275) fun i => ?_
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_jwImgG (neg : Bool) (h : jwTabCheck neg = true)
    (w : List (Fin 6 × Bool)) :
    Rep 275 (wordT 275 (jwL neg) (w.map jwLetterZ)) (wordG (jwImgG neg) (w.map jwLetterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_jwL neg h ?_ ?_
  · cases b <;> simp [jwLetterZ] <;> omega
  · cases b <;> simp [jwLetterZ] <;> omega

theorem lift_jwGen_eq_one (neg : Bool) (h : jwTabCheck neg = true)
    {w : List (Fin 6 × Bool)} (hw : w ∈ jwRels neg) :
    FreeGroup.lift (jwGen neg) (FreeGroup.mk w) = 1 := by
  have h1 := (tab_facts neg h).2.1 w hw
  have hr := rep_wordG_jwImgG neg h w
  rw [h1] at hr
  rw [← wordG_jwImgG_map_letterZ]
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem lift_jwGen_mem_closure (neg : Bool) (v : FreeGroup (Fin 6)) :
    FreeGroup.lift (jwGen neg) v ∈ Subgroup.closure (Set.range (jwGen neg)) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_jwGen (neg : Bool) (h : jwTabCheck neg = true) :
    Subgroup.closure (Set.range (jwGen neg)) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hA : a = FreeGroup.lift (jwGen neg) (FreeGroup.mk (jwOfCodes jwSurjACodes)) := by
    rw [← wordG_jwImgG_map_letterZ]
    have hr := rep_wordG_jwImgG neg h (jwOfCodes jwSurjACodes)
    rw [show (jwOfCodes jwSurjACodes).map jwLetterZ = jwSurjA from rfl,
      (tab_facts neg h).2.2.1] at hr
    exact eq_of_rep_eq rep_alpha hr
  have hB : b = FreeGroup.lift (jwGen neg) (FreeGroup.mk (jwOfCodes (jwSurjBCodes neg))) := by
    rw [← wordG_jwImgG_map_letterZ]
    have hr := rep_wordG_jwImgG neg h (jwOfCodes (jwSurjBCodes neg))
    rw [show (jwOfCodes (jwSurjBCodes neg)).map jwLetterZ = jwSurjB neg from rfl,
      (tab_facts neg h).2.2.2] at hr
    exact eq_of_rep_eq rep_beta hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_jwGen_mem_closure neg _
  · rw [hB]; exact lift_jwGen_mem_closure neg _

end CFSG.Sporadic.Recognition.JankoWong
