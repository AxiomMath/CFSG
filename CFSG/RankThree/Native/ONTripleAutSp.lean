
module

public import CFSG.RankThree.Native.ONTripleAutSpBase

public import CFSG.RankThree.Native.ONTripleAutData
public import CFSG.RankThree.Native.ONTripleNorm
public import CFSG.RankThree.Native.ONTripleA6
public meta import CFSG.RankThree.Native.ONTripleNorm
public meta import CFSG.RankThree.Native.ONTripleAutData
public meta import CFSG.RankThree.Native.ONTripleA6
public import CFSG.RankThree.Native.ONTripleAutSpInputs
public import Certificates.Certificate8138

public section

namespace CFSG.RankThree.Native.ONTriple

open Equiv

theorem r0_check : r0Check = true :=
  Certificates.certificate8138.1

theorem r0_parts : R0codes.length = 320 ∧ R0words.length = 320 ∧
    (∀ i < 320, (R0words.getD i []).foldl (fun a k => amul a (if k = 0 then M0A else M1A)) idA =
      (R0codes.getD i []).toArray) ∧
    (∀ l ∈ R0codes, l.length = 16 ∧ ∀ x ∈ l, x < 3) ∧ (∀ w ∈ R0words, ∀ k ∈ w, k < 2) := by
  have h := r0_check
  simp only [r0Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem r0_valid
    {l : List ℕ} (hl : l ∈ R0codes) : ValidA l.toArray :=
  validA_toArray (r0_parts.2.2.2.1 l hl).1 (r0_parts.2.2.2.1 l hl).2

theorem memA_iff
    {a : Array ℕ} (ha : ValidA a) : memA a = true ↔ decA a ∈ R0list := by
  rw [memA, List.contains_iff_mem, R0arrs, List.mem_map, R0list, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, (decA_toArray l).symm⟩
  · rintro ⟨l, hl, hle⟩
    refine ⟨l, hl, ?_⟩
    apply decA_injective (r0_valid hl) ha
    rw [decA_toArray, hle]

theorem exists_word_of_mem_R0 {r : M4} (hr : r ∈ R0list) :
    ∃ w : List ℕ, (∀ k ∈ w, k < 2) ∧ r = (w.map fun k => matNM k).prod := by
  obtain ⟨hl1, hl2, hw, -, hlt⟩ := r0_parts
  rw [R0list, List.mem_map] at hr
  obtain ⟨l, hl, rfl⟩ := hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
  have hi' : i < 320 := by rw [hl1] at hi; exact hi
  refine ⟨R0words.getD i [], hlt _ ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by rw [hl2]; exact hi')]
    exact List.getElem_mem _
  · have e := congrArg decA (hw i hi')
    rw [foldl_amul, decA_idA, one_mul, List.getD_eq_getElem _ _ hi, decA_toArray] at e
    exact e.symm

theorem sp_check : spCheckA = true :=
  Certificates.certificate8138.2.1

theorem spLeafA_spec {T : M4} (h : spLeafA (encA T) = true) :
    T * symInvM T = 1 ∧
      (symInvM T * matNM 0 * T ∈ R0list → symInvM T * matNM 1 * T ∈ R0list → T ∈ R0list) ∧
      (T ∈ R0list ∨ ∃ r ∈ R0list, ∃ k < 10, (r * T) ^ k ≠ 1 ∧ ((r * T) ^ k) ^ 3 = 1) := by
  unfold spLeafA at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hT := validA_encA T
  refine ⟨?_, fun hA hB => ?_, ?_⟩
  · have := congrArg decA h1
    rwa [decA_amul, decA_encA, decA_symInvA, decA_idA] at this
  · rcases h2 with (h2 | h2) | h2
    · have hA' : memA (amul (amul (symInvA (encA T)) M0A) (encA T)) = true := by
        rw [memA_iff (validA_amul _ _), decA_amul, decA_amul, decA_symInvA, decA_M0A, decA_encA]
        exact hA
      rw [hA'] at h2
      exact absurd h2 (by decide)
    · have hB' : memA (amul (amul (symInvA (encA T)) M1A) (encA T)) = true := by
        rw [memA_iff (validA_amul _ _), decA_amul, decA_amul, decA_symInvA, decA_M1A, decA_encA]
        exact hB
      rw [hB'] at h2
      exact absurd h2 (by decide)
    · rw [memA_iff hT, decA_encA] at h2
      exact h2
  · rcases h3 with h3 | h3
    · rw [memA_iff hT, decA_encA] at h3
      exact Or.inl h3
    · right
      rw [List.any_eq_true] at h3
      obtain ⟨r, hr, hk⟩ := h3
      rw [List.any_eq_true] at hk
      obtain ⟨k, hk, hB⟩ := hk
      rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hB
      rw [R0arrs, List.mem_map] at hr
      obtain ⟨l, hl, rfl⟩ := hr
      refine ⟨toM4 l, List.mem_map_of_mem hl, k, List.mem_range.1 hk, fun he => hB.1 ?_, ?_⟩
      · apply decA_injective (validA_apow _ _) validA_idA
        rw [decA_apow, decA_amul, decA_toArray, decA_encA, he, decA_idA]
      · have := congrArg decA hB.2
        rwa [decA_apow, decA_apow, decA_amul, decA_toArray, decA_encA, decA_idA] at this

theorem sp_facts
    (T : M4) (hT : ∀ i j, ThreeQRel.threePair omegaZ (T i) (T j) = omegaZ i j) :
    T * symInvM T = 1 ∧
      (symInvM T * matNM 0 * T ∈ R0list → symInvM T * matNM 1 * T ∈ R0list → T ∈ R0list) ∧
      (T ∈ R0list ∨ ∃ r ∈ R0list, ∃ k < 10, (r * T) ^ k ≠ 1 ∧ ((r * T) ^ k) ^ 3 = 1) := by
  have h := sp_check
  simp only [spCheckA, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  have htp : ∀ i j : Fin 4,
      tpTab[vcode (T i) * 81 + vcode (T j)]! = (omegaZ i j).val := by
    intro i j
    rw [tpTab_getElem! (vcode_lt _) (vcode_lt _), vdec_vcode, vdec_vcode, hT]
  obtain ⟨o01, o02, o12, o03, o13, o23⟩ := omegaZ_vals
  rcases h _ (vcode_lt (T 0)) _ (vcode_lt (T 1)) with h1 | h1
  · exact absurd ((htp 0 1).trans o01) h1
  rcases h1 _ (vcode_lt (T 2)) with h2 | h2
  · rcases h2 with h2 | h2
    · exact absurd ((htp 0 2).trans o02) h2
    · exact absurd ((htp 1 2).trans o12) h2
  rcases h2 _ (vcode_lt (T 3)) with h3 | h3
  · rcases h3 with (h3 | h3) | h3
    · exact absurd ((htp 0 3).trans o03) h3
    · exact absurd ((htp 1 3).trans o13) h3
    · exact absurd ((htp 2 3).trans o23) h3
  have hTeq : (Matrix.of ![vdec (vcode (T 0)), vdec (vcode (T 1)), vdec (vcode (T 2)),
      vdec (vcode (T 3))] : M4) = T := by
    ext i j
    fin_cases i <;> simp [vdec_vcode]
  rw [hTeq] at h3
  exact spLeafA_spec h3

theorem a6_rigid :
    ∀ u₁ u₂ : Perm (Fin 6), u₁ ^ 3 = 1 → u₂ ^ 3 = 1 → (u₁ * u₂) ^ 5 = 1 →
    evW u₁ u₂ Wy0 = sY 0 → evW u₁ u₂ Wy1 = sY 1 → evW u₁ u₂ Wt4 = s4 →
      u₁ = sK1 ∧ u₂ = sK2 :=
  Certificates.certificate8138.2.2.1

theorem cent_sY :
    ∀ t : Perm (Fin 6), t * sY 0 = sY 0 * t → t * sY 1 = sY 1 * t →
    ∃ a < 3, ∃ b < 3, t = sY 0 ^ a * sY 1 ^ b :=
  Certificates.certificate8138.2.2.2

end CFSG.RankThree.Native.ONTriple
