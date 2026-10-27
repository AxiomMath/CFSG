module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Check
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemG23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

theorem length_mul14 (m n : List ℕ) : (mul14 m n).length = 196 := by
  simp [mul14]

theorem length_one14 : one14.length = 196 := by
  simp [one14]

theorem length_wordCode (w : List ℕ) : (wordCode w).length = 196 := by
  have key : ∀ (w : List ℕ) (acc : List ℕ), acc.length = 196 →
      (w.foldl (fun acc l => mul14 acc (letterCode l)) acc).length = 196 := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons l w ih => intro acc _; exact ih _ (length_mul14 _ _)
  exact key w one14 length_one14

theorem invWord_lt (w : List ℕ) (hw : ∀ l ∈ w, l < 8) : ∀ l ∈ invWord w, l < 8 := by
  intro l hl
  simp only [invWord, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  split_ifs <;> omega

section Elements


noncomputable def rootElem (l : ℕ) : GL14 :=
  if l = 0 then gX 0 else if l = 1 then gX 1 else if l = 2 then gY 0 else gY 1

noncomputable def letterElem (l : ℕ) : GL14 :=
  if l < 4 then rootElem l else (rootElem (l - 4))⁻¹

noncomputable def wordElem (w : List ℕ) : GL14 :=
  (w.map letterElem).prod

@[expose] def rootCode (l : ℕ) : List ℕ :=
  [x0c, x1c, y0c, y1c].getD l one14

theorem coe_rootElem {l : ℕ} (hl : l < 4) : (rootElem l : M14) = dec14 (rootCode l) := by
  unfold rootElem rootCode
  interval_cases l
  · simpa using coe_gX0
  · simpa using coe_gX1
  · simpa using coe_gY0
  · simpa using coe_gY1

theorem rootElem_mem {l : ℕ} (hl : l < 4) : rootElem l ∈ R3 := by
  unfold rootElem
  interval_cases l
  · simpa using gX_mem 0
  · simpa using gX_mem 1
  · simpa using gY_mem 0
  · simpa using gY_mem 1

@[expose] def RootCubes : Prop := ∀ l < 4, cube14 (rootCode l) = one14

theorem rootElem_pow_three (hc : RootCubes) {l : ℕ} (hl : l < 4) : rootElem l ^ 3 = 1 :=
  pow_three_of_code (coe_rootElem hl) (hc l hl)

theorem coe_letterElem (hc : RootCubes) {l : ℕ} (hl : l < 8) :
    (letterElem l : M14) = dec14 (letterCode l) := by
  by_cases h4 : l < 4
  · have hl' : letterElem l = rootElem l := by simp [letterElem, h4]
    have hc' : letterCode l = rootCode l := by simp [letterCode, rootCode, h4]
    rw [hl', hc']
    exact coe_rootElem h4
  · have hl' : letterElem l = rootElem (l - 4) ^ 2 := by
      simp only [letterElem, h4, ite_false]
      exact inv_eq_sq (rootElem_pow_three hc (by omega))
    have hc' : letterCode l = sq14 (rootCode (l - 4)) := by simp [letterCode, rootCode, h4]
    rw [hl', hc']
    exact coe_sq (coe_rootElem (by omega))

theorem letterElem_mem {l : ℕ} (hl : l < 8) : letterElem l ∈ R3 := by
  by_cases h4 : l < 4
  · simp only [letterElem, h4, ite_true]
    exact rootElem_mem h4
  · simp only [letterElem, h4, ite_false]
    exact inv_mem (rootElem_mem (by omega))

theorem coe_wordElem (hc : RootCubes) (w : List ℕ) (hw : ∀ l ∈ w, l < 8) :
    (wordElem w : M14) = dec14 (wordCode w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l < 8) → ∀ (g : GL14) (c : List ℕ),
      (g : M14) = dec14 c →
      ((g * (w.map letterElem).prod : GL14) : M14) =
        dec14 (w.foldl (fun acc l => mul14 acc (letterCode l)) c) := by
    intro w
    induction w with
    | nil => intro _ g c h; simpa using h
    | cons l w ih =>
      intro hw g c h
      rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
      refine ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _ ?_
      rw [Units.val_mul, h, coe_letterElem hc (hw l (List.mem_cons_self ..)), dec14_mul14]
  have := key w hw 1 one14 (by rw [Units.val_one, dec14_one14])
  rwa [one_mul] at this

theorem wordElem_mem (w : List ℕ) (hw : ∀ l ∈ w, l < 8) : wordElem w ∈ R3 := by
  unfold wordElem
  exact list_prod_mem fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact letterElem_mem (hw l hl)

theorem wordElem_invWord (w : List ℕ) (hw : ∀ l ∈ w, l < 8) :
    wordElem (invWord w) = (wordElem w)⁻¹ := by
  have hflip : ∀ l, l < 8 → letterElem (if l < 4 then l + 4 else l - 4) = (letterElem l)⁻¹ := by
    intro l hl
    by_cases h4 : l < 4
    · have : ¬ (l + 4 < 4) := by omega
      simp [letterElem, h4, this]
    · have h4' : l - 4 < 4 := by omega
      simp [letterElem, h4, h4']
  unfold wordElem invWord
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  simp only [Function.comp_apply]
  exact hflip l (hw l hl)

theorem wordPair_spec (hc : RootCubes) (w : List ℕ) (hw : ∀ l ∈ w, l < 8) :
    dec14 ((wordPair w).take 196) = (wordElem w : M14) ∧
      dec14 ((wordPair w).drop 196) = ((wordElem w)⁻¹ : GL14) := by
  have hlen := length_wordCode w
  refine ⟨?_, ?_⟩
  · rw [wordPair, List.take_left' hlen, coe_wordElem hc w hw]
  · rw [wordPair, List.drop_left' hlen, ← wordElem_invWord w hw,
      coe_wordElem hc _ (invWord_lt w hw)]

theorem dec14_conjStep (hc : RootCubes) (w : List ℕ) (hw : ∀ l ∈ w, l < 8) (x : List ℕ) :
    dec14 (conjStep (wordPair w) x) =
      (wordElem w : M14) * dec14 x * ((wordElem w)⁻¹ : GL14) := by
  obtain ⟨h1, h2⟩ := wordPair_spec hc w hw
  rw [conjStep, dec14_mul14, dec14_mul14, h1, h2]

end Elements

end CFSG.RankThree.PartTwo.Sec4.Item434RemG23
