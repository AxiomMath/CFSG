module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Code
public import CFSG.Quasithin.Background.G2UClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U Matrix

local notation "Mat4" => Matrix (Fin 4) (Fin 4) F9

theorem matA_unitary : ((dec4 matAc).map (· ^ 3))ᵀ * dec4 matAc = 1 := by decide +kernel

theorem det_matA : (dec4 matAc).det = 1 := by decide +kernel

theorem matB_unitary : ((dec4 matBc).map (· ^ 3))ᵀ * dec4 matBc = 1 := by decide +kernel

theorem det_matB : (dec4 matBc).det = 1 := by decide +kernel

theorem matAi_unitary : ((dec4 matAic).map (· ^ 3))ᵀ * dec4 matAic = 1 := by decide +kernel

theorem det_matAi : (dec4 matAic).det = 1 := by decide +kernel

theorem matBi_unitary : ((dec4 matBic).map (· ^ 3))ᵀ * dec4 matBic = 1 := by decide +kernel

theorem det_matBi : (dec4 matBic).det = 1 := by decide +kernel

theorem mul_matAi : dec4 matAc * dec4 matAic = 1 := by decide +kernel

theorem mul_matBi : dec4 matBc * dec4 matBic = 1 := by decide +kernel

@[expose] noncomputable def suOfMat (A : Mat4) (hdet : A.det = 1) (hu : (A.map (· ^ 3))ᵀ * A = 1) :
    StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' A (by rw [hdet]; exact isUnit_one),
    Subgroup.subset_closure ⟨hdet, hu⟩⟩

theorem coe_suOfMat (A : Mat4) (hdet : A.det = 1) (hu : (A.map (· ^ 3))ᵀ * A = 1) :
    (((suOfMat A hdet hu : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) = A := rfl

@[expose] noncomputable def suA : StatedSU 4 3 F9 := suOfMat _ det_matA matA_unitary

@[expose] noncomputable def suB : StatedSU 4 3 F9 := suOfMat _ det_matB matB_unitary

@[expose] noncomputable def suAi : StatedSU 4 3 F9 := suOfMat _ det_matAi matAi_unitary

@[expose] noncomputable def suBi : StatedSU 4 3 F9 := suOfMat _ det_matBi matBi_unitary

theorem suA_mul_suAi : suA * suAi = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact mul_matAi

theorem suB_mul_suBi : suB * suBi = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact mul_matBi

theorem suA_inv : suA⁻¹ = suAi := inv_eq_of_mul_eq_one_right suA_mul_suAi

theorem suB_inv : suB⁻¹ = suBi := inv_eq_of_mul_eq_one_right suB_mul_suBi

@[expose] noncomputable def letterElem (l : ℕ) : StatedSU 4 3 F9 :=
  if l = 0 then suA else if l = 1 then suB else if l = 2 then suAi else suBi

@[expose] noncomputable def wordElem (w : List ℕ) : StatedSU 4 3 F9 := (w.map letterElem).prod

theorem coe_letterElem {l : ℕ} (hl : l < 4) :
    (((letterElem l : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) = dec4 (letterCode l) := by
  unfold letterElem letterCode
  interval_cases l <;> simp [suA, suB, suAi, suBi, coe_suOfMat]

theorem letterElem_flip {l : ℕ} (hl : l < 4) :
    letterElem (if l < 2 then l + 2 else l - 2) = (letterElem l)⁻¹ := by
  unfold letterElem
  interval_cases l <;> simp [← suA_inv, ← suB_inv]

theorem coe_wordElem (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    (((wordElem w : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) = dec4 (wordCode w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l < 4) → ∀ (g : StatedSU 4 3 F9) (c : List ℕ),
      (((g : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) = dec4 c →
      (((g * (w.map letterElem).prod : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) =
        dec4 (w.foldl (fun acc l => mul4 acc (letterCode l)) c) := by
    intro w
    induction w with
    | nil => intro _ g c h; simpa using h
    | cons l w ih =>
      intro hw g c h
      rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
      refine ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _ ?_
      rw [Subgroup.coe_mul, Units.val_mul, h, coe_letterElem (hw l (List.mem_cons_self ..)),
        dec4_mul4]
  have := key w hw 1 one4 (by
    rw [Subgroup.coe_one, Units.val_one, dec4_one4])
  rwa [one_mul] at this

theorem wordElem_invWord (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    wordElem (invWord w) = (wordElem w)⁻¹ := by
  unfold wordElem invWord
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  simp only [Function.comp_apply]
  exact letterElem_flip (hw l hl)

theorem invWord_lt (w : List ℕ) (hw : ∀ l ∈ w, l < 4) : ∀ l ∈ invWord w, l < 4 := by
  intro l hl
  simp only [invWord, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  split_ifs <;> omega

theorem length_wordCode (w : List ℕ) : (wordCode w).length = 16 := by
  have key : ∀ (w : List ℕ) (acc : List ℕ), acc.length = 16 →
      (w.foldl (fun acc l => mul4 acc (letterCode l)) acc).length = 16 := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons l w ih => intro acc _; exact ih _ (by simp [mul4])
  exact key w one4 rfl

theorem wordPair_spec (w : List ℕ) (hw : ∀ l ∈ w, l < 4) :
    dec4 ((wordPair w).take 16) = (((wordElem w : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) ∧
      dec4 ((wordPair w).drop 16) =
        ((((wordElem w)⁻¹ : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) := by
  have hlen := length_wordCode w
  refine ⟨?_, ?_⟩
  · rw [wordPair, List.take_left' hlen, coe_wordElem w hw]
  · rw [wordPair, List.drop_left' hlen, ← wordElem_invWord w hw,
      coe_wordElem _ (invWord_lt w hw)]

theorem dec4_conjStep (w : List ℕ) (hw : ∀ l ∈ w, l < 4) (x : List ℕ) :
    dec4 (conjStep (wordPair w) x) =
      (((wordElem w : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) * dec4 x *
        ((((wordElem w)⁻¹ : StatedSU 4 3 F9) : GL (Fin 4) F9) : Mat4) := by
  obtain ⟨h1, h2⟩ := wordPair_spec w hw
  rw [conjStep, dec4_mul4, dec4_mul4, h1, h2]

@[expose] noncomputable def toMat : StatedSU 4 3 F9 →* Mat4 :=
  (Units.coeHom Mat4).comp (StatedSU 4 3 F9).subtype

theorem toMat_apply (g : StatedSU 4 3 F9) : toMat g = ((g : GL (Fin 4) F9) : Mat4) := rfl

theorem toMat_injective : Function.Injective toMat := fun _ _ h =>
  Subtype.ext (Units.ext h)

@[expose] noncomputable def sylS : Subgroup (StatedSU 4 3 F9) :=
  Subgroup.closure {g | ∃ w ∈ uGenWords, wordElem w = g}

theorem uSylCheck_parts (h : uSylCheck = true) :
    uElems.size = 729 ∧ closedCheck mul4 uGens uElems = true ∧ distinctCheck uElems = true ∧
      allCheck canon4 uElems = true ∧ (∀ w ∈ uGenWords, ∀ l ∈ w, l < 4) := by
  simp only [uSylCheck, Bool.and_eq_true, beq_iff_eq, wordOK, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem image_gens_sylS (hw : ∀ w ∈ uGenWords, ∀ l ∈ w, l < 4) :
    toMat '' {g | ∃ w ∈ uGenWords, wordElem w = g} = {y | ∃ c ∈ uGens, dec4 c = y} := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, uGens, List.mem_map]
  constructor
  · rintro ⟨g, ⟨w, hwm, rfl⟩, rfl⟩
    exact ⟨wordCode w, ⟨w, hwm, rfl⟩, (toMat_apply _ ▸ coe_wordElem w (hw w hwm)).symm⟩
  · rintro ⟨_, ⟨w, hwm, rfl⟩, rfl⟩
    exact ⟨wordElem w, ⟨w, hwm, rfl⟩, (toMat_apply _ ▸ coe_wordElem w (hw w hwm))⟩

theorem image_sylS (hsyl : uSylCheck = true) :
    toMat '' (sylS : Set (StatedSU 4 3 F9)) =
      {y | ∃ t < uElems.size, dec4 (uElems.getD t []) = y} := by
  obtain ⟨-, hclosed, -, -, hw⟩ := uSylCheck_parts hsyl
  exact image_closure_eq dec4 one4 mul4 uGens toMat dec4_one4 dec4_mul4 _
    (image_gens_sylS hw) uPar hclosed

theorem canon4_uAt (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) : canon4 (uAt t) = true := by
  obtain ⟨hsize, -, -, hcanon, -⟩ := uSylCheck_parts hsyl
  exact allCheck_spec (p := canon4) (es := uElems) hcanon (t := t) (ht.trans_eq hsize.symm)

theorem card_sylS (hsyl : uSylCheck = true) : Nat.card sylS = 729 := by
  obtain ⟨hsize, hclosed, hdist, hcanon, hw⟩ := uSylCheck_parts hsyl
  refine (card_closure_eq dec4 one4 mul4 uGens toMat toMat_injective dec4_one4 dec4_mul4 _
    (image_gens_sylS hw) uPar hclosed hdist fun t ht t' ht' e => ?_).trans hsize
  exact dec4_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e

theorem exists_code_sylS (hsyl : uSylCheck = true) {g : StatedSU 4 3 F9} (hg : g ∈ sylS) :
    ∃ t < 729, dec4 (uAt t) = toMat g := by
  have h : toMat g ∈ toMat '' (sylS : Set (StatedSU 4 3 F9)) := ⟨g, hg, rfl⟩
  rw [image_sylS hsyl] at h
  obtain ⟨t, ht, e⟩ := h
  obtain ⟨hsize, -⟩ := uSylCheck_parts hsyl
  exact ⟨t, ht.trans_eq hsize, e⟩

theorem exists_elem_of_code (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) :
    ∃ g ∈ sylS, dec4 (uAt t) = toMat g := by
  have h : dec4 (uElems.getD t []) ∈ {y | ∃ t < uElems.size, dec4 (uElems.getD t []) = y} := by
    obtain ⟨hsize, -⟩ := uSylCheck_parts hsyl
    exact ⟨t, ht.trans_eq hsize.symm, rfl⟩
  rw [← image_sylS hsyl] at h
  obtain ⟨g, hg, e⟩ := h
  exact ⟨g, hg, e.symm⟩

theorem uAt_inj (hsyl : uSylCheck = true) {t t' : ℕ} (ht : t < 729) (ht' : t' < 729)
    (h : uAt t = uAt t') : t = t' := by
  obtain ⟨hsize, -, hdist, -⟩ := uSylCheck_parts hsyl
  exact distinctCheck_spec hdist (ht.trans_eq hsize.symm) (ht'.trans_eq hsize.symm) h

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
