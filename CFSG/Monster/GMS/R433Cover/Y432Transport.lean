module

public import CFSG.Monster.GMS.R433Cover.Relators

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)
open CFSG.YGroups (yRels spiderWord ngen R433 U433 yGen F433 yHom yHom_yGen)

theorem rels_y432_y433 : ∀ w ∈ yRels 4 3 2, w.map id ∈ yRels 4 3 3 := by decide +kernel

@[expose] noncomputable def iota432 : CFSG.YGroups.YGroup 4 3 2 →* U433 :=
  yHom id rels_y432_y433

theorem iota432_evalWord (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    iota432 (evalWord (yGen 4 3 2) w) = evalWord (yGen 4 3 3) w := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, map_mul, ih (fun c' hc' => hw c' (by simp [hc'])), evalWord_cons]
    congr 1
    exact yHom_yGen id rels_y432_y433 (by simpa [ngen] using hw c (by simp))

@[expose] def f213Word : List ℕ := (List.replicate 9 [0, 5, 6, 7, 1, 2, 8]).flatten

theorem letters_lt_of_replicate_flatten {w : List ℕ} {n : ℕ} (h : ∀ c ∈ w, c < 10) :
    ∀ c ∈ (List.replicate n w).flatten, c < 10 := by
  intro c hc
  rw [List.mem_flatten] at hc
  obtain ⟨l, hl, hcl⟩ := hc
  rw [List.mem_replicate] at hl
  rw [hl.2] at hcl
  exact h c hcl

theorem f213Word_lt : ∀ c ∈ f213Word, c < 10 :=
  letters_lt_of_replicate_flatten (by intro c hc; simp at hc; omega)

theorem spiderWord_lt : ∀ c ∈ spiderWord 4 3, c < 10 := by
  intro c hc; simp [CFSG.YGroups.spiderWord] at hc; omega

variable {G : Type*} [Group G]

theorem marked_mul_self (ρ : R433 →* G) (c : ℕ) : marked ρ c * marked ρ c = 1 := by
  show ρ (R433.π (yGen 4 3 3 c)) * ρ (R433.π (yGen 4 3 3 c)) = 1
  rw [← map_mul, ← map_mul, CFSG.YGroups.yGen_mul_self, map_one, map_one]

theorem marked_evalWord (ρ : R433 →* G) (w : List ℕ) :
    evalWord (marked ρ) w = (ρ.comp R433.π) (evalWord (yGen 4 3 3) w) :=
  (CFSG.YGroups.Relabel.map_evalWord (ρ.comp R433.π) (yGen 4 3 3) w).symm

theorem conjIdentity_of_eq {g : ℕ → G} (hinv : ∀ c, g c * g c = 1) (Y : List ℕ)
    (h : evalWord g (Y.reverse ++ [0, 4, 6] ++ Y) = evalWord g [2, 5, 7, 9]) :
    ConjIdentity g Y := by
  rw [evalWord_append, evalWord_append, evalWord_reverse_inv hinv] at h
  simpa [ConjIdentity, evalWord, mul_assoc] using h

theorem spiderIdentity_of_eq {g : ℕ → G}
    (h : evalWord g
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten = 1) :
    SpiderIdentity g := by
  rw [CFSG.YGroups.Y443.evalWord_replicate_flatten, evalWord_append,
    CFSG.YGroups.Y443.evalWord_replicate_flatten] at h
  simpa [SpiderIdentity, evalWord] using h

theorem identities_of_Y432 (ρ : R433 →* G) (Y : List ℕ) (hYlt : ∀ c ∈ Y, c < 10)
    (hid2 : evalWord (yGen 4 3 2) (Y.reverse ++ [0, 4, 6] ++ Y) =
      evalWord (yGen 4 3 2) ([2, 5, 7, 9] ++ f213Word))
    (hid1 : evalWord (yGen 4 3 2)
      (List.replicate 3 ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten = 1) :
    ConjIdentity (marked ρ) Y ∧ SpiderIdentity (marked ρ) := by
  have hinv := marked_mul_self ρ
  constructor
  · apply conjIdentity_of_eq hinv Y
    have hl : ∀ c ∈ Y.reverse ++ [0, 4, 6] ++ Y, c < 10 := by
      intro c hc
      simp only [List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with (hc | hc | hc | hc) | hc
      · exact hYlt c hc
      · omega
      · omega
      · omega
      · exact hYlt c hc
    have hr : ∀ c ∈ [2, 5, 7, 9] ++ f213Word, c < 10 := by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (hc | hc | hc | hc) | hc
      · omega
      · omega
      · omega
      · omega
      · exact f213Word_lt c hc
    have hF : (ρ.comp R433.π) (evalWord (yGen 4 3 3) f213Word) = 1 := by
      have : evalWord (yGen 4 3 3) f213Word = F433 2 1 3 := by
        rw [F433_213_eq, f213Word, CFSG.YGroups.Y443.evalWord_replicate_flatten]
      rw [this]; simp [CFSG.YGroups.R433.π_F433_213]
    have h2 : iota432 (evalWord (yGen 4 3 2) (Y.reverse ++ [0, 4, 6] ++ Y)) =
        iota432 (evalWord (yGen 4 3 2) ([2, 5, 7, 9] ++ f213Word)) := by rw [hid2]
    rw [iota432_evalWord _ hl, iota432_evalWord _ hr,
      evalWord_append (yGen 4 3 3) [2, 5, 7, 9] f213Word] at h2
    have h3 := congrArg (ρ.comp R433.π) h2
    rw [map_mul, hF, mul_one, ← marked_evalWord, ← marked_evalWord] at h3
    exact h3
  · apply spiderIdentity_of_eq
    have hl : ∀ c ∈ (List.replicate 3
        ((List.replicate 5 (spiderWord 4 3)).flatten ++ [0])).flatten, c < 10 := by
      apply letters_lt_of_replicate_flatten
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact letters_lt_of_replicate_flatten spiderWord_lt c hc
      · simp at hc; omega
    have h := congrArg (fun x => (ρ.comp R433.π) (iota432 x)) hid1
    simp only [iota432_evalWord _ hl, map_one] at h
    rw [marked_evalWord]
    exact h

end CFSG.Monster.GMS.R433Cover
