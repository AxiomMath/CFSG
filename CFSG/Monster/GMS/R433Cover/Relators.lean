module

public import CFSG.Monster.GMS.R433Cover.Flags
public import CFSG.YGroups.Y433.MarkedQuotient

public section

namespace CFSG.Monster.GMS.R433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open CFSG.YGroups (yRels yEdges pairExp pairWord spiderWord ngen R433 yGen F433)

variable {E G : Type*} [Group E] [Group G]

theorem parent_lt (c : ℕ) (hc : 0 < c) : parent c < c := by
  by_cases h : c < 11
  · exact (parent_edge c h hc).1
  · have : parent c = 0 := by
      unfold parent
      exact List.getD_eq_default _ _ (by simpa using h)
    omega

theorem edges_parent : ∀ p ∈ edges, 0 < p.2 ∧ p.2 < 11 ∧ parent p.2 = p.1 := by decide

theorem yEdges_eq : yEdges 4 3 3 = edges := by decide

@[expose] def edgeB (s t : ℕ) : Bool := decide ((s, t) ∈ edges)

theorem pair_exp_cases : ∀ s < 11, ∀ t < 11, s < t →
    (pairExp 4 3 3 s t = 3 ∧ edgeB s t = true) ∨ (pairExp 4 3 3 s t = 2 ∧ nonadj s t = true) := by
  decide

theorem pair_exp_two : ∀ s < 11, ∀ t < 11, s < t → nonadj s t = true → pairExp 4 3 3 s t = 2 := by
  decide

theorem pair_exp_three : ∀ c < 11, 0 < c → pairExp 4 3 3 (parent c) c = 3 := by decide

theorem nonadj_symm : ∀ s < 11, ∀ t < 11, nonadj s t = true → nonadj t s = true := by decide

theorem nonadj_lt {s t : ℕ} (h : nonadj s t = true) : s < 11 ∧ t < 11 := by
  unfold nonadj at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem length_even_of_mem_yRels : ∀ w ∈ yRels 4 3 3, w.length % 2 = 0 := by decide +kernel

theorem rels_of_flags {gh : ℕ → E}
    (hsq1 : ∀ s < 11, gh s * gh s = 1)
    (hcomm : ∀ s t, nonadj s t = true → gh s * gh t = gh t * gh s)
    (hedge : ∀ p ∈ edges, (gh p.1 * gh p.2) ^ 3 = 1)
    (hsp : (evalWord gh (spiderWord 4 3)) ^ 10 = 1) :
    ∀ w ∈ yRels 4 3 3, evalWord gh w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hspw
  · have := hsq1 s (by simpa [ngen] using hs)
    simpa [evalWord] using this
  · have hs11 : s < 11 := by simpa [ngen] using hs
    have ht11 : t < 11 := by simpa [ngen] using ht
    have hlt : s < t := by simpa using hst
    unfold pairWord
    rw [CFSG.YGroups.Y443.evalWord_pair]
    rcases pair_exp_cases s hs11 t ht11 hlt with ⟨h3, he⟩ | ⟨h2, hna⟩
    · rw [h3]; exact hedge (s, t) (by simpa [edgeB] using he)
    · rw [h2]
      have hc := hcomm s t hna
      have hs1 := hsq1 s hs11
      have ht1 := hsq1 t ht11
      calc (gh s * gh t) ^ 2 = gh s * gh t * (gh s * gh t) := sq _
        _ = gh s * (gh t * gh s) * gh t := by group
        _ = gh s * (gh s * gh t) * gh t := by rw [← hc]
        _ = (gh s * gh s) * (gh t * gh t) := by group
        _ = 1 := by rw [hs1, ht1, one_mul]
  · split_ifs at hspw with hc
    · simp only [List.mem_singleton] at hspw
      subst hspw
      rw [CFSG.YGroups.Y443.evalWord_replicate_flatten]
      exact hsp
    · simp at hspw

theorem fam_sq {g : ℕ → G} (hrel : ∀ w ∈ yRels 4 3 3, evalWord g w = 1) {s : ℕ} (hs : s < 11) :
    g s * g s = 1 := by
  have := hrel [s, s] (CFSG.YGroups.square_mem_yRels (p := 4) (q := 3) (r := 3) (s := s)
    (by simpa [ngen] using hs))
  simpa [evalWord] using this

theorem fam_pair {g : ℕ → G} (hrel : ∀ w ∈ yRels 4 3 3, evalWord g w = 1) {s t : ℕ} (hst : s < t)
    (ht : t < 11) : (g s * g t) ^ pairExp 4 3 3 s t = 1 := by
  have := hrel _ (CFSG.YGroups.Y443.pairWord_mem_yRels (p := 4) (q := 3) (r := 3) hst
    (by simpa [ngen] using ht))
  rwa [pairWord, CFSG.YGroups.Y443.evalWord_pair] at this

theorem fam_comm {g : ℕ → G} (hrel : ∀ w ∈ yRels 4 3 3, evalWord g w = 1) {s t : ℕ}
    (h : nonadj s t = true) : g s * g t = g t * g s := by
  obtain ⟨hs, ht⟩ := nonadj_lt h
  have hne : s ≠ t := by
    unfold nonadj at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h2 := fam_pair hrel hlt ht
    rw [pair_exp_two s hs t ht hlt h] at h2
    exact commute_of_sq (fam_sq hrel hs) (fam_sq hrel ht) h2
  · have h' := nonadj_symm s hs t ht h
    have h2 := fam_pair hrel hlt hs
    rw [pair_exp_two t ht s hs hlt h'] at h2
    exact (commute_of_sq (fam_sq hrel ht) (fam_sq hrel hs) h2).symm

@[expose] noncomputable def marked (ρ : R433 →* G) (c : ℕ) : G := ρ (R433.π (yGen 4 3 3 c))

theorem F433_213_eq :
    F433 2 1 3 = evalWord (yGen 4 3 3) [0, 5, 6, 7, 1, 2, 8] ^ 9 := by
  rw [CFSG.YGroups.F433_eq_evalWord]
  rfl

theorem marked_rels (ρ : R433 →* G) : ∀ w ∈ yRels 4 3 3, evalWord (marked ρ) w = 1 := by
  intro w hw
  have := CFSG.YGroups.Relabel.map_evalWord (ρ.comp R433.π) (yGen 4 3 3) w
  rw [CFSG.YGroups.evalWord_yGen_of_mem hw, map_one] at this
  exact this.symm

theorem marked_F (ρ : R433 →* G) : (evalWord (marked ρ) [0, 5, 6, 7, 1, 2, 8]) ^ 9 = 1 := by
  have h := CFSG.YGroups.Relabel.map_evalWord (ρ.comp R433.π) (yGen 4 3 3)
    [0, 5, 6, 7, 1, 2, 8]
  calc (evalWord (marked ρ) [0, 5, 6, 7, 1, 2, 8]) ^ 9
      = ((ρ.comp R433.π) (evalWord (yGen 4 3 3) [0, 5, 6, 7, 1, 2, 8])) ^ 9 := by rw [h]; rfl
    _ = (ρ.comp R433.π) (evalWord (yGen 4 3 3) [0, 5, 6, 7, 1, 2, 8] ^ 9) :=
        (map_pow _ _ _).symm
    _ = (ρ.comp R433.π) (F433 2 1 3) := by rw [← F433_213_eq]
    _ = 1 := by simp [CFSG.YGroups.R433.π_F433_213]

@[expose] def ConjIdentity (g : ℕ → G) (Y : List ℕ) : Prop :=
  (evalWord g Y)⁻¹ * (g 0 * g 4 * g 6) * evalWord g Y = g 2 * g 5 * g 7 * g 9

@[expose] def SpiderIdentity (g : ℕ → G) : Prop :=
  ((evalWord g (spiderWord 4 3)) ^ 5 * g 0) ^ 3 = 1

end CFSG.Monster.GMS.R433Cover
