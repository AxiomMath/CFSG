module

public import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin.JonesParshall

@[expose] def foxCoefM {n k : ℕ} (mats : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) :
    List (Fin k) → Fin k → Matrix (Fin n) (Fin n) (ZMod 2)
  | [] => fun _ => 0
  | i :: w => fun l => (if i = l then 1 else 0) + mats i * foxCoefM mats w l

private theorem foxC8_sum_ite_mulVec {n k : ℕ} {R : Type*} [CommRing R]
    (vals : Fin k → Fin n → R) (i : Fin k) :
    ∑ l, (if i = l then (1 : Matrix (Fin n) (Fin n) R) else 0) *ᵥ vals l = vals i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem foxC8_foxEvalM_eq_sum {n k : ℕ}
    (mats : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) (vals : Fin k → Fin n → ZMod 2)
    (w : List (Fin k)) : foxEvalM mats vals w = ∑ l, foxCoefM mats w l *ᵥ vals l := by
  induction w with
  | nil => simp [foxEvalM, foxCoefM]
  | cons i w ih =>
    change vals i + mats i *ᵥ foxEvalM mats vals w =
      ∑ l, ((if i = l then 1 else 0) + mats i * foxCoefM mats w l) *ᵥ vals l
    rw [ih, mulVec_sum]
    simp only [add_mulVec, Finset.sum_add_distrib, ← mulVec_mulVec, foxC8_sum_ite_mulVec]

private theorem eq_cob_of_foxCert {n k m : ℕ} {R : Type*} [CommRing R]
    (A : Fin k → Matrix (Fin n) (Fin n) R)
    (D : Fin m → Fin k → Matrix (Fin n) (Fin n) R) (P : Fin k → Matrix (Fin n) (Fin n) R)
    (C : Fin k → Fin m → Matrix (Fin n) (Fin n) R)
    (hcert : ∀ j l, (if j = l then 1 else 0) - (A j - 1) * P l = ∑ r, C j r * D r l)
    {v : Fin k → Fin n → R} (hv : ∀ r, ∑ l, D r l *ᵥ v l = 0) (j : Fin k) :
    v j = A j *ᵥ (∑ l, P l *ᵥ v l) - ∑ l, P l *ᵥ v l := by
  have h1 : ∑ l, ((if j = l then 1 else 0) - (A j - 1) * P l) *ᵥ v l = 0 := by
    simp_rw [hcert, sum_mulVec, ← mulVec_mulVec]
    rw [Finset.sum_comm]
    simp_rw [← mulVec_sum, hv, mulVec_zero, Finset.sum_const_zero]
  have h2 : ∑ l, ((if j = l then 1 else 0) - (A j - 1) * P l) *ᵥ v l =
      v j - (A j *ᵥ (∑ l, P l *ᵥ v l) - ∑ l, P l *ᵥ v l) := by
    simp_rw [sub_mulVec, Finset.sum_sub_distrib, foxC8_sum_ite_mulVec, ← mulVec_mulVec,
      ← mulVec_sum, sub_mulVec, one_mulVec]
  rw [h2] at h1
  exact sub_eq_zero.mp h1

theorem exists_cob_of_foxCert {G : Type*} [Group G] {n k m : ℕ}
    (μ : G →* AddMonoid.End (Fin n → ZMod 2)) (gens : Fin k → G)
    (mats : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) (hμ : ∀ i u, μ (gens i) u = mats i *ᵥ u)
    (rels : Fin m → List (Fin k)) (hrel : ∀ r, wordEval gens (rels r) = 1)
    (P : Fin k → Matrix (Fin n) (Fin n) (ZMod 2))
    (C : Fin k → Fin m → Matrix (Fin n) (Fin n) (ZMod 2))
    (hcert : ∀ j l, (if j = l then 1 else 0) - (mats j - 1) * P l =
      ∑ r, C j r * foxCoefM mats (rels r) l)
    {f : G → Fin n → ZMod 2} (hf : f ∈ Z1A μ) :
    ∃ x : Fin n → ZMod 2, ∀ j, f (gens j) = μ (gens j) x - x := by
  have hfox : ∀ w, foxEval μ gens (fun l => f (gens l)) w =
      foxEvalM mats (fun l => f (gens l)) w := by
    intro w
    induction w with
    | nil => rfl
    | cons i w ih =>
      change f (gens i) + μ (gens i) (foxEval μ gens (fun l => f (gens l)) w) =
        f (gens i) + mats i *ᵥ foxEvalM mats (fun l => f (gens l)) w
      rw [ih, hμ i]
  have hrel0 : ∀ r, ∑ l, foxCoefM mats (rels r) l *ᵥ (fun l => f (gens l)) l = 0 := by
    intro r
    have h1 := Z1A_wordEval hf gens (rels r)
    rw [hrel r, Z1A_one hf] at h1
    have h2 : foxEval μ gens (fun l => f (gens l)) (rels r) = 0 := h1.symm
    rw [hfox (rels r), foxC8_foxEvalM_eq_sum] at h2
    exact h2
  have hv : ∀ j, f (gens j) =
      mats j *ᵥ (∑ l, P l *ᵥ f (gens l)) - ∑ l, P l *ᵥ f (gens l) := by
    intro j
    have h := eq_cob_of_foxCert mats (fun r l => foxCoefM mats (rels r) l) P C hcert
      (v := fun l => f (gens l)) hrel0 j
    simpa using h
  exact ⟨∑ l, P l *ᵥ f (gens l), fun j => by rw [hv j, hμ j]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
