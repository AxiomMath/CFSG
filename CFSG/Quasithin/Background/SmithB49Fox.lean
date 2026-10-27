module

public import CFSG.Quasithin.Background.SmithB49Bits
public import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_ite_mulVec {k : ℕ} (vals : Fin k → ι → ZMod 2) (i : Fin k) :
    ∑ l, (if i = l then (1 : Matrix ι ι (ZMod 2)) else 0) *ᵥ vals l = vals i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem foxEval_eq_sum {G : Type*} [Group G] {k : ℕ} (μ : G →* AddMonoid.End (ι → ZMod 2))
    (gens : Fin k → G) (A : Fin k → Matrix ι ι (ZMod 2)) (hA : ∀ i v, μ (gens i) v = A i *ᵥ v)
    (vals : Fin k → ι → ZMod 2) (w : List (Fin k)) :
    foxEval μ gens vals w = ∑ l, foxD A w l *ᵥ vals l := by
  induction w with
  | nil =>
    show (0 : ι → ZMod 2) = ∑ l, foxD A [] l *ᵥ vals l
    simp [foxD]
  | cons i w ih =>
    change vals i + μ (gens i) (foxEval μ gens vals w) =
      ∑ l, ((if i = l then 1 else 0) + A i * foxD A w l) *ᵥ vals l
    rw [hA, ih, mulVec_sum]
    simp only [add_mulVec, Finset.sum_add_distrib, ← mulVec_mulVec, sum_ite_mulVec]

theorem cocycle_word {G : Type*} [Group G] {k : ℕ} {μ : G →* AddMonoid.End (ι → ZMod 2)}
    {gens : Fin k → G} {A : Fin k → Matrix ι ι (ZMod 2)} (hA : ∀ i v, μ (gens i) v = A i *ᵥ v)
    {c : G → ι → ZMod 2} (hc : c ∈ Z1A μ) (w : List (Fin k)) :
    c (wordEval gens w) = ∑ l, foxD A w l *ᵥ c (gens l) := by
  rw [Z1A_wordEval hc gens w, foxEval_eq_sum μ gens A hA]

theorem fox_rel {G : Type*} [Group G] {k : ℕ} {μ : G →* AddMonoid.End (ι → ZMod 2)}
    {gens : Fin k → G} {A : Fin k → Matrix ι ι (ZMod 2)} (hA : ∀ i v, μ (gens i) v = A i *ᵥ v)
    {c : G → ι → ZMod 2} (hc : c ∈ Z1A μ) {r : List (Fin k)} (hr : wordEval gens r = 1) :
    ∑ l, foxD A r l *ᵥ c (gens l) = 0 := by
  rw [← cocycle_word hA hc r, hr]
  exact Z1A_one hc

omit [Fintype ι] [DecidableEq ι] in
theorem two_eq_zero_vec (x : ι → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

theorem eq_of_cert {k m : ℕ} (A : Fin k → Matrix ι ι (ZMod 2))
    (D : Fin m → Fin k → Matrix ι ι (ZMod 2)) (P F E : Fin k → Matrix ι ι (ZMod 2))
    (C : Fin k → Fin m → Matrix ι ι (ZMod 2))
    (hcert : ∀ j l, (if j = l then 1 else 0) + (A j + 1) * P l + F j * E l = ∑ r, C j r * D r l)
    {v : Fin k → ι → ZMod 2} (hv : ∀ r, ∑ l, D r l *ᵥ v l = 0) (j : Fin k) :
    v j = A j *ᵥ (∑ l, P l *ᵥ v l) + (∑ l, P l *ᵥ v l) + F j *ᵥ (∑ l, E l *ᵥ v l) := by
  have h1 : ∑ l, ((if j = l then 1 else 0) + (A j + 1) * P l + F j * E l) *ᵥ v l = 0 := by
    simp_rw [hcert, sum_mulVec, ← mulVec_mulVec]
    rw [Finset.sum_comm]
    simp_rw [← mulVec_sum, hv, mulVec_zero, Finset.sum_const_zero]
  have h2 : ∑ l, ((if j = l then 1 else 0) + (A j + 1) * P l + F j * E l) *ᵥ v l =
      v j + (A j *ᵥ (∑ l, P l *ᵥ v l) + (∑ l, P l *ᵥ v l) + F j *ᵥ (∑ l, E l *ᵥ v l)) := by
    simp_rw [add_mulVec, Finset.sum_add_distrib, sum_ite_mulVec, ← mulVec_mulVec,
      ← mulVec_sum, add_mulVec, one_mulVec]
    abel
  rw [h2] at h1
  have h3 := congrArg (· + (A j *ᵥ (∑ l, P l *ᵥ v l) + (∑ l, P l *ᵥ v l) +
    F j *ᵥ (∑ l, E l *ᵥ v l))) h1
  simp only [zero_add] at h3
  rw [← h3, add_assoc, two_eq_zero_vec, add_zero]

theorem mem_B1A_of_cert {G : Type*} [Group G] {k m : ℕ} {μ : G →* AddMonoid.End (ι → ZMod 2)}
    {gens : Fin k → G} (hgen : Subgroup.closure (Set.range gens) = ⊤)
    {A : Fin k → Matrix ι ι (ZMod 2)} (hA : ∀ i v, μ (gens i) v = A i *ᵥ v)
    {rels : Fin m → List (Fin k)} (hrels : ∀ r, wordEval gens (rels r) = 1)
    (P : Fin k → Matrix ι ι (ZMod 2)) (C : Fin k → Fin m → Matrix ι ι (ZMod 2))
    (hcert : ∀ j l, (if j = l then 1 else 0) + (A j + 1) * P l =
      ∑ r, C j r * foxD A (rels r) l)
    {c : G → ι → ZMod 2} (hc : c ∈ Z1A μ) : c ∈ B1A μ := by
  set x : ι → ZMod 2 := ∑ l, P l *ᵥ c (gens l)
  have hv : ∀ j, c (gens j) = A j *ᵥ x + x + (0 : Matrix ι ι (ZMod 2)) *ᵥ
      (∑ l, (0 : Matrix ι ι (ZMod 2)) *ᵥ c (gens l)) :=
    eq_of_cert A (fun r l => foxD A (rels r) l) P 0 0 C
      (fun j l => by simpa using hcert j l) (fun r => fox_rel hA hc (hrels r))
  have hf' : c - coboundaryA μ x ∈ Z1A μ := sub_mem hc (B1A_le_Z1A _ ⟨x, rfl⟩)
  have h0 := eq_zero_of_vanish_closure hf' hgen (by
    rintro _ ⟨i, rfl⟩
    change c (gens i) - (μ (gens i) x - x) = 0
    rw [hv i, hA, zero_mulVec, add_zero, sub_eq_zero]
    funext p
    simp only [Pi.add_apply, Pi.sub_apply]
    generalize (A i *ᵥ x) p = a
    generalize x p = b
    revert a b
    decide)
  have e : c = coboundaryA μ x := sub_eq_zero.mp h0
  rw [e]
  exact ⟨x, rfl⟩

theorem exists_of_cert {G : Type*} [Group G] {k m : ℕ} {μ : G →* AddMonoid.End (ι → ZMod 2)}
    {gens : Fin k → G} {A : Fin k → Matrix ι ι (ZMod 2)} (hA : ∀ i v, μ (gens i) v = A i *ᵥ v)
    {rels : Fin m → List (Fin k)} (hrels : ∀ r, wordEval gens (rels r) = 1)
    (P F E : Fin k → Matrix ι ι (ZMod 2)) (C : Fin k → Fin m → Matrix ι ι (ZMod 2))
    (hcert : ∀ j l, (if j = l then 1 else 0) + (A j + 1) * P l + F j * E l =
      ∑ r, C j r * foxD A (rels r) l)
    {c : G → ι → ZMod 2} (hc : c ∈ Z1A μ) :
    ∃ x y : ι → ZMod 2, ∀ j, (c - coboundaryA μ x) (gens j) = F j *ᵥ y := by
  refine ⟨∑ l, P l *ᵥ c (gens l), ∑ l, E l *ᵥ c (gens l), fun j => ?_⟩
  have hv := eq_of_cert A (fun r l => foxD A (rels r) l) P F E C hcert
    (fun r => fox_rel hA hc (hrels r)) j
  change c (gens j) - (μ (gens j) _ - _) = _
  rw [hA, hv]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply]
  generalize (A j *ᵥ ∑ l, P l *ᵥ c (gens l)) p = a
  generalize (∑ l, P l *ᵥ c (gens l)) p = b
  generalize (F j *ᵥ ∑ l, E l *ᵥ c (gens l)) p = f
  revert a b f
  decide

end CFSG.Quasithin.B5.B49
