module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassKeys

public section

namespace Certificates.SUSmall

open CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conj_eq {m : ℕ} (r s : Pair m) :
    conj r s = ((s.1 - smDot r.2 s.1 • r.1, s.2 - smDot s.2 r.1 • r.2) : Pair m) := rfl

private lemma hdRo7SmRulesCAux_smDot_comm {m : ℕ} (w v : SMV m) : smDot w v = smDot v w := by
  simp only [smDot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma hdRo7SmRulesCAux_smDot_sub_single {m : ℕ} (v : SMV m) (i j : Fin m) :
    smDot v (Pi.single i 1 - Pi.single j 1) = v i - v j := by
  simp only [smDot, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma hdRo7SmRulesCAux_smDot_single_sub {m : ℕ} (v : SMV m) (i j : Fin m) :
    smDot (Pi.single i 1 - Pi.single j 1) v = v i - v j := by
  rw [hdRo7SmRulesCAux_smDot_comm, hdRo7SmRulesCAux_smDot_sub_single]

theorem smRCl_zeroPairZ {m : ℕ} {R : Set (SMV m × SMV m)} (hR : SMRCl R) {p : Pair m}
    (hp : p ∈ R) : zeroPairZ p = true := by
  rw [SMRCl] at hR
  obtain ⟨-, -, -, -, hSMT, hZero, -, -, -⟩ := hR
  rw [zeroPairZ, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  by_cases hij : i = j
  · subst hij; simp
  · let t : Pair m := (Pi.single i 1 - Pi.single j 1, Pi.single i 1 - Pi.single j 1)
    have ht : SMTClass t := ⟨i, j, 1, hij, Or.inl rfl, by simp [t], by simp [t]⟩
    have htR : t ∈ R := hSMT t ht
    have hz : p.2 i - p.2 j = 0 ↔ p.1 i - p.1 j = 0 := by
      have h := hZero p hp t htR
      dsimp only [t] at h
      rw [hdRo7SmRulesCAux_smDot_sub_single, hdRo7SmRulesCAux_smDot_single_sub] at h
      exact h
    rw [sub_eq_zero, sub_eq_zero] at hz
    exact hz.symm

theorem smRCl_class_closed {m : ℕ} {R : Set (SMV m × SMV m)} (hR : SMRCl R) {p q : Pair m}
    (hq : q ∈ R) (h : SMClass p q) : p ∈ R := by
  rw [SMRCl] at hR
  obtain ⟨-, hPerm, hNeg, -, -, -, -, -, -⟩ := hR
  obtain ⟨π, s, hs, hpq⟩ := h
  have hperm : ((fun i => q.1 (π i), fun i => q.2 (π i)) : Pair m) ∈ R := hPerm q hq π
  rcases hs with hs | hs
  · have hpeq : p = ((fun i => q.1 (π i), fun i => q.2 (π i)) : Pair m) := by
      apply Prod.ext
      · funext i; rw [(hpq i).1, hs, one_mul]
      · funext i; rw [(hpq i).2, hs, one_mul]
    rw [hpeq]; exact hperm
  · have hneg : ((-(fun i => q.1 (π i)), -(fun i => q.2 (π i))) : Pair m) ∈ R := hNeg _ hperm
    have hpeq : p = ((-(fun i => q.1 (π i)), -(fun i => q.2 (π i))) : Pair m) := by
      apply Prod.ext
      · funext i; rw [(hpq i).1, hs, neg_one_mul]; rfl
      · funext i; rw [(hpq i).2, hs, neg_one_mul]; rfl
    rw [hpeq]; exact hneg

theorem smRCl_conj_mem {m : ℕ} {R : Set (SMV m × SMV m)} (hR : SMRCl R) {r s : Pair m}
    (hr : r ∈ R) (hs : s ∈ R) : conj r s ∈ R := by
  rw [conj_eq]
  rw [SMRCl] at hR
  obtain ⟨-, -, -, hConj, -, -, -, -, -⟩ := hR
  exact hConj r hr s hs

private lemma hdRo7SmRulesCAux_sameLine_eq_true {m : ℕ} {a b : SMV m} :
    sameLine a b = true ↔ a = b ∨ a = -b := by
  rw [sameLine, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; funext i; simp [neg_one_mul])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; funext i; simp [neg_one_mul])

private lemma hdRo7SmRulesCAux_repeatedLine_eq_false {m : ℕ} {R : Set (SMV m × SMV m)}
    (hR : SMRCl R) {r s : Pair m} (hr : r ∈ R) (hs : s ∈ R) :
    repeatedLine r s = false := by
  rw [SMRCl] at hR
  obtain ⟨-, -, hNeg, -, -, -, hRoot, hFunc, -⟩ := hR
  let ns : Pair m := (fun i => -(s.1 i), fun i => -(s.2 i))
  have hnegmem : ns ∈ R := hNeg s hs
  have hmain : (sameLine r.1 s.1 || sameLine r.2 s.2) = true → r = s ∨ r = ns := by
    intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hdRo7SmRulesCAux_sameLine_eq_true] at h
      rcases h with h | h
      · exact Or.inl (Prod.ext h (hRoot r hr s hs h))
      · have h1 : ns.1 = r.1 := h.symm
        have h2 : ns.2 = r.2 := hRoot ns hnegmem r hr h1
        exact Or.inr (Prod.ext h1.symm h2.symm)
    · rw [hdRo7SmRulesCAux_sameLine_eq_true] at h
      rcases h with h | h
      · exact Or.inl (Prod.ext (hFunc r hr s hs h) h)
      · have h1 : ns.2 = r.2 := h.symm
        have h2 : ns.1 = r.1 := hFunc ns hnegmem r hr h1
        exact Or.inr (Prod.ext h2.symm h1.symm)
  rw [repeatedLine]
  by_cases hsame : (sameLine r.1 s.1 || sameLine r.2 s.2) = true
  · rcases hmain hsame with h | h
    · rw [h]; simp
    · rw [h]; dsimp only [ns]; simp
  · rw [Bool.not_eq_true] at hsame
    rw [hsame, Bool.and_false]

theorem smRCl_not_badPair {m : ℕ} {R : Set (SMV m × SMV m)} (hR : SMRCl R) {r s : Pair m}
    (hr : r ∈ R) (hs : s ∈ R) : badPair r s = false := by
  have hR' := hR
  rw [SMRCl] at hR'
  obtain ⟨-, -, -, -, -, hZero, -, -, hAxis⟩ := hR'
  have hc : conj r s ∈ R := smRCl_conj_mem hR hr hs
  have hzero : zeroPairZ (conj r s) = true := smRCl_zeroPairZ hR hc
  have hrepeat : repeatedLine r s = false :=
    hdRo7SmRulesCAux_repeatedLine_eq_false hR hr hs
  have hmismatch : ((smDot r.2 s.1 == 0) != (smDot s.2 r.1 == 0)) = false := by
    have heq : (smDot r.2 s.1 == 0) = (smDot s.2 r.1 == 0) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact hZero r hr s hs
    rw [heq]
    simp
  have hfix : fixesAxis (conj r s) = false := by
    rw [fixesAxis]
    by_cases hsum : (∑ i, (conj r s).2 i) = 0
    · have hsmt : SMTClass (conj r s) := hAxis (conj r s) hc hsum
      have htr : isTranspositionPair (conj r s) = true :=
        (isTranspositionPair_iff (conj r s)).mpr hsmt
      have hb : ((∑ i, (conj r s).2 i) == 0) = true := by
        rw [beq_iff_eq]; exact hsum
      rw [hb, htr]
      rfl
    · have hb : ((∑ i, (conj r s).2 i) == 0) = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact hsum (by rwa [beq_iff_eq] at h)
      rw [hb]
      rfl
  rw [badPair]
  rw [hrepeat, hmismatch, hzero, hfix]
  rfl

end Certificates.SUSmall

end
