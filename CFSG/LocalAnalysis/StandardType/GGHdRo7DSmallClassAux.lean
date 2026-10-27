module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DSmClassAuxAux_all_ne_of_supp_eq {n : ℕ} {h : DV n} (hs : dSupp h = n) :
    ∀ i : Fin n, h i.succ ≠ 0 := by
  have hcard : (Finset.univ.filter fun i : Fin n => h i.succ ≠ 0).card =
      (Finset.univ : Finset (Fin n)).card := by
    simpa [dSupp, Finset.card_univ, Fintype.card_fin] using hs
  intro i
  exact Finset.card_filter_eq_iff.mp hcard i (Finset.mem_univ i)

private theorem hdRo7DSmClassAuxAux_supp_eq_of_all_ne {n : ℕ} {h : DV n}
    (hall : ∀ i : Fin n, h i.succ ≠ 0) : dSupp h = n := by
  rw [dSupp, Finset.filter_true_of_mem (fun i _ => hall i), Finset.card_univ, Fintype.card_fin]

private theorem hdRo7DSmClassAuxAux_filter_eq_one {n : ℕ} {h : DV n} {i : Fin n}
    (hi : h i.succ ≠ 0) (hrest : ∀ k : Fin n, k ≠ i → h k.succ = 0) :
    Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) = {i} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hne
    exact hk (hrest k hne)
  · rintro rfl
    exact hi

private theorem hdRo7DSmClassAuxAux_filter_eq_two {n : ℕ} {h : DV n} {i j : Fin n}
    (hij : i ≠ j) (hi : h i.succ ≠ 0) (hj : h j.succ ≠ 0)
    (hrest : ∀ k : Fin n, k ≠ i → k ≠ j → h k.succ = 0) :
    Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) = {i, j} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hne
    simp only [not_or] at hne
    exact hk (hrest k hne.1 hne.2)
  · rintro (rfl | rfl)
    · exact hi
    · exact hj

private theorem hdRo7DSmClassAuxAux_filter_eq_empty {n : ℕ} {h : DV n}
    (hrest : ∀ k : Fin n, h k.succ = 0) :
    Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) = ∅ := by
  ext k
  simp [hrest k]

private theorem hdRo7DSmClassAuxAux_sum_sq {n : ℕ} (h : DV n) :
    (∑ i : Fin n, h i.succ * h i.succ) = (dSupp h : ZMod 3) := by
  have hsq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  rw [dSupp, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : h i.succ = 0
  · simp [hi]
  · rw [hsq _ hi]
    simp [hi]

private theorem hdRo7DSmClassAuxAux_supp_eq_iff {n : ℕ} (h : DV n) :
    dSupp h = n ↔ ∀ i : Fin n, h i.succ ≠ 0 :=
  ⟨fun hs => hdRo7DSmClassAuxAux_all_ne_of_supp_eq hs, hdRo7DSmClassAuxAux_supp_eq_of_all_ne⟩

theorem dRCl_mem_of_ext (hT : DSmTransLeaf) {n : ℕ} {ρ : ZMod 3} {Φ : Set (DV n)}
    (hΦ : DRCl ρ Φ) {h g : DV n} (hh : h ∈ Φ) (h0 : h 0 ≠ 0) (g0 : g 0 ≠ 0)
    (hs : dSupp h = dSupp g) (hsg : dSupp h = n → dSgn h = dSgn g) : g ∈ Φ := by
  obtain ⟨σ, c, hd, hgc⟩ := hT.1 n h g h0 g0 hs hsg
  rw [DRCl] at hΦ
  obtain ⟨-, hneg, -, hP, -, -, -⟩ := hΦ
  have h1 : dAct σ c h ∈ Φ := hP h hh σ c hd
  rcases hgc with hgc | hgc
  · rwa [hgc] at h1
  · have h2 := hneg (dAct σ c h) h1
    rwa [hgc, neg_neg] at h2

theorem dRCl_mem_of_int (hT : DSmTransLeaf) {n : ℕ} {ρ : ZMod 3} {Φ : Set (DV n)}
    (hΦ : DRCl ρ Φ) {h g : DV n} (hh : h ∈ Φ) (h0 : h 0 = 0) (g0 : g 0 = 0) (hs : dSupp h = 1)
    (hg : dSupp g = 1) : g ∈ Φ := by
  obtain ⟨σ, c, hd, hgc⟩ := hT.2 n h g h0 g0 hs hg
  rw [DRCl] at hΦ
  obtain ⟨-, hneg, -, hP, -, -, -⟩ := hΦ
  have h1 : dAct σ c h ∈ Φ := hP h hh σ c hd
  rcases hgc with hgc | hgc
  · rwa [hgc] at h1
  · have h2 := hneg (dAct σ c h) h1
    rwa [hgc, neg_neg] at h2

theorem dRCl_false_of_bad {n : ℕ} {ρ : ZMod 3} {Φ : Set (DV n)} (hΦ : DRCl ρ Φ) {h g : DV n}
    (hh : h ∈ Φ) (hg : g ∈ Φ) (h0 : dRef ρ h g 0 = 0)
    (hbad : ¬ (dIsD (dRef ρ h g) ∨ dIsO (dRef ρ h g))) : False := by
  rw [DRCl] at hΦ
  obtain ⟨-, -, hRef, -, -, hF, -⟩ := hΦ
  exact hbad (hF (dRef ρ h g) (hRef h hh g hg) h0)

theorem dB_self_of_ne {n : ℕ} (ρ : ZMod 3) {h : DV n} (h0 : h 0 ≠ 0) :
    dB ρ h h = ρ + (dSupp h : ZMod 3) := by
  have hsq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  have hrho : ρ * h 0 * h 0 = ρ := by
    rw [mul_assoc, hsq _ h0, mul_one]
  rw [dB, hdRo7DSmClassAuxAux_sum_sq, hrho]

theorem dB_self_of_eq {n : ℕ} (ρ : ZMod 3) {h : DV n} (h0 : h 0 = 0) :
    dB ρ h h = (dSupp h : ZMod 3) := by
  have hrho : ρ * h 0 * h 0 = 0 := by
    rw [h0]
    ring
  rw [dB, hdRo7DSmClassAuxAux_sum_sq, hrho, zero_add]

theorem dSupp_le {n : ℕ} (h : DV n) : dSupp h ≤ n := by
  unfold dSupp
  simpa [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => h i.succ ≠ 0))

theorem dSgn_of_full {n : ℕ} {h : DV n} (h0 : h 0 ≠ 0) (hs : dSupp h = n) :
    dSgn h = 1 ∨ dSgn h = -1 := by
  have hpm : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  have hall : ∀ i : Fin n, h i.succ ≠ 0 := hdRo7DSmClassAuxAux_all_ne_of_supp_eq hs
  rw [dSgn]
  refine Finset.prod_induction (fun i : Fin n => h 0 * h i.succ) (fun x => x = 1 ∨ x = -1)
    ?_ (Or.inl rfl) ?_
  · intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  · intro i _
    rcases hpm _ h0 with h1 | h1 <;> rcases hpm _ (hall i) with h2 | h2 <;>
      rw [h1, h2] <;> decide

theorem eq_smul_dE_of_dSupp_zero {n : ℕ} {h : DV n} (hs : dSupp h = 0) : h = h 0 • dE n 0 := by
  have hempty : Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) = ∅ := by
    rw [← Finset.card_eq_zero, ← dSupp]
    exact hs
  have hall : ∀ i : Fin n, h i.succ = 0 := by
    intro i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) := by
      simpa using hi
    rw [hempty] at hmem
    exact Finset.notMem_empty i hmem
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [dE]
  · intro i
    simp [dE, hall i]

theorem dIsD_iff {n : ℕ} (h : DV n) :
    dIsD h ↔ (h 0 = 0 ∧ dSupp h = 2) ∨ (h 0 ≠ 0 ∧ dSupp h = 1) := by
  constructor
  · rintro ⟨i, j, hij, hi, hj, hrest⟩
    by_cases hi0 : i = 0
    · subst hi0
      have hj0 : j ≠ 0 := by rintro rfl; exact hij rfl
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
      right
      refine ⟨hi, ?_⟩
      rw [dSupp, hdRo7DSmClassAuxAux_filter_eq_one hj ?_, Finset.card_singleton]
      intro k hk
      exact hrest k.succ (Fin.succ_ne_zero k)
        (fun hk' => hk (Fin.succ_injective _ hk'))
    · by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
        right
        refine ⟨hj, ?_⟩
        rw [dSupp, hdRo7DSmClassAuxAux_filter_eq_one hi ?_, Finset.card_singleton]
        intro k hk
        exact hrest k.succ (fun hk' => hk (Fin.succ_injective _ hk'))
          (Fin.succ_ne_zero k)
      · left
        have hzero : h 0 = 0 := hrest 0 (Ne.symm hi0) (Ne.symm hj0)
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
        have hij' : i' ≠ j' := fun hh => hij (by rw [hh])
        refine ⟨hzero, ?_⟩
        rw [dSupp, hdRo7DSmClassAuxAux_filter_eq_two hij' hi hj ?_,
          Finset.card_pair hij']
        intro k hk hk'
        exact hrest k.succ (fun hh => hk (Fin.succ_injective _ hh))
          (fun hh => hk' (Fin.succ_injective _ hh))
  · rintro (⟨hzero, hs2⟩ | ⟨hzero, hs1⟩)
    · obtain ⟨i, j, hij, hf⟩ := Finset.card_eq_two.mp hs2
      refine ⟨i.succ, j.succ, fun hh => hij (Fin.succ_injective _ hh), ?_, ?_, ?_⟩
      · have hm : i ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          rw [hf]; simp
        simpa using hm
      · have hm : j ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          rw [hf]; simp
        simpa using hm
      · intro k hki hkj
        by_contra hk
        have hk0 : k ≠ 0 := by
          intro hkzero
          exact hk (by rw [hkzero]; exact hzero)
        obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk0
        have hm : l ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          simpa using hk
        rw [hf] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact hki rfl
        · exact hkj rfl
    · obtain ⟨i, hf⟩ := Finset.card_eq_one.mp hs1
      refine ⟨0, i.succ, (Fin.succ_ne_zero i).symm, hzero, ?_, ?_⟩
      · have hm : i ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          rw [hf]; simp
        simpa using hm
      · intro k hk0 hki
        by_contra hk
        obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk0
        have hm : l ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          simpa using hk
        rw [hf] at hm
        simp only [Finset.mem_singleton] at hm
        exact hki (by rw [hm])

theorem dIsO_iff {n : ℕ} (h : DV n) :
    dIsO h ↔ (h 0 = 0 ∧ dSupp h = 1) ∨ (h 0 ≠ 0 ∧ dSupp h = 0) := by
  constructor
  · rintro ⟨i, hi, hrest⟩
    by_cases hi0 : i = 0
    · subst hi0
      right
      have hempty : Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) = ∅ :=
        hdRo7DSmClassAuxAux_filter_eq_empty (fun k => hrest k.succ (Fin.succ_ne_zero k))
      refine ⟨hi, ?_⟩
      rw [dSupp, hempty, Finset.card_empty]
    · left
      have hzero : h 0 = 0 := hrest 0 (Ne.symm hi0)
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
      refine ⟨hzero, ?_⟩
      rw [dSupp, hdRo7DSmClassAuxAux_filter_eq_one hi ?_, Finset.card_singleton]
      intro k hk
      exact hrest k.succ (fun hh => hk (Fin.succ_injective _ hh))
  · rintro (⟨hzero, hs1⟩ | ⟨hzero, hs0⟩)
    · obtain ⟨i, hf⟩ := Finset.card_eq_one.mp hs1
      refine ⟨i.succ, ?_, ?_⟩
      · have hm : i ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          rw [hf]; simp
        simpa using hm
      · intro k hki
        by_contra hk
        have hk0 : k ≠ 0 := by
          intro hkzero
          exact hk (by rw [hkzero]; exact hzero)
        obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk0
        have hm : l ∈ Finset.univ.filter (fun k : Fin n => h k.succ ≠ 0) := by
          simpa using hk
        rw [hf] at hm
        simp only [Finset.mem_singleton] at hm
        exact hki (by rw [hm])
    · have hempty : Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) = ∅ := by
        rw [← Finset.card_eq_zero, ← dSupp]
        exact hs0
      have hall : ∀ i : Fin n, h i.succ = 0 := by
        intro i
        by_contra hi
        have hmem : i ∈ Finset.univ.filter (fun i : Fin n => h i.succ ≠ 0) := by
          simpa using hi
        rw [hempty] at hmem
        exact Finset.notMem_empty i hmem
      refine ⟨0, hzero, ?_⟩
      intro k hk
      obtain ⟨l, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk
      exact hall l

theorem dIsS_iff {n : ℕ} (ε : ZMod 3) (h : DV n) :
    dIsS ε h ↔ h 0 ≠ 0 ∧ dSupp h = n ∧ dSgn h = ε := by
  rw [dIsS, hdRo7DSmClassAuxAux_supp_eq_iff h]

end CFSG.StandardType.HdRo7D.Small
