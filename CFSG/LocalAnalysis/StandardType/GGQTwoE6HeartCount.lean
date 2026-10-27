module

public import Certificates.Data.E6Heart
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.StandardType.E6Heart

theorem mem_phiL (y : List ℕ) (i : ℕ) :
    i ∈ Certificates.E6Heart.phiL y ↔
      i < 72 ∧ Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt i) y = 0 := by
  simp only [Certificates.E6Heart.phiL, List.mem_filter, List.mem_range, beq_iff_eq]

theorem phiL_nodup (y : List ℕ) : (Certificates.E6Heart.phiL y).Nodup := by
  unfold Certificates.E6Heart.phiL
  exact (List.nodup_range (n := 72)).filter _

theorem repL_length (t : ℕ) : (Certificates.E6Heart.repL t).length = 6 := by
  rfl

theorem repL_injective {s t : ℕ} (hs : s < 243) (ht : t < 243)
    (h : Certificates.E6Heart.repL s = Certificates.E6Heart.repL t) : s = t := by
  simp only [Certificates.E6Heart.repL, List.cons.injEq, List.nil_eq, true_and,
    and_true] at h
  omega

private lemma ggE6c_m3_lt (z : ℤ) : Certificates.E6Heart.m3 z < 3 := by
  unfold Certificates.E6Heart.m3
  exact (Int.toNat_lt (Int.emod_nonneg z (by omega))).mpr
    (Int.emod_lt_of_pos z (by omega))

theorem qOf_lt (y : List ℕ) : Certificates.E6Heart.qOf y < 3 := by
  unfold Certificates.E6Heart.qOf
  exact ggE6c_m3_lt _

theorem pair3_lt (a : List ℤ) (y : List ℕ) : Certificates.E6Heart.pair3 a y < 3 := by
  unfold Certificates.E6Heart.pair3
  exact ggE6c_m3_lt _

private def ggE6c_subtypeEquivFin (n : ℕ) (p : ℕ → Bool) :
    {t : Fin n // p t = true} ≃ {t : ℕ // t < n ∧ p t = true} where
  toFun t := ⟨t.1.1, t.1.2, t.2⟩
  invFun t := ⟨⟨t.1, t.2.1⟩, t.2.2⟩
  left_inv t := by simp
  right_inv t := by simp

private lemma ggE6c_length_filter_range (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = Nat.card {t : Fin n // p t = true} := by
  rw [Nat.card_congr (ggE6c_subtypeEquivFin n p)]
  rw [← List.toFinset_card_of_nodup ((List.nodup_range (n := n)).filter p)]
  rw [List.toFinset_filter]
  have hfr : (List.range n).toFinset = Finset.range n := by
    ext x
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [hfr]
  have hcard : Nat.card {t : ℕ // t < n ∧ p t = true} =
      Finset.card ((Finset.range n).filter (fun t => p t)) :=
    Nat.subtype_card _ (by intro x; simp)
  rw [hcard]

private lemma ggE6c_card_subtype_congr {n : ℕ} {P Q : Fin n → Prop} (h : ∀ t, P t ↔ Q t) :
    Nat.card {t : Fin n // P t} = Nat.card {t : Fin n // Q t} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun t => h t))

theorem kerSize_eq (c : List ℕ) :
    Certificates.E6Heart.kerSize c = Nat.card {t : Fin 243 //
      ∀ i ∈ c, Certificates.E6Heart.pair3 (Certificates.E6Heart.rootAt i)
        (Certificates.E6Heart.repL t) = 0} := by
  unfold Certificates.E6Heart.kerSize
  rw [ggE6c_length_filter_range]
  apply ggE6c_card_subtype_congr
  intro t
  simp only [List.all_eq_true, beq_iff_eq]

theorem check_spec (h : Certificates.E6Heart.check () = true) :
    Certificates.E6Heart.rootsOk () = true ∧ Certificates.E6Heart.radOk () = true ∧
      (∀ t : Fin 243, t ≠ 0 → Certificates.E6Heart.goodAt t = true) ∧
      Certificates.E6Heart.cntQ 0 = 80 ∧ Certificates.E6Heart.cntQ 1 = 90 ∧
      Certificates.E6Heart.cntQ 2 = 72 := by
  unfold Certificates.E6Heart.check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  intro t ht
  rcases h3 (t : ℕ) t.2 with h0 | hg
  · exact absurd (Fin.ext h0) ht
  · exact hg

theorem goodAt_spec (t : ℕ) (h : Certificates.E6Heart.goodAt t = true) :
    (∀ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
      Certificates.E6Heart.closedIn (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
        (Certificates.E6Heart.compOf (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
          i) = true) ∧
    (Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 0 →
      ∀ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
        (Certificates.E6Heart.compOf (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
          i).length ≤ 6) ∧
    (Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) ≠ 0 →
      (∀ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
        6 < (Certificates.E6Heart.compOf
          (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i).length →
        ∀ j ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
          (Certificates.E6Heart.compOf
            (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) j).length ≤ 6 ∨
          j ∈ Certificates.E6Heart.compOf
            (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i) ∧
      ∃ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
        (Certificates.E6Heart.compOf (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
          i).length =
          (if Certificates.E6Heart.qOf (Certificates.E6Heart.repL t) = 1 then 24 else 30) ∧
        Certificates.E6Heart.kerSize (Certificates.E6Heart.compOf
          (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t)) i) = 3) := by
  unfold Certificates.E6Heart.goodAt at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  rw [List.all_eq_true] at hA
  have hclosed : ∀ i ∈ Certificates.E6Heart.phiL (Certificates.E6Heart.repL t),
      Certificates.E6Heart.closedIn (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
        (Certificates.E6Heart.compOf (Certificates.E6Heart.phiL (Certificates.E6Heart.repL t))
          i) = true := by
    intro i hi
    exact hA _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  refine ⟨hclosed, ?_, ?_⟩
  · intro hq i hi
    have hB0 := hB
    rw [if_pos (by simp [beq_iff_eq, hq])] at hB0
    rw [List.all_eq_true] at hB0
    simpa only [decide_eq_true_eq] using hB0 _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro hq
    have hB0 := hB
    rw [if_neg (by simp [beq_iff_eq, hq])] at hB0
    rw [Bool.and_eq_true] at hB0
    obtain ⟨hD, hE⟩ := hB0
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hD
      intro i hi hlen j hj
      have hp := hD _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [Bool.or_eq_true] at hp
      rcases hp with hl | hr
      · simp only [decide_eq_true_eq] at hl
        omega
      · rw [List.all_eq_true] at hr
        have hq2 := hr _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
        rw [Bool.or_eq_true] at hq2
        rcases hq2 with hl2 | hcont
        · exact Or.inl (decide_eq_true_eq.mp hl2)
        · exact Or.inr (List.contains_iff_mem.mp hcont)
    · rw [List.any_eq_true] at hE
      obtain ⟨p, hp_mem, hp_prop⟩ := hE
      rw [List.mem_map] at hp_mem
      obtain ⟨i, hi, rfl⟩ := hp_mem
      rw [Bool.and_eq_true] at hp_prop
      obtain ⟨hlen, hker⟩ := hp_prop
      refine ⟨i, hi, ?_, ?_⟩
      · simpa only [beq_iff_eq, decide_eq_true_eq] using hlen
      · simpa only [beq_iff_eq] using hker

end CFSG.StandardType.E6Heart

end

