module

public import Certificates.Data.F4NA

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.LieType.Simplicity.TitsBits

namespace F4SylowCert

variable (c : F4SylowCert) (tb : ℕ → ℕ)

theorem homOK_iff (w : List ℕ) :
    c.homOK w = true ↔ ∀ i < 729, ∀ g < 6,
      c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3 := by
  simp only [homOK, List.all_eq_true, List.mem_range, decide_eq_true_eq]

structure NAFacts : Prop where
  homA : ∀ i < 729, ∀ g < 6, c.wt f4WA (c.rtv i g) = (c.wt f4WA i + f4WA.getD g 0) % 3
  homB : ∀ i < 729, ∀ g < 6, c.wt f4WB (c.rtv i g) = (c.wt f4WB i + f4WB.getD g 0) % 3
  homC : ∀ i < 729, ∀ g < 6, c.wt f4WC (c.rtv i g) = (c.wt f4WC i + f4WC.getD g 0) % 3
  homY2 : ∀ i < 729, ∀ g < 6, c.wt f4WY2 (c.rtv i g) = (c.wt f4WY2 i + f4WY2.getD g 0) % 3
  cover : ∀ i < 729, cubeF tb i = true ↔
    (c.wt f4WA i = 0 ∨ c.wt f4WB i = 0 ∨ c.wt f4WC i = 0)
  cardA : ((List.range 729).filter fun i => c.wt f4WA i == 0).length = 243
  cardB : ((List.range 729).filter fun i => c.wt f4WB i == 0).length = 243
  cardC : ((List.range 729).filter fun i => c.wt f4WC i == 0).length = 243
  cardE0 : ((List.range 729).filter fun i => c.wt f4WA i == 0 && c.wt f4WY2 i == 0).length = 81
  zbWt : c.wt f4WB f4NaZ = 0
  zbNe : f4NaZ ≠ 0
  zbCube : cubeF tb f4NaZ = true
  zbComm : ∀ j < 729, c.wt f4WB j = 0 → commF tb f4NaZ j = true
  zbTr : trIB (tb f4NaZ) = true
  zaLen : f4ZaList.length = 9
  zaNodup : f4ZaList.Nodup
  zaCent : ∀ z ∈ f4ZaList, z < 729 ∧ c.wt f4WA z = 0 ∧
    ∀ j < 729, c.wt f4WA j = 0 → commF tb z j = true
  zcLen : f4ZcList.length = 9
  zcNodup : f4ZcList.Nodup
  zcCent : ∀ z ∈ f4ZcList, z < 729 ∧ c.wt f4WC z = 0 ∧
    ∀ j < 729, c.wt f4WC j = 0 → commF tb z j = true
  qcount : ((List.range 729).filter fun i => c.wt f4WB i == 0 && qF tb i).length = 24
  a0count : ((List.range 729).filter fun i => c.wt f4WA i == 0 && c.wt f4WY2 i == 0 &&
    decide (i ≠ 0) && !trIB (tb i)).length = 24
  uniq : ∀ i < 729, cubeF tb i = true → ¬ (c.wt f4WA i = 0 ∧ c.wt f4WY2 i = 0) →
    ∃ C : List ℕ, (∀ j, j ∈ C ↔ (j < 729 ∧ cubeF tb j = true ∧ commF tb j i = true)) ∧
      C.length ≤ 81 ∧ (C.length < 81 ∨ ∃ x ∈ C, ∃ y ∈ C, commF tb x y = false)

variable {c tb}

theorem NAFacts.of_naCheckWith (h : c.naCheckWith tb = true) : c.NAFacts tb := by
  unfold naCheckWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, hA, hB, hC, hE0, z1, z2, z3, z4, z5, a1, a2, a3, b1, b2, b3, hq,
    ha0, hu⟩ := h
  rw [homOK_iff] at h1 h2 h3 h4
  simp only [beq_iff_eq] at z1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at z4
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, and_assoc] at a3 b3
  refine ⟨h1, h2, h3, h4, ?_, hA, hB, hC, hE0, z1, z2, z3, ?_, z5, a1, a2, ?_, b1, b2, ?_, hq, ha0,
    ?_⟩
  · intro i hi
    have := List.all_eq_true.1 h5 i (List.mem_range.2 hi)
    rw [beq_iff_eq, Bool.eq_iff_iff] at this
    rw [this]
    simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]
  · intro j hj hw
    rcases z4 j hj with h | h
    · exact absurd hw h
    · exact h
  · intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := a3 z hz
    refine ⟨hz1, hz2, fun j hj hw => ?_⟩
    rcases hz3 j hj with h | h
    · exact absurd hw h
    · exact h
  · intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := b3 z hz
    refine ⟨hz1, hz2, fun j hj hw => ?_⟩
    rcases hz3 j hj with h | h
    · exact absurd hw h
    · exact h
  · intro i hi hcube hnt
    have := List.all_eq_true.1 hu i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd hcube (by simp [h])
    · exact absurd h hnt
    · have hmem : ∀ j, j ∈ (List.filter (fun j => commF tb j i)
          (List.filter (fun i => cubeF tb i) (List.range 729))) ↔
          (j < 729 ∧ cubeF tb j = true ∧ commF tb j i = true) := by
        intro j
        simp only [List.mem_filter, List.mem_range]
        constructor
        · rintro ⟨⟨hj, hc⟩, hcm⟩
          exact ⟨hj, hc, hcm⟩
        · rintro ⟨hj, hc, hcm⟩
          exact ⟨⟨hj, hc⟩, hcm⟩
      unfold uniqF at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
        Bool.not_eq_true'] at h
      obtain ⟨hle, hlt | ⟨x, hx, y, hy, hxy⟩⟩ := h
      · exact ⟨_, hmem, hle, Or.inl hlt⟩
      · exact ⟨_, hmem, hle, Or.inr ⟨x, hx, y, hy, hxy⟩⟩

theorem NAFacts.of_naCheck (h : c.naCheck = true) : c.NAFacts fun i => c.tabArr.getD i 0 :=
  NAFacts.of_naCheckWith h

end F4SylowCert

end CFSG.RankThree.PartOne.F106
