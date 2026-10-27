module

public import CFSG.RankThree.PartOne.F106.NoQD32NANab
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Tab

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank

section Count

variable {K : Type} [Field K] [CharP K 2] {ω : Cube K} {hK : Nat.card K = (2 ^ 1) ^ 2}
  {c : U6SylowCert} [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] (T : U6Tab ω hK c)

include T

theorem U6Tab.sel_Z_mem (hna : c.NAFacts) : c.sel ω hK u6NaZ ∈ u6Y0 ω hK c :=
  (T.sel_mem_Y0 hna.zidx.1).mpr (by rw [hna.zidx.2]; exact hna.zblk)

theorem U6Tab.sel_Z_central (hna : c.NAFacts) :
    ∀ y ∈ u6Y0 ω hK c, y * c.sel ω hK u6NaZ = c.sel ω hK u6NaZ * y := by
  intro y hy
  obtain ⟨i, hi, -, rfl⟩ := T.mem_Y0.mp hy
  have h1 := hna.zcentral i hi
  rw [← hna.zidx.2] at h1
  exact (sel_comm_iff (ω := ω) (hK := hK) (c := c) i u6NaZ).mpr h1

omit [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] T in
theorem U6Tab.sel_Z_cube (hna : c.NAFacts) : c.sel ω hK u6NaZ ^ 3 = 1 := by
  rw [sel_cube_iff, hna.zidx.2]
  exact hna.zcube

omit [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] in
theorem U6Tab.sel_Z_ne_one (hna : c.NAFacts) : c.sel ω hK u6NaZ ≠ 1 := by
  intro h
  have h1 : u6NaZ = 0 := T.sel_inj _ hna.zidx.1 0 (by norm_num) (h.trans T.sel_zero.symm)
  have h2 := hna.zidx.2
  rw [h1, T.tab_zero] at h2
  exact hna.zne h2.symm

omit [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] in
theorem U6Tab.exists_mul_Z (hna : c.NAFacts) {i : ℕ} (hi : i < 729) :
    ∃ k < 729, c.sel ω hK i * c.sel ω hK u6NaZ = c.sel ω hK k ∧
      c.tab k = (c.tab i).mul U6Mon.zc := by
  obtain ⟨k, hk, hkeq⟩ := T.exists_sel _ (T.S.mul_mem (T.sel_mem i hi) (T.sel_mem _ hna.zidx.1))
  refine ⟨k, hk, hkeq, ?_⟩
  have := (sel_mul_eq_iff (ω := ω) (hK := hK) (c := c) i u6NaZ k).mp hkeq
  rw [hna.zidx.2] at this
  exact this.symm


open scoped _root_.Classical in
theorem U6Tab.card_Qset_Y0 (hna : c.NAFacts)
    (hZ : Nat.card (Subgroup.center ↥(u6Y0 ω hK c)) = 3) :
    Nat.card (Qset (u6Y0 ω hK c) (trZeroP (StatedSU 6 (2 ^ 1) K))) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y0 := u6Y0 ω hK c with hY0
  set z : StatedProj (StatedSU 6 (2 ^ 1) K) := c.sel ω hK u6NaZ with hz
  let z0 : ↥Y0 := ⟨z, T.sel_Z_mem hna⟩
  have hz0coe : (z0 : StatedProj (StatedSU 6 (2 ^ 1) K)) = z := rfl
  have hz0c : z0 ∈ Subgroup.center ↥Y0 := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (T.sel_Z_central hna g g.2)
  have hz03 : z0 ^ 3 = 1 := Subtype.ext (U6Tab.sel_Z_cube (ω := ω) (hK := hK) hna)
  have hz01 : z0 ≠ 1 := fun h => T.sel_Z_ne_one hna (congrArg Subtype.val h)
  have hord : orderOf z0 = 3 := orderOf_eq_prime hz03 hz01
  have hle : Subgroup.zpowers z0 ≤ Subgroup.center ↥Y0 := Subgroup.zpowers_le.mpr hz0c
  have hcardz : Nat.card (Subgroup.zpowers z0) = 3 := by rw [Nat.card_zpowers, hord]
  have hZeq : Subgroup.zpowers z0 = Subgroup.center ↥Y0 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcardz])
  have hmem : ∀ x : ↥Y0, x ∈ Subgroup.center ↥Y0 ↔ x = 1 ∨ x = z0 ∨ x = z0 * z0 := by
    intro x
    rw [← hZeq, mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      interval_cases k
      · exact Or.inl (pow_zero z0)
      · exact Or.inr (Or.inl (pow_one z0))
      · exact Or.inr (Or.inr (pow_two z0))
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp, pow_zero _⟩
      · exact ⟨1, by simp, pow_one _⟩
      · exact ⟨2, by simp, pow_two _⟩
  let QP : StatedProj (StatedSU 6 (2 ^ 1) K) → Prop := fun g =>
    ¬ trZeroP (StatedSU 6 (2 ^ 1) K) g ∧ ¬ trZeroP (StatedSU 6 (2 ^ 1) K) (g * z) ∧
      ¬ trZeroP (StatedSU 6 (2 ^ 1) K) (g * z * z)
  have hQ : ∀ y : ↥Y0, y ∈ Qset Y0 (trZeroP (StatedSU 6 (2 ^ 1) K)) ↔ QP (y : _) := by
    intro y
    constructor
    · intro hy
      refine ⟨?_, ?_, ?_⟩
      · have := mem_Qset.mp hy 1 (Subgroup.one_mem _)
        simpa using this
      · exact mem_Qset.mp hy z0 hz0c
      · have := mem_Qset.mp hy (z0 * z0) ((hmem _).mpr (Or.inr (Or.inr rfl)))
        have e : ((y * (z0 * z0) : ↥Y0) : StatedProj (StatedSU 6 (2 ^ 1) K)) = y * z * z := by
          rw [← mul_assoc]
          rfl
        rwa [e] at this
    · rintro ⟨h1, h2, h3⟩
      refine mem_Qset.mpr fun c hc => ?_
      rcases (hmem c).mp hc with rfl | rfl | rfl
      · simpa using h1
      · exact h2
      · have e : ((y * (z0 * z0) : ↥Y0) : StatedProj (StatedSU 6 (2 ^ 1) K)) = y * z * z := by
          rw [← mul_assoc]
          rfl
        rw [e]
        exact h3
  rw [Nat.card_congr (Equiv.subtypeEquivRight hQ),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ Y0) QP)]
  have h := card_set_eq_filter T.S (c.sel ω hK) (fun g => g ∈ Y0 ∧ QP g) T.sel_inj T.exists_sel
    T.sel_mem
  have hset : {g : StatedProj (StatedSU 6 (2 ^ 1) K) // g ∈ Y0 ∧ QP g} =
      {g : StatedProj (StatedSU 6 (2 ^ 1) K) // g ∈ T.S ∧ (g ∈ Y0 ∧ QP g)} := by
    congr 1
    ext g
    constructor
    · intro hg
      exact ⟨T.Y0_le hg.1, hg⟩
    · intro hg
      exact hg.2
  rw [hset, h]
  rw [card_filter_range_eq_length 729 _
    (fun i => decide ((c.tab i).blk = 0) && (c.tab i).qB)]
  · exact hna.qcount
  · intro i hi
    obtain ⟨k1, hk1, hs1, ht1⟩ := T.exists_mul_Z hna hi
    obtain ⟨k2, hk2, hs2, ht2⟩ := T.exists_mul_Z hna hk1
    have e1 := sel_trZero_iff (ω := ω) (hK := hK) (c := c) i
    have e2 := sel_trZero_iff (ω := ω) (hK := hK) (c := c) k1
    have e3 := sel_trZero_iff (ω := ω) (hK := hK) (c := c) k2
    have hb := T.sel_mem_Y0 (ω := ω) (hK := hK) (c := c) hi
    show (c.sel ω hK i ∈ Y0 ∧ (¬ trZeroP (StatedSU 6 (2 ^ 1) K) (c.sel ω hK i) ∧
      ¬ trZeroP (StatedSU 6 (2 ^ 1) K) (c.sel ω hK i * c.sel ω hK u6NaZ) ∧
      ¬ trZeroP (StatedSU 6 (2 ^ 1) K) (c.sel ω hK i * c.sel ω hK u6NaZ * c.sel ω hK u6NaZ))) ↔
        _
    rw [hs1, hs2, hb, e1, e2, e3, ht2, ht1]
    simp [U6Mon.qB, and_assoc]

end Count

end CFSG.RankThree.PartOne.F106
