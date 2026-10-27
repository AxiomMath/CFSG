module

public import CFSG.RankThree.PartOne.F106.U6Mono
public import Certificates.Data.U6NA

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix

namespace U6Mon

theorem sum_block_perm (t : Fin 2 → ZMod 3) (d : Fin 6 → ZMod 3) :
    d (u6Perm t 0) + d (u6Perm t 1) + d (u6Perm t 2) = d 0 + d 1 + d 2 := by
  have key : ∀ t : Fin 2 → ZMod 3,
      (u6Perm t 0 = 0 ∧ u6Perm t 1 = 1 ∧ u6Perm t 2 = 2) ∨
      (u6Perm t 0 = 1 ∧ u6Perm t 1 = 2 ∧ u6Perm t 2 = 0) ∨
      (u6Perm t 0 = 2 ∧ u6Perm t 1 = 0 ∧ u6Perm t 2 = 1) := by decide
  rcases key t with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> try ring

theorem blk_mul (x y : U6Mon) : (x.mul y).blk = x.blk + y.blk := by
  have h := sum_block_perm (-x.t) y.d
  have e : ∀ i, (x.mul y).d i = x.raw y i - x.raw y 0 := fun i => by
    rw [mul, d_ofFun]
  have key : ∀ (a b c u0 u1 u2 s : ZMod 3), u0 + u1 + u2 = s →
      0 + ((b + u1) - (a + u0)) + ((c + u2) - (a + u0)) = (a + b + c) + s := by decide
  have h0 : (x.mul y).d0 = 0 := by
    have := e 0
    rw [sub_self] at this
    exact this
  have h1 : (x.mul y).d1 = x.raw y 1 - x.raw y 0 := e 1
  have h2 : (x.mul y).d2 = x.raw y 2 - x.raw y 0 := e 2
  unfold blk
  rw [h0, h1, h2]
  exact key x.d0 x.d1 x.d2 (y.d (u6Perm (-x.t) 0)) (y.d (u6Perm (-x.t) 1))
    (y.d (u6Perm (-x.t) 2)) (y.d0 + y.d1 + y.d2) h

theorem t0_mul (x y : U6Mon) : (x.mul y).t0 = x.t0 + y.t0 := by
  have : (x.mul y).t = x.t + y.t := by rw [mul, t_ofFun]
  exact congrFun this 0

theorem t1_mul (x y : U6Mon) : (x.mul y).t1 = x.t1 + y.t1 := by
  have : (x.mul y).t = x.t + y.t := by rw [mul, t_ofFun]
  exact congrFun this 1

end U6Mon

namespace U6SylowCert

variable (c : U6SylowCert)

theorem tabArr_getD {i : ℕ} (hi : i < 729) : c.tabArr.getD i U6Mon.one = c.tab i := by
  simp [tabArr, hi]

structure NAFacts : Prop where
  e3 : ((List.range 729).filter fun i => (c.tab i).cubeB).length = 297
  y0 : ((List.range 729).filter fun i => decide ((c.tab i).blk = 0)).length = 243
  y0cube : ∀ i < 729, (c.tab i).blk = 0 → (c.tab i).cubeB = true
  zblk : U6Mon.zc.blk = 0
  zcube : U6Mon.zc.cubeB = true
  zne : U6Mon.zc ≠ U6Mon.one
  zidx : u6NaZ < 729 ∧ c.tab u6NaZ = U6Mon.zc
  oneTr : U6Mon.one.trB = true
  zcentral : ∀ i < 729, U6Mon.commB (c.tab i) U6Mon.zc = true
  qcount : ((List.range 729).filter fun i => decide ((c.tab i).blk = 0) && (c.tab i).qB).length
    = 48
  e0 : ((List.range 729).filter fun i => decide ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0)).length = 81
  a0 : ((List.range 729).filter fun i => decide ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) &&
    decide (i ≠ 0) && (c.tab i).trB).length = 30
  uniq : ∀ i < 729, ¬ ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) →
    ∃ C : List ℕ, (∀ j, j ∈ C ↔ (j < 729 ∧ (c.tab j).cubeB = true ∧
        U6Mon.commB (c.tab j) (c.tab i) = true)) ∧ C.length ≤ 81 ∧
      (C.length < 81 ∨ ∃ x ∈ C, ∃ y ∈ C, U6Mon.commB (c.tab x) (c.tab y) = false)

theorem NAFacts.of_naCheckWith (g : ℕ → U6Mon) (hg : ∀ i, i < 729 → g i = c.tab i)
    (h : naCheckWith g = true) : c.NAFacts := by
  unfold naCheckWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he3, hy0⟩, hy0c⟩, hzb⟩, hzc⟩, hzne⟩, hzi⟩, hone⟩, hzcent⟩, hq⟩, he0⟩, ha0⟩,
    huniq⟩ := h
  have hf : ∀ (p : ℕ → U6Mon → Bool),
      (List.range 729).filter (fun i => p i (g i)) =
        (List.range 729).filter (fun i => p i (c.tab i)) := fun p =>
    List.filter_congr fun i hi => by rw [hg i (List.mem_range.mp hi)]
  refine ⟨?_, ?_, ?_, hzb, hzc, hzne, ⟨hzi.1, ?_⟩, hone, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hf (fun _ x => x.cubeB)]; exact he3
  · rw [← hf (fun _ x => decide (x.blk = 0))]; exact hy0
  · intro i hi hb
    have := hy0c i hi
    rw [hg i hi] at this
    rcases this with h1 | h1
    · simp [hb] at h1
    · exact h1
  · rw [← hg u6NaZ hzi.1]; exact hzi.2
  · intro i hi
    have := hzcent i hi
    rwa [hg i hi] at this
  · rw [← hf (fun _ x => decide (x.blk = 0) && x.qB)]; exact hq
  · rw [← hf (fun _ x => decide (x.t0 = 0 ∧ x.t1 = 0))]; exact he0
  · rw [← hf (fun i x => decide (x.t0 = 0 ∧ x.t1 = 0) && decide (i ≠ 0) && x.trB)]; exact ha0
  · intro i hi hnt
    rcases huniq i hi with hU | hU
    · rw [hg i hi] at hU
      exact absurd hU hnt
    · have hmem : ∀ j, j ∈ (List.filter (fun j => U6Mon.commB (g j) (g i))
          (List.filter (fun i => (g i).cubeB) (List.range 729))) ↔
          (j < 729 ∧ (c.tab j).cubeB = true ∧ U6Mon.commB (c.tab j) (c.tab i) = true) := by
        intro j
        simp only [List.mem_filter, List.mem_range]
        constructor
        · rintro ⟨⟨hj, hc⟩, hcm⟩
          rw [hg j hj] at hc hcm
          rw [hg i hi] at hcm
          exact ⟨hj, hc, hcm⟩
        · rintro ⟨hj, hc, hcm⟩
          rw [hg j hj, hg i hi]
          exact ⟨⟨hj, hc⟩, hcm⟩
      unfold uniqOK at hU
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
        Bool.not_eq_true'] at hU
      obtain ⟨hle, hlt | ⟨x, hx, y, hy, hxy⟩⟩ := hU
      · exact ⟨_, hmem, hle, Or.inl hlt⟩
      · refine ⟨_, hmem, hle, Or.inr ⟨x, hx, y, hy, ?_⟩⟩
        have hx' := (hmem x).mp hx
        have hy' := (hmem y).mp hy
        rw [hg x hx'.1, hg y hy'.1] at hxy
        exact hxy

theorem NAFacts.of_naCheck (h : c.naCheck = true) : c.NAFacts :=
  NAFacts.of_naCheckWith c _ (fun _ hi => tabArr_getD c hi) h

end U6SylowCert

end CFSG.RankThree.PartOne.F106
