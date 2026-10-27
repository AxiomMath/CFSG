module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

@[expose] def vec (x y : ℤ) : Fin Tag.G2.rank → ℤ := ![x, y]

@[expose] def pairs12 : List ((Fin Tag.G2.rank → ℤ) × (Fin Tag.G2.rank → ℤ)) :=
  [(vec 1 0, vec 0 1), (vec 2 3, vec (-1) (-1)), (vec 1 3, vec (-1) (-2)),
   (vec (-1) 0, vec 0 (-1)), (vec (-2) (-3), vec 1 1), (vec (-1) (-3), vec 1 2),
   (vec 1 0, vec (-1) (-1)), (vec 2 3, vec (-1) (-2)), (vec 1 3, vec 0 (-1)),
   (vec (-1) 0, vec 1 1), (vec (-2) (-3), vec 1 2), (vec (-1) (-3), vec 0 1)]

theorem pairs12_closed : ∀ p ∈ pairs12, ∀ i : Fin Tag.G2.rank,
    (reflect Tag.G2 i p.1, reflect Tag.G2 i p.2) ∈ pairs12 := by
  decide +kernel

theorem weyl_pair_mem (w : WeylGroup Tag.G2) : (w • rA, w • rR) ∈ pairs12 := by
  refine (coxeterSystem Tag.G2).simple_induction_left
    (p := fun w : WeylGroup Tag.G2 => (w • rA, w • rR) ∈ pairs12) w ?_ ?_
  · simp only [one_smul]
    decide +kernel
  · intro w i hw
    rw [mul_smul, mul_smul, simple_smul, simple_smul]
    exact pairs12_closed _ hw i

theorem smul_eq_pair (w : WeylGroup Tag.G2) (v : Fin Tag.G2.rank → ℤ) :
    w • v = v i0 • (w • rA) + v i1 • (w • rR) := by
  rw [smul_eq_sum_smul_single w v]
  have h2 : ∀ f : Fin Tag.G2.rank → (Fin Tag.G2.rank → ℤ),
      ∑ j, f j = f i0 + f i1 := fun f => Fin.sum_univ_two f
  rw [h2, single_i0, single_i1]

theorem smul_apply_eq (w : WeylGroup Tag.G2) (v : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank) :
    (w • v) i = v i0 * (w • rA) i + v i1 * (w • rR) i := by
  rw [smul_eq_pair w v]
  simp

theorem fix_c_pairs : ∀ p ∈ pairs12, (2 • p.1 + 3 • p.2 = rC) → p.1 i0 = 1 ∧ p.2 i0 = 0 := by
  decide +kernel

theorem fix_v_pairs : ∀ p ∈ pairs12, (p.1 + 2 • p.2 = rV) → p.1 i1 = 0 ∧ p.2 i1 = 1 := by
  decide +kernel

theorem cases_v_pairs : ∀ p ∈ pairs12, (p.1 + 2 • p.2 = rV) ∨
    ((∀ δ ∈ [p.1 + 2 • p.2, p.1 + 3 • p.2, 2 • p.1 + 3 • p.2], 0 < height δ →
        δ ∈ [rA, rU, rB, rC]) ∨
      (∀ δ ∈ [p.1 + 2 • p.2, p.1 + 3 • p.2, 2 • p.1 + 3 • p.2], 0 < height δ →
        δ ∈ [rR, rB, rC])) := by
  decide +kernel

theorem smul_rC (w : WeylGroup Tag.G2) : w • rC = 2 • (w • rA) + 3 • (w • rR) := by
  rw [smul_eq_pair w rC]
  have e0 : rC i0 = 2 := rfl
  have e1 : rC i1 = 3 := rfl
  rw [e0, e1]
  simp

theorem smul_rV (w : WeylGroup Tag.G2) : w • rV = w • rA + 2 • (w • rR) := by
  rw [smul_eq_pair w rV]
  have e0 : rV i0 = 1 := rfl
  have e1 : rV i1 = 2 := rfl
  rw [e0, e1]
  simp

theorem smul_rB (w : WeylGroup Tag.G2) : w • rB = w • rA + 3 • (w • rR) := by
  rw [smul_eq_pair w rB]
  have e0 : rB i0 = 1 := rfl
  have e1 : rB i1 = 3 := rfl
  rw [e0, e1]
  simp

theorem weyl_fixes_c {w : WeylGroup Tag.G2} (h : w • rC = rC) :
    ∀ v : Fin Tag.G2.rank → ℤ, ∀ i ∉ ({i1} : Set (Fin Tag.G2.rank)), (w • v) i = v i := by
  intro v i hi
  have hi0 : i = i0 := by
    rcases fin_two_cases i with rfl | rfl
    · rfl
    · exact absurd (Set.mem_singleton _) hi
  obtain ⟨h1, h2⟩ := fix_c_pairs _ (weyl_pair_mem w) (by rw [← smul_rC]; exact h)
  rw [smul_apply_eq, hi0]
  have e1 : (w • rA) i0 = 1 := h1
  have e2 : (w • rR) i0 = 0 := h2
  rw [e1, e2]
  ring

theorem weyl_fixes_v {w : WeylGroup Tag.G2} (h : w • rV = rV) :
    ∀ v : Fin Tag.G2.rank → ℤ, ∀ i ∉ ({i0} : Set (Fin Tag.G2.rank)), (w • v) i = v i := by
  intro v i hi
  have hi1 : i = i1 := by
    rcases fin_two_cases i with rfl | rfl
    · exact absurd (Set.mem_singleton _) hi
    · rfl
  obtain ⟨h1, h2⟩ := fix_v_pairs _ (weyl_pair_mem w) (by rw [← smul_rV]; exact h)
  rw [smul_apply_eq, hi1]
  have e1 : (w • rA) i1 = 0 := h1
  have e2 : (w • rR) i1 = 1 := h2
  rw [e1, e2]
  ring

theorem weyl_cases_v (w : WeylGroup Tag.G2) :
    w • rV = rV ∨
      ((∀ δ ∈ [w • rV, w • rB, w • rC], 0 < height δ → δ ∈ [rA, rU, rB, rC]) ∨
        (∀ δ ∈ [w • rV, w • rB, w • rC], 0 < height δ → δ ∈ [rR, rB, rC])) := by
  have := cases_v_pairs _ (weyl_pair_mem w)
  rw [← smul_rV, ← smul_rB, ← smul_rC] at this
  exact this

end CFSG.Quasithin.H13.F431.G2.Cent
