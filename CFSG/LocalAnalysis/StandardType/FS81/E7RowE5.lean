module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowE4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

variable {X : Subgroup (GL (Fin 8) (ZMod 3))} {δ : ZMod 3}

@[expose] def LineOrb (X : Subgroup (GL (Fin 8) (ZMod 3))) : Set (Coords 8) :=
  {e | OrbitLine X (Pi.single 0 1 + Pi.single 1 1) e}

@[expose] def qE8e (e : Coords 8) : ZMod 3 :=
  2 * (e 0 ^ 2 + e 1 ^ 2) + (e 2 ^ 2 + e 3 ^ 2 + e 4 ^ 2 + e 5 ^ 2 + e 6 ^ 2 + e 7 ^ 2)

theorem orbitLine_iff {v e : Coords 8} :
    OrbitLine X v e ↔ ∃ g ∈ X, ↑ₘg *ᵥ v = e ∨ ↑ₘg *ᵥ v = -e :=
  Iff.rfl

theorem qE8_eq_qE8e (e : Coords 8) : qE8 e = qE8e e := by
  rw [qE8_eq]
  rfl

@[expose] def qReps (δ : ZMod 3) : List (Coords 8) :=
  [![1, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, δ], ![1, 1, 1, 1, 1, 1, 1, -δ],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 0]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem qE8_classes (hδ : δ = 1 ∨ δ = -1) :
    ∀ e : Coords 8, qE8e e = 1 → nf e ∈ qReps δ ∨ nf (-e) ∈ qReps δ := by
  rcases hδ with rfl | rfl <;> decide +kernel

set_option maxRecDepth 100000 in
theorem chain_facts (hδ : δ = 1 ∨ δ = -1) :
    PhiPred δ ![0, 1, 1, 1, 1, 1, 1, δ] ∧
      nf (reflMe ![0, 1, 1, 1, 1, 1, 1, δ] ![1, 1, 0, 0, 0, 0, 0, 0]) = ![1, 1, 1, 1, 1, 1, 1, δ] ∧
    PhiPred δ ![1, 0, 1, 1, 1, 1, 1, -δ] ∧
      nf (-reflMe ![1, 0, 1, 1, 1, 1, 1, -δ] ![1, 1, 0, 0, 0, 0, 0, 0]) =
        ![1, 1, 1, 1, 1, 1, 1, -δ] ∧
    PhiPred δ ![1, 1, 0, 0, 0, 0, 0, 1] ∧
      nf (reflMe ![1, 1, 0, 0, 0, 0, 0, 1] ![1, 1, 0, 0, 0, 0, 0, 0]) = ![0, 0, 1, 0, 0, 0, 0, 0] ∧
    PhiPred δ ![0, 1, 1, 1, 1, 1, -1, -δ] ∧
      nf (reflMe ![0, 1, 1, 1, 1, 1, -1, -δ] ![1, 1, 1, 1, 1, 1, 1, δ]) =
        ![1, 0, 1, 1, 0, 0, 0, 0] ∧
    PhiPred δ ![1, 0, 1, 1, 1, -1, -1, -δ] ∧
      nf (-reflMe ![1, 0, 1, 1, 1, -1, -1, -δ] ![1, 1, 1, 1, 1, 1, 1, δ]) =
        ![1, 1, 1, 1, 1, 0, 0, 0] ∧
    PhiPred δ ![1, 0, 1, -1, -1, -1, -1, -δ] ∧
      nf (reflMe ![1, 0, 1, -1, -1, -1, -1, -δ] ![1, 1, 1, 1, 1, 1, 1, δ]) =
        ![0, 1, 1, 1, 1, 1, 1, 0] ∧
    PhiPred δ ![1, -1, 0, 0, 0, 0, 0, -δ] ∧
      nf (-reflMe ![1, -1, 0, 0, 0, 0, 0, -δ] ![1, 1, 1, 1, 1, 1, 1, δ]) =
        ![1, 0, 1, 1, 1, 1, 1, 0] ∧
    PhiPred δ ![1, 0, 1, 1, 1, 1, -1, δ] ∧
      nf (reflMe ![1, 0, 1, 1, 1, 1, -1, δ] ![1, 1, 1, 1, 1, 1, 1, -δ]) =
        ![0, 1, 1, 1, 0, 0, 0, 0] ∧
    PhiPred δ ![1, 0, 1, 1, 1, 1, 1, -δ] ∧
      nf (reflMe ![1, 0, 1, 1, 1, 1, 1, -δ] ![1, 0, 1, 1, 0, 0, 0, 0]) =
        ![0, 0, 1, 1, 1, 1, 0, 0] := by
  rcases hδ with rfl | rfl <;> decide +kernel

theorem lo_mul {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X) {e : Coords 8} (he : e ∈ LineOrb X) :
    ↑ₘx *ᵥ e ∈ LineOrb X := by
  obtain ⟨g, hg, hge | hge⟩ := orbitLine_iff.mp he
  · exact orbitLine_iff.mpr ⟨x * g, X.mul_mem hx hg, Or.inl (by rw [mulVec_gmul, hge])⟩
  · exact orbitLine_iff.mpr
      ⟨x * g, X.mul_mem hx hg, Or.inr (by rw [mulVec_gmul, hge, Matrix.mulVec_neg])⟩

theorem lo_neg {e : Coords 8} (he : e ∈ LineOrb X) : -e ∈ LineOrb X := by
  obtain ⟨g, hg, hge | hge⟩ := orbitLine_iff.mp he
  · exact orbitLine_iff.mpr ⟨g, hg, Or.inr (by rw [hge, neg_neg])⟩
  · exact orbitLine_iff.mpr ⟨g, hg, Or.inl hge⟩

namespace E8Data

variable (D : E8Data X δ)
include D

theorem lo_nf (e : Coords 8) : e ∈ LineOrb X ↔ nf e ∈ LineOrb X := by
  apply mem_iff_nf_mem
  intro g hg v hv
  obtain ⟨x, hx, hxA⟩ := D.core.exists_fix (Gen.mat_mem hg)
  rw [← Gen.mat_mulVec, ← hxA]
  exact lo_mul hx.1 hv

theorem lo_step {a w b : Coords 8} (ha : a ∈ LineOrb X) (hw : PhiPred δ w)
    (hb : nf (reflMe w a) = b ∨ nf (-reflMe w a) = b) : b ∈ LineOrb X := by
  obtain ⟨⟨m, hm, hmr⟩, -⟩ := D.phi_reflM ((D.phi_iff w).mpr hw)
  have h1 := lo_mul hm ha
  rw [hmr, reflM_mulVec_e] at h1
  rcases hb with hb | hb
  · rw [← hb]
    exact (D.lo_nf _).mp h1
  · rw [← hb]
    exact (D.lo_nf _).mp (lo_neg h1)

theorem reps_mem : ∀ b ∈ qReps δ, b ∈ LineOrb X := by
  obtain ⟨w1, s1, w2, s2, w3, s3, w4, s4, w5, s5, w6, s6, w7, s7, w8, s8, w9, s9⟩ :=
    chain_facts D.hδ
  have h0 : (![1, 1, 0, 0, 0, 0, 0, 0] : Coords 8) ∈ LineOrb X := by
    refine orbitLine_iff.mpr ⟨1, X.one_mem, Or.inl ?_⟩
    rw [Units.val_one, Matrix.one_mulVec]
    funext i
    fin_cases i <;> rfl
  have h1 := D.lo_step h0 w1 (Or.inl s1)
  have h2 := D.lo_step h0 w2 (Or.inr s2)
  have h3 := D.lo_step h0 w3 (Or.inl s3)
  have h4 := D.lo_step h1 w4 (Or.inl s4)
  have h5 := D.lo_step h1 w5 (Or.inr s5)
  have h6 := D.lo_step h1 w6 (Or.inl s6)
  have h7 := D.lo_step h1 w7 (Or.inr s7)
  have h8 := D.lo_step h2 w8 (Or.inl s8)
  have h9 := D.lo_step h4 w9 (Or.inl s9)
  intro b hb
  simp only [qReps, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

theorem orbitLine_e0e1 {e : Coords 8} :
    OrbitLine X (Pi.single 0 1 + Pi.single 1 1) e ↔ qE8 e = 1 := by
  have hq0 : qE8 (Pi.single 0 1 + Pi.single 1 1 : Coords 8) = 1 := by
    rw [qE8_eq_qE8e]
    decide
  rw [orbitLine_iff]
  constructor
  · rintro ⟨g, hg, hge | hge⟩
    · rw [← hge, qE8_mulVec_of_b8 (D.iso hg), hq0]
    · rw [← neg_neg e, qE8_neg, ← hge, qE8_mulVec_of_b8 (D.iso hg), hq0]
  · intro hq
    rw [qE8_eq_qE8e] at hq
    have hreps := D.reps_mem
    rcases qE8_classes D.hδ e hq with h | h
    · exact (D.lo_nf e).mpr (hreps _ h)
    · have := lo_neg ((D.lo_nf (-e)).mpr (hreps _ h))
      rwa [neg_neg] at this

end E8Data

end CFSG.StandardType.FrameRoute.FS81.E7Row

namespace CFSG.StandardType.FrameRoute.FS81

open E7Row

theorem e7MatCore_holds : E7MatCore := by
  intro X hH hstab hcard hA hodd hmove
  have h : CoreHyp X := ⟨hH, hstab, hcard, hA⟩
  obtain ⟨δ, hδ, horb⟩ := orb1_eq h
  obtain ⟨t, ht, htM⟩ := exists_t0 h hδ horb hodd hmove
  obtain ⟨g, hg, hgr⟩ := exists_root_orbit h hδ horb hodd hmove ht htM
  have D : E8Data X δ := ⟨h, hδ, horb, ⟨t, ht, htM⟩, ⟨g, hg, hgr⟩⟩
  refine ⟨δ, hδ, D.card_X, fun e he => ?_, fun e _ => D.orbitLine_e0e1⟩
  rw [orbitLine_iff]
  constructor
  · rintro ⟨y, hy, hye | hye⟩
    · exact (D.phi_iff_e8RootLine he).mp ⟨y, hy, hye⟩
    · have := D.phi_neg ⟨y, hy, hye⟩
      rw [neg_neg] at this
      exact (D.phi_iff_e8RootLine he).mp this
  · intro hE
    obtain ⟨y, hy, hye⟩ := (D.phi_iff_e8RootLine he).mpr hE
    exact ⟨y, hy, Or.inl hye⟩

end CFSG.StandardType.FrameRoute.FS81

end
