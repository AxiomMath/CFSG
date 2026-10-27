module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310NotQB
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth91a : Stroth91aStatement := by
  intro G _ _ M Q Z B hc n t hs
  exact hs.plus4

theorem Sec9Hyp.card_V {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec9Hyp hc n t) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 5 := by
  obtain ⟨K, fK, finK, hK, hrep⟩ := h.plus4
  have := card_of_naturalRep hrep (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hK
  rw [this]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem sec9_notQB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) : ¬ Vt M (LB M Q B) B Z t ≤ QB B := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV := hc.B_le_Vt hs5.mem
  have hVQ := hc.Vt_le_Q t
  obtain ⟨K, _, _, hK, φ, hφr, -, hsec⟩ := hs.plus4
  refine hc.not_le_QB_of_natural h35 hLR hZV hBV hVQ hK (ι := Fin 2 ⊕ Fin 2) ?_ φ hsec
    (polarBilin (quadPlus 2 K)) ?_
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rintro A ⟨s, rfl⟩ u hu hrank
    have hA : φ s ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rw [← hφr]
      exact ⟨s, rfl⟩
    exact omega_hform (coe_quadPlus 2 K) (nondegenerate_polarBilin_quadPlus 2 K) hA hu hrank

theorem stroth91c_of_34 (h34 : Stroth34Statement) : Stroth91cStatement := by
  intro G _ _ M Q Z B hc n t hs R V W hR hV hW
  subst hR hV hW
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  obtain ⟨h1, h2⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hs5.mem hs5.notQ
    (sec9_notQB h34 hs)
  have := hc.isChiIso_Q1_Ut hs5.mem
  rw [h2, h1]
  exact this

theorem Sec9Hyp.card_W (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) :
    Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * n - 3) := by
  have hs5 := hs.toSec5
  have hchi := stroth91c_of_34 h34 G M Q Z B hc n t hs (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  obtain ⟨K, fK, finK, hK, φ, -, -, hsec⟩ := hs.plus4
  obtain ⟨-, hN, -⟩ := hsec
  haveI := hN
  have hc' := card_mul_card_of_isChiIso hchi (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q)
    (sec39_Z_le_Vt : Z ≤ Vt M (LB M Q B) B Z t)
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs5.width
  have hn3 := hs5.n_gt
  rw [hw, hs.card_V] at hc'
  have h1 : Nat.card Z ^ (2 * n + 2) =
      Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 := by
    calc Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (2 * n + 1) * Nat.card Z := by ring
      _ = _ := hc'
  have h2 : Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (2 * n - 3) * Nat.card Z ^ 5 := by
    rw [← pow_add]
    congr 1
    omega
  have h5 : 0 < Nat.card Z ^ 5 := by positivity
  exact Nat.eq_of_mul_eq_mul_right h5 (h1.symm.trans h2)

end CFSG.RankThree.GF2n.Stroth80
