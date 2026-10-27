module

public import CFSG.Quasithin.Recognition.St84.Sec5Basic
public import CFSG.Quasithin.Recognition.St84.Gen.MixedCentralZData
import CFSG.Quasithin.Recognition.St84.Sec5Step89
import CFSG.Quasithin.Recognition.St84.Sec5Step7
import CFSG.Quasithin.Recognition.St84.HigmanQuadProof
import CFSG.Quasithin.Recognition.St84.Sec68E
import CFSG.Quasithin.Recognition.St84.Gen.Sec7Gen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

theorem Setup.nOf_ne_of_adj (Y : Setup Γ G) (hne : Y.n 0 ≠ Y.n 1) :
    ∀ v w : V, Γ.Adj v w → nOf Γ v ≠ nOf Γ w := by
  intro v w hvw
  obtain ⟨g, -, hg | hg⟩ := Y.hyp.edgeTrans (Y.vert 0) (Y.vert 1) v w (Y.adj 0) hvw
  · have hv := Y.hyp.nOf_smul g (Y.vert 0)
    have hw := Y.hyp.nOf_smul g (Y.vert 1)
    rw [← hg.1, ← hg.2, hv, hw]
    exact hne
  · have hv := Y.hyp.nOf_smul g (Y.vert 1)
    have hw := Y.hyp.nOf_smul g (Y.vert 0)
    rw [← hg.1, ← hg.2, hv, hw]
    exact hne.symm

theorem Setup.not_rightTransitive_or_shift_one (Y : Setup Γ G) (hs : IsSingularity Γ G s)
    (hodd : Odd s) :
    ¬ RightTransitive Γ G (Y.line.arc 0 s).vert 0 s ∨
      ¬ RightTransitive Γ G ((Y.shift 1).line.arc 0 s).vert 0 s := by
  obtain ⟨o, ho, -⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
    (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts hs hodd
  rcases Nat.even_or_odd (Γ.dist o (Y.vert 0)) with hd0 | hd0
  · refine Or.inl ((ho s le_rfl (Y.line.arc 0 s)).1 ?_)
    simpa [Line.arc] using Y.odd_dist_vert_of_even o hodd hd0
  · refine Or.inr ((ho s le_rfl ((Y.shift 1).line.arc 0 s)).1 ?_)
    simpa [Line.arc] using Y.odd_dist_vert_succ_of_odd o hodd hd0

theorem Setup.odd_card_GT (hc : CharTwoStab (V := V) (G := G)) (Y : Setup Γ G)
    (hmax : 2 ≤ Y.n 0 ∨ 2 ≤ Y.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s) :
    Odd (Nat.card Y.GT) := by
  refine Nat.not_even_iff_odd.mp fun hEven => ?_
  rcases Y.not_rightTransitive_or_shift_one hs hodd with hX | hX
  · exact sec6_false hc Y hmax hs hodd h5 hX hEven
  · have h1 : (Y.shift 1).n 1 = Y.n 0 := by
      rw [Setup.shift_n]
      simpa using Y.n_add 1 0
    refine sec6_false hc (Y.shift 1) ?_ hs hodd h5 hX (by simpa [Setup.shift_GT] using hEven)
    rw [h1, Setup.shift_n, zero_add]
    exact hmax.symm

theorem Setup.n_eq_two_of_Zt_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) : n₀ = 2 := by
  obtain ⟨l, r₀, -, -, he0⟩ := Y.exists_ZtExt H hZ
  obtain ⟨hlr, -⟩ := Y.s52_step1 H hZ he0
  have he : Y.ZtExt 0 r₀ r₀ := hlr ▸ he0
  obtain ⟨r, -, -, hr⟩ := Y.exists_isMaxRegLen H
  have h2 := Y.s52_step2 H hZ hr he
  have h3 := Y.s52_step3 H hZ hr he h2
  have h4 := (Y.s52_step4 H hZ h3).1
  have h5a := Y.s52_step5 H hZ h3 he (higmanQuad n₀)
  have hev : Y.reverse.ZtExt 0 r₀ r₀ := he.reverse
  have hZrev : Y.reverse.Zt 0 ≠ ⊥ := by
    rw [Setup.Zt, Setup.reverse_Z, Setup.reverse_K]
    simpa [Setup.Zt] using hZ
  have h3rev : Y.reverse.Zt 1 = ⊥ := by
    have hrevZt : Y.reverse.Zt 1 = Y.Zt (-1) := by
      rw [Setup.Zt, Setup.reverse_Z, Setup.reverse_K]
      simp [Setup.Zt]
    rw [hrevZt]
    have h := Y.Zt_add_two (1 : ℤ) (-1)
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
    rw [h, h3, Subgroup.map_bot]
  have h5b : ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ)) := by
    have h := (Y.reverse).s52_step5 H.reverse hZrev h3rev hev (higmanQuad n₀)
    rwa [Setup.reverse_Z, Setup.reverse_Gi] at h
  have h6 := Y.s52_step6 H hZ h3 hr he h2 ⟨h5a, h5b⟩
  have hb := Y.s52_step7 H hZ h3 h4 hr he h2 ⟨h5a, h5b⟩ h6 (higmanQuad n₀)
  exact (Y.caseA_n H hZ h3 h4 hb he).1

theorem Setup.centralZData_of_three_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (h3 : 3 ≤ n₀) :
    Y.CentralZData := by
  by_cases hZ : Y.Zt 0 = ⊥
  · exact Y.centralZData H hZ
  · have h4 : 2 < n₀ := h3
    exact absurd (Y.n_eq_two_of_Zt_ne_bot H hZ) (ne_of_gt h4)

theorem st84MixedCentralZData_holds : St84MixedCentralZData := by
  intro V G _ _ Γ hΓ hc Y h3 h1
  have hne : Y.n 0 ≠ Y.n 1 := by rw [h1]; omega
  have hmix : ∀ v w : V, Γ.Adj v w → nOf Γ v ≠ nOf Γ w := Y.nOf_ne_of_adj hne
  obtain ⟨s, -, hs, -, hodd, h5⟩ := sec7_mixed hΓ hc hmix
  have hOdd : Odd (Nat.card Y.GT) := Y.odd_card_GT hc (Or.inl (by omega)) hs hodd h5
  exact Y.centralZData_of_three_le ⟨hc, by omega, rfl, h1, hs, hodd, h5, hOdd⟩ h3

end CFSG.Quasithin.St84

end
