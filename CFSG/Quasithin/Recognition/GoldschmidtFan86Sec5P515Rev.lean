module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem inXi_rev (hXi1 : ∀ T' : Track Γ G, ¬ Xi 1 T') {T : Track Γ G} (hXi : InXi T) :
    InXi T.rev := by
  obtain ⟨i, hi, hmin⟩ := hXi
  have hi1 : i ≠ 1 := fun h => hXi1 T (h ▸ hi)
  rcases i with _ | _ | _ | _ | n
  · exact hi.elim
  · exact absurd rfl hi1
  · refine ⟨2, ?_, hmin⟩
    show T.rev.HasReflections
    intro k
    obtain ⟨f, hf2, hf⟩ := hi (-k)
    refine ⟨f, hf2, fun i => ?_⟩
    show f • T.line.vert (-(k + i)) = T.line.vert (-(k - i))
    rw [show -(k + i) = -k + -i by ring, show -(k - i) = -k - -i by ring]
    exact hf (-i)
  · refine ⟨3, ?_, hmin⟩
    show HasLenTwoReflection Γ G T.rev
    obtain ⟨k, f, hff, h0, h1, h2⟩ := (hi : HasLenTwoReflection Γ G T)
    have back : ∀ u v : V, f • u = v → f • v = u := fun u v h => by
      rw [← h, smul_smul, hff, one_smul]
    refine ⟨-k, f, hff, ?_, ?_, ?_⟩
    · show f • T.line.vert (-(-k)) = T.line.vert (-(-k))
      rw [neg_neg]
      exact h0
    · show f • T.line.vert (-(-k + 1)) = T.line.vert (-(-k - 1))
      rw [show -(-k + 1) = k - 1 by ring, show -(-k - 1) = k + 1 by ring]
      exact back _ _ h1
    · show f • T.line.vert (-(-k + 2)) = T.line.vert (-(-k - 2))
      rw [show -(-k + 2) = k - 2 by ring, show -(-k - 2) = k + 2 by ring]
      exact back _ _ h2
  · exact hi.elim

theorem lab_rev (T : Track Γ G) (z : G) (m : ℤ) : lab T.rev z m = lab T z (-m) := by
  simp [lab, Track.rev, zpow_neg]

theorem half (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h40 : Fan40 F) (T : Track Γ G) (z : G)
    (a tL tR : ℤ) (hXi : InXi T) (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1)
    (hc : T.line.IsCoreFix z a (a + 2) tL tR) (hval : valence Γ (T.line.vert (a + 1)) ≠ 3)
    (hr : 5 ≤ tR - (a + 2)) (k j : ℤ) (hj : 0 ≤ j) (hjr : 2 * j + 3 ≤ tR - (a + 2)) :
    lab T z (k + j) ∈ ballStab Γ G 2 (T.line.vert (a + 1 + 2 * k)) := by
  have hc' := isCoreFix_lab T k hc
  rw [show a + 2 + 2 * k = a + 2 * k + 2 by ring] at hc'
  have hval' : valence Γ (T.line.vert (a + 2 * k + 1)) ≠ 3 := by
    rw [show a + 2 * k + 1 = a + 1 + 2 * k by ring, valence_vert_add_two_mul F T.line (a + 1) k]
    exact hval
  obtain ⟨-, -, C⟩ := mkCtx F h513b h510 h511 h512cen h512b h40 T (lab T z k) (a + 2 * k)
    (tL + 2 * k) (tR + 2 * k) hXi (lab_mem_ZZ T hz k) (lab_ne_one T hz1 k) hc' hval'
    (by omega)
  have := core F h40 C (r := tR + 2 * k - (a + 2 * k + 2)) (by omega) hj (by omega)
  rw [lab_lab, show a + 2 * k + 1 = a + 1 + 2 * k by ring] at this
  exact this

theorem fan515a_of (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) : Fan515a F := by
  intro h40 T z a tL tR hXi hz hz1 hc hval hr k j hj hjr
  refine ⟨half F h513b h510 h511 h512cen h512b h40 T z a tL tR hXi hz hz1 hc hval hr k j hj hjr,
    ?_⟩
  obtain ⟨hXi1, htL, -⟩ := mkCtx F h513b h510 h511 h512cen h512b h40 T z a tL tR hXi hz hz1 hc
    hval hr
  have hc' : T.rev.line.IsCoreFix z (-(a + 2)) (-(a + 2) + 2) (-tR) (-tL) := by
    have := hc.rev
    rw [show -(a + 2) + 2 = -a by ring]
    exact this
  have hval' : valence Γ (T.rev.line.vert (-(a + 2) + 1)) ≠ 3 := by
    show valence Γ (T.line.vert (-(-(a + 2) + 1))) ≠ 3
    rw [show -(-(a + 2) + 1) = a + 1 by ring]
    exact hval
  have := half F h513b h510 h511 h512cen h512b h40 T.rev z (-(a + 2)) (-tR) (-tL)
    (inXi_rev hXi1 hXi) (Line.ZZ_rev hz) hz1 hc' hval' (by omega) (-k) j hj (by omega)
  rw [lab_rev, show -(-k + j) = k - j by ring] at this
  have e : T.rev.line.vert (-(a + 2) + 1 + 2 * -k) = T.line.vert (a + 1 + 2 * k) := by
    show T.line.vert (-(-(a + 2) + 1 + 2 * -k)) = _
    congr 1
    ring
  rw [e] at this
  exact this

end P515

theorem fan_5_15a {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) : Fan515a F :=
  P515.fan515a_of F h513b h510 h511 h512cen h512b

end CFSG.Quasithin.Fan86
