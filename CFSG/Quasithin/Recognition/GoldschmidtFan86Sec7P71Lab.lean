module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ZLab

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem valence_line_two (F : FanTree Γ G) (T : Track Γ G) (i : ℤ) :
    Fan86.valence Γ (T.line.vert (i + 2)) = Fan86.valence Γ (T.line.vert i) := by
  rw [← T.trans i]
  exact F.valence_smul_eq T.τ _

theorem valence_line_pm_four (F : FanTree Γ G) (T : Track Γ G) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) :
    Fan86.valence Γ (T.line.vert (c - 4)) = 5 ∧ Fan86.valence Γ (T.line.vert (c + 4)) = 5 := by
  have e1 := valence_line_two F T c
  have e2 := valence_line_two F T (c + 2)
  have e3 := valence_line_two F T (c - 2)
  have e4 := valence_line_two F T (c - 4)
  rw [sub_add_cancel] at e3
  rw [show c - 4 + 2 = c - 2 by ring] at e4
  rw [show c + 2 + 2 = c + 4 by ring] at e2
  exact ⟨by rw [← e4, ← e3, h5], by rw [e2, e1, h5]⟩

theorem fixIdx_label (F : FanTree Γ G) (L : ZLab Γ G) (h40 : Fan40 F) (h62 : Fan62 F)
    (h63 : Fan63 F) (T : Track Γ G) (hT : InXi T) {c : ℤ}
    (h5 : Fan86.valence Γ (T.line.vert c) = 5) (i : ℤ) :
    i ∈ T.line.fixIdx (L.z (T.line.vert c)) ↔ c - 4 ≤ i ∧ i ≤ c + 4 := by
  have hc := L.isCentral (T.line.vert c) h5
  have hcinv : L.z (T.line.vert c) ∈ Cinv G (T.line.vert c) :=
    ⟨hc.2.1, hc.2.2.1, hc.1, hc.2.2.2⟩
  have hball := h63 h40 (T.line.vert c) (L.z (T.line.vert c)) hcinv 1
  rw [one_mul, inv_one, mul_one, one_smul] at hball
  have hfixd : ∀ j : ℤ, c - 4 ≤ j → j ≤ c + 4 →
      L.z (T.line.vert c) • T.line.vert j = T.line.vert j := by
    intro j h1 h2
    refine mem_ballStab.1 hball _ ?_
    rcases le_total c j with h | h
    · rw [Line.dist_eq F.isTree T.line h]
      omega
    · rw [SimpleGraph.dist_comm, Line.dist_eq F.isTree T.line h]
      omega
  have hmem : L.z (T.line.vert c) ∈ T.line.ZZ := by
    refine ⟨hc.2.2.1, c, ?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨hc.1, MulAction.mem_stabilizer_iff.2 ?_⟩
      exact hfixd (c + 1) (by omega) (by omega)
    · intro h hh
      exact hc.2.2.2 h (Subgroup.mem_inf.1 hh).1
  obtain ⟨⟨a, b, tL, tR, hfx⟩, hall⟩ := h62 h40 T hT _ hmem hc.2.1
  obtain ⟨h2, h3, h4⟩ := hall a b tL tR hfx
  have l1 : c - 4 ∈ T.line.fixIdx (L.z (T.line.vert c)) := hfixd _ le_rfl (by omega)
  have l2 : c + 4 ∈ T.line.fixIdx (L.z (T.line.vert c)) := hfixd _ (by omega) le_rfl
  rw [hfx.fix] at l1 l2 ⊢
  omega

end P71

end CFSG.Quasithin.Fan86
