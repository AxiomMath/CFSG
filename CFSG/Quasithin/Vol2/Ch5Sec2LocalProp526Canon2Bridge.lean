module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Orient
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon2Snd
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon2U4ext
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalCanon2Common

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Lists

variable {G : Type} [Group G]

theorem F112ListA.toLegacyBare_of_le {L1 L2 S : Subgroup G} (h : F112ListA L1 L2 S)
    (hS1 : S ≤ L1) (hS2 : S ≤ L2)
    (hc1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1)
    (hc2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2) : F112ListALegacyBare L1 L2 S := by
  have hL1 : L1 ⊔ S = L1 := sup_eq_left.mpr hS1
  have hL2 : L2 ⊔ S = L2 := sup_eq_left.mpr hS2
  simp only [F112ListA] at h
  simp only [F112ListALegacyBare]
  rcases h with h1 | h2 | ⟨f, hf, hA, hq1, hq2, hsp, hc⟩ | ⟨f, hf, hA, hq1, hsp, hq2, hc⟩ |
    ⟨a, ha, hA, he, hc1', hq2, hc2'⟩ | ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ |
    ⟨hA, hSU, hsp, hq2, hc⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr (Or.inl ⟨f, hf, hA, hq1, hq2, ?_, ?_⟩))
    · rw [hL1, ← hc1]
      exact hsp
    · rw [hL2, ← hc2]
      exact hc
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hA, hq1, ?_, hq2, ?_⟩)))
    · rw [← hc1]
      exact hsp
    · rw [← hc2]
      exact hc
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, hA, he, ?_, hq2, ?_⟩))))
    · rw [← hc1]
      exact hc1'
    · rw [← hc2]
      exact hc2'
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hA, hq1, ?_, hb2, hq2, hO⟩)))))
    rw [← hc1]
    exact hsp
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hA, hSU, ?_, hq2, ?_⟩)))))
    · rw [← hc1]
      exact hsp
    · rw [← hc2]
      exact hc

end Lists

section Orientation

variable {G : Type} [Group G] [Finite G]

theorem centerOf_le_centralizer_of_E6ExtC (hRL : RankOneListedFacts.{0}) {L1 L2 S : Subgroup G}
    (h111 : Hyp111 L1 L2 S) (hE : F112E6ExtC L1 L2 S) :
    centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
  obtain ⟨f, hf, -, hq1, hsp, -, -, -⟩ := hE
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 hRL h111
  have hOQ : pCoreOf 2 L1 ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := F1.pCoreOf_le_pCoreOf_parabolic hR
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  have hLQ : L1 ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  refine centerOf_le_centralizer_of_hyp111 hR hQS hOQ hLQ ?_
  refine le_centralizer_of_isL2Quot (n := f) (f := f) hf (by omega) hq1
    (by rw [card_centerOf_eq, hsp.2.2])
    (hLQ.trans (A4.normalizer_le_normalizer_centerOf _)) fun o ho => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 o (hOQ ho)).symm

end Orientation

namespace Hyp5_2_4

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem bridge (hRL : RankOneListedFacts.{0}) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4)
    (hsecC : Stmt5_2_6_secondC) (hU4C : Stmt5_2_6_U4extC)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hnotL : ¬ centerOf (sec52S M H) ≤ Subgroup.centralizer (L : Set G))
    {L1' L2' : Subgroup G} (hor12 : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L))
    (hlistC : F112ListA L1' L2' (sec52S M H)) (hsecond : F112Second L1' L2' (sec52S M H)) :
    F112ListALegacyBare L1' L2' (sec52S M H) ∧
      ((perfectCore L1' = L1' ∧ perfectCore L2' = L2' ∧ sec52S M H ≤ L1' ∧
          sec52S M H ≤ L2') ∨ F112E6Ext L1' L2' (sec52S M H)) := by
  obtain ⟨h111', hq', hSn', hns1, hns2⟩ := hyp.f112_hyps hF11 hbor h524 hor12
  have hRs : Hyp111R L1' L2' (sec52S M H) := Hyp111R.of_hyp111 hRL h111'
  rcases hsecC G L1' L2' (sec52S M H) h111' hq' hSn' hns1 hns2 hlistC hsecond with
    ⟨hp1, hp2, hS1, hS2⟩ | hext
  · exact ⟨hlistC.toLegacyBare_of_le hS1 hS2 (pCoreOf_parabolic_eq_of_le hRs hS1)
      (pCoreOf_parabolic'_eq_of_le hRs hS2), Or.inl ⟨hp1, hp2, hS1, hS2⟩⟩
  ·
    have hc := centerOf_le_centralizer_of_E6ExtC hRL h111' hext
    obtain ⟨h1, h2⟩ : L1' = L₂ ∧ L2' = L := by
      rcases hor12 with ⟨h1, -⟩ | h12
      · rw [h1] at hc
        exact absurd hc hnotL
      · exact h12
    subst L1' L2'
    obtain ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ := hext
    have hAα := hyp.isU4ExtTwo_of_orient h331 hR hbor (Or.inr ⟨rfl, rfl⟩) hA
    have hspV : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (sec52G2 M H D L₂)) := by
      obtain ⟨-, hG2, -⟩ := hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)
      rw [hG2, ← bigB_swap L L₂ (sec52S M H)]
      exact hsp
    obtain ⟨-, hO2, -⟩ := hU4C G T M L V H B D L₂ n f hyp hf hAα hq1 hspV hb2 hq2 hO
    have hext' : F112E6Ext L₂ L (sec52S M H) :=
      ⟨f, hf, hA, hq1, by rw [← hO2]; exact hspV, hb2, hq2, hO⟩
    refine ⟨?_, Or.inr hext'⟩
    unfold F112ListALegacyBare
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hext'.e6)))))

end Hyp5_2_4

end CFSG.Quasithin.H13
