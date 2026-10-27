module

public import CFSG.Quasithin.H13.VolIC129BorelMain
public import CFSG.Quasithin.Background.C129NativeLight

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem asc129Statement_of_join (hjoin : C129Native.JoinForm G)
    (hA7 : L238.C129A7StatementCat (G := G)) : ASC129Statement G := by
  intro H T M hsq hX hT hcgs hMH
  have hSQ : IsSQTKCat ↥H := ⟨isStronglyQuasithin_iff.mpr hsq.1, hsq.2⟩
  by_cases hT0 : T = ⊥
  ·
    have hO : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
    rw [hT0, le_bot_iff] at hO
    refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun h hh => ?_⟩
    have hmem : h ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨hh, ?_⟩
      rw [hO]
      exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [show g = 1 from by simpa using hg]
        simp
    have h2 := hX hmem
    rw [hO] at h2
    have h1 : h = 1 := by simpa using h2
    exact ⟨1, M.one_mem, Fin.elim0, fun i => i.elim0, by simp [h1]⟩
  · have hTM : T ≤ M := fun t ht =>
      hcgs (inf_normalizer_le_cgsIn hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩)
    rcases hjoin H T M hX hSQ hT hT0 hcgs hMH with hHM | ⟨s, L, -, hs2, hL, hcomp, hHL⟩
    · refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun h hh => ?_⟩
      have : h ∈ M := by rw [← hHM]; exact hh
      exact ⟨h, this, Fin.elim0, fun i => i.elim0, by simp⟩
    · refine ⟨s, L, hs2, fun i => ⟨(hL i).1, ?_, (hL i).2.1⟩, ?_⟩
      · exact isBorelOfBlock_of_isChi0Block hX hT hcgs hTM (hL i).1 (hL i).2.1 (hL i).2.2
      · exact C129Native.exists_set_product_of_join hA7 hX hSQ hT hcgs hMH hTM hs2 hL hcomp hHL

theorem asc129Statement_of_minParabolicBlocks
    (hMB : MinParabolicBlocks) (hB113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (G : Type) [Group G] [Finite G] : ASC129Statement G := by
  have h127 : L238.C127StatementCat (G := G) := L246C127.c127StatementCat_of_asB113 hB113
  have h123 : L238.C123TwoCgsStatement (G := G) := L246.C123.c123_holds G
  have hB42 : L238.AltBlockStatementJCat (G := G) := L238.altBlockStatementJCat_holds
  exact asc129Statement_of_join (C129Native.joinForm_of_minParabolicBlocks hMB hB113 G)
    (L246A7.c129A7_of_inputs hMB h127 h123 hB42 C129Native.a38ForSQTKCat_proved)

end CFSG.Quasithin.H13.VolI
