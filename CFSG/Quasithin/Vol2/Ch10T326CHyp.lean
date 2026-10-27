module

public import CFSG.Quasithin.Vol2.Ch10SecA1010C
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

@[expose] def Ch10CaseIV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I ∨ Concl701Four T L I →
      ∀ _ : IsMulCommutative ↥(fsuVM T L I), ¬ Case3_2_6_iv T L I

@[expose] def Ch10CaseIVFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Concl701FF T L I ∨ Concl701Four T L I →
      ∀ _ : IsMulCommutative ↥(fsuVM T L I), ¬ Case3_2_6_iv T L I

theorem exists_hyp10C (hfsu : StmtFSUChoice) (h701 : Stmt7_0_1) (h1010 : Stmt10_1_0C)
    (hIV : Ch10CaseIV) {G : Type} [Group G] [Finite G] {T L : Subgroup G} (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hq : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T L)
    (hf : quasithinIsFaithfulLocal T L) (hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) : ∃ I : Subgroup G, Hyp10 G T L I := by
  obtain ⟨I, hI⟩ := hfsu G T L hs hn hq hT hmax hf hqs
  have hlt : L < fsuL0 T L := by
    refine lt_of_le_of_ne (le_conjClosure L T) fun h => hnot ?_
    have h' : L = conjClosure L T := h
    have hT0 : T ≤ Subgroup.normalizer (conjClosure L T : Set G) := le_normalizer_conjClosure L T
    rwa [← h'] at hT0
  obtain ⟨hc, -, -, h4⟩ := h701 G T L I hI
  have key : Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I →
      ∃ I' : Subgroup G, Hyp10 G T L I' := by
    intro h7
    rcases h1010 G T L I hI hlt hc h7 with ⟨x, hx, h3⟩ | ⟨hcVM, hiv⟩
    · exact ⟨CFSG.conjugate I x, ⟨fsu_conjugate hI hx, hnot, hlt, h3⟩⟩
    · exact absurd hiv (hIV G T L I hI hlt hc (h7.imp_right (Or.imp_right Or.inl)) hcVM)
  rcases h4 with h | h | h | h
  · exact key (Or.inl h)
  · exact key (Or.inr (Or.inl h))
  · exact key (Or.inr (Or.inr h))
  · rcases h.2.2 with ⟨x, hx, h3⟩ | ⟨hcVM, hiv⟩
    · exact ⟨CFSG.conjugate I x, ⟨fsu_conjugate hI hx, hnot, hlt, h3⟩⟩
    · exact absurd hiv (hIV G T L I hI hlt hc (Or.inr (Or.inr (Or.inr h))) hcVM)

theorem stmt10_0_1_of_stepsC (hfsu : StmtFSUChoice) (h701 : Stmt7_0_1) (h1010 : Stmt10_1_0C)
    (hIV : Ch10CaseIV) (h10213 : Stmt10_2_13) (hclose : StmtClose10) : Stmt10_0_1 := by
  intro G _ _ T L hs hn hq hT hmax hf hqs
  by_contra hnot
  obtain ⟨I, hI⟩ := exists_hyp10C hfsu h701 h1010 hIV hs hn hq hT hmax hf hqs hnot
  obtain ⟨K, hKmax, hKf, hKqs, hKnot, ⟨eA⟩⟩ := hclose G T L I hI
  obtain ⟨J, hJ⟩ := exists_hyp10C hfsu h701 h1010 hIV hs hn hq hT hKmax hKf hKqs hKnot
  obtain ⟨⟨⟨eL⟩, -⟩, -, -⟩ := h10213 G T K J hJ
  exact not_sl_three_two_equiv_alternating_five (eL.symm.trans eA)

end CFSG.Quasithin.Vol2.Ch10
