module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBTv
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggInnerDiagOnLab_exc_of {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    {T : ℕ → LargeEvenLabel → Prop}
    (hTS : ∀ lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab)
    (h : GGInnerDiagOnLab T p Bs L) : GGInnerDiagOnLab GGRemTableBLExcLabel p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hTS lab hlab hθ.2.1 hθ.1, hθ.2⟩

theorem ggTableBCxInputOn_restrict_exc {T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBCxInputOn GGRemTableBLExcLabel)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab) :
    GGTableBCxInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_exc_of
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggTableBModuleInputOn_restrict_exc {T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBModuleInputOn GGRemTableBLExcLabel)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab) :
    GGTableBModuleInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_exc_of
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggTableBActionInputOn_restrict_exc {T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBActionInputOn GGRemTableBLExcLabel)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab) :
    GGTableBActionInputOn T := by
  intro G _ _ p B Bs x L D J B₂ hC hL hM
  exact hX G p B Bs x L D J B₂ hC (ggInnerDiagOnLab_exc_of
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL) hM

theorem ggLTransvectionCenterInputOn_restrict_exc {T : ℕ → LargeEvenLabel → Prop}
    (hX : GGLTransvectionCenterInputOn GGRemTableBLExcLabel)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab) :
    GGLTransvectionCenterInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_exc_of
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggLNoInvariantLineInputOn_restrict_exc {T : ℕ → LargeEvenLabel → Prop}
    (hX : GGLNoInvariantLineInputOn GGRemTableBLExcLabel)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab →
      GGRemTableBLExcLabel p lab) :
    GGLNoInvariantLineInputOn T := by
  intro G _ _ p B Bs x L D J hC hL E hEBs hxE hE
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_exc_of
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL) E hEBs hxE hE

theorem ggBstarInnerDiagLInputOn_resLID_false :
    GGBstarInnerDiagLInputOn GGRemTableBLExcResLID := by
  intro G _ _ p B Bs x L D J hC hL
  exfalso
  obtain ⟨-, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, θ, hST⟩ := largeEvenRawDatum_exists hraw
  exact ggRemTableBLExc_resLID_false hC.tableB_facts.1 hlab hST.2.1 hST.1

theorem ggRemTableBLExc2Label_of_exc (p : ℕ) (lab : LargeEvenLabel)
    (h : GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGRemTableBLExc2Label p lab := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h1 | ⟨ht, hp3, hd | hn1⟩ | ⟨ht, hn1, hp3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨ht, hp3, hd⟩)
  · exact (h2 (by unfold GGE6TwoThreeLabel; exact ⟨ht, hn1, hp3⟩)).elim
  · exact Or.inr (Or.inr ⟨ht, hn1, hp3⟩)

theorem ggTableBModuleInputOn_mono_exc {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBModuleInputOn S') :
    GGTableBModuleInputOn S :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC (hL.mono hSS')

theorem ggTableBActionInputOn_mono_exc {S S' : ℕ → LargeEvenLabel → Prop}
    (hSS' : ∀ p lab, S p lab → S' p lab) (h : GGTableBActionInputOn S') :
    GGTableBActionInputOn S :=
  fun G _ _ p B Bs x L D J B₂ hC hL hM => h G p B Bs x L D J B₂ hC (hL.mono hSS') hM

end CFSG.Yardstones.M3f9567aba59d
