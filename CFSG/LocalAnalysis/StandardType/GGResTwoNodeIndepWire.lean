module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndep
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmall
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeNineDep
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLE3E6
public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJTwoNodeInput_of_small_large_e6 (hS : GGTBJTwoNodeSmallInput)
    (hL : GGTBJTwoNodeLargeInput) (hE : GGE6D4TwoNodeLocalInput) : GGTBJTwoNodeInput := by
  have key : ∀ {p : ℕ} {labJ labX : LargeEvenLabel}, ggRowTwoNode p labJ labX →
      (10 ≤ labX.rank ∧ ggRowTwoNode p labJ labX) ∨ ggRowTwoNodeSmallJA p labJ labX ∨
        (p = 3 ∧ (labX.tag = .E6 ∨ labX.tag = .twE6)) := by
    intro p labJ labX hr
    rcases hr with ⟨ht, hp1, hp2, hX⟩ | ⟨ht, hp1, hp2, hX⟩ | ⟨hJ, hp3, -, hX⟩ | ⟨hJ, hp3, -, hX⟩
    · rcases le_or_gt 10 labX.rank with h | h
      · exact Or.inl ⟨h, Or.inl ⟨ht, hp1, hp2, hX⟩⟩
      · exact Or.inr (Or.inl ⟨⟨Or.inl ⟨ht, hp1, hp2, hX⟩, by omega⟩, Or.inl ht⟩)
    · rcases le_or_gt 10 labX.rank with h | h
      · exact Or.inl ⟨h, Or.inr (Or.inl ⟨ht, hp1, hp2, hX⟩)⟩
      · exact Or.inr (Or.inl ⟨⟨Or.inr (Or.inl ⟨ht, hp1, hp2, hX⟩), by omega⟩, Or.inr ht⟩)
    · exact Or.inr (Or.inr ⟨hp3, Or.inl (by rw [hX])⟩)
    · exact Or.inr (Or.inr ⟨hp3, Or.inr (by rw [hX])⟩)
  intro G _ _ p B Bs x L D J y K hH hp
  refine ⟨fun hX hrow => ?_, fun hX hrow => ?_⟩
  · obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    rcases key hr with ⟨h10, hr'⟩ | hs | ⟨hp3, htag⟩
    · exact (hL G p B Bs x L D J y K hH).1 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr', h10⟩⟩
    · exact (hS G p B Bs x L D J y K hH).1 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hs⟩
    · subst hp3
      exact (hE G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hr
        htag).2.2.2.2.2
  · obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := hrow
    rcases key hr with ⟨h10, hr'⟩ | hs | ⟨hp3, htag⟩
    · exact (hL G p B Bs x L D J y K hH).2 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr', h10⟩⟩
    · exact (hS G p B Bs x L D J y K hH).2 hX ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hs⟩
    · subst hp3
      exact (hE G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hr
        htag).2.2.2.2.2

theorem ggResTwoNodeIndepInput_of_inputs (hKG : GGReflClassLargeInput')
    (hOrb : GGResCentBoundInput) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hKFix : GGTwoNodeKFixLineInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hD : GGTwoNodeIndepDatum) (hJ : GGTBJInputR) (hJ2 : GGTBJTwoNodeInput)
    (hPosB : LR6SmallRankPosB) (hExcl : LR6SmallRankExcl) (hNine : LR6NineDepPos)
    (hTwo : GGResTwoNodeIndepSmallTwoInput) (hTwoNine : GGResTwoNodeNineDepTwoInput)
    (hE6 : GGResTwoNodeIndepLE3E6Input)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) : GGResTwoNodeIndepInput :=
  have hLE3 : GGResTwoNodeIndepLE3RestInput :=
    ggResTwoNodeIndepLE3Rest_of_E6 hE6 hTwo hTwoNine hFix hKFix hD hJ2
  ggResTwoNodeIndepInput_of_parts
    (ggResTwoNodeIndepLargeInput_of_inputs hKG hOrb hOrbK hFix hFixK hKFix hJr hPump hLB hSP hD hJ
      hJ2
      (ggResTwoNodeNineDepInput_of_inputs hNine hTwoNine hLE3 hOrb hOrbK hFix hFixK hD hJ hJ2 hX
        h6c h6d h6e h6f h6g)
      hX h6c h6d h6e h6f h6g)
    (ggResTwoNodeIndepSmallInput_of_inputs
      (ggResTwoNodeIndepSmallRest_of_two hTwo hLE3 hJ hJ2 hX h6c h6d h6e h6f h6g)
      hPosB hExcl hOrb hOrbK hFix hFixK hKFix hJr hPump hLB hSP hD hJ2)

end CFSG.StandardType

end
