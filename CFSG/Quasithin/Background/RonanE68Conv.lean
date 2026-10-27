module

public import CFSG.Quasithin.Background.RonanE68Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.Quasithin.Background.ONanE68Setting

public section

namespace CFSG.Quasithin

namespace RonanE68

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof
  CFSG.QuasithinUnique.Vol2Native.L239

section Scope

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem hypOrMax_of_equalityScope (hU : U ∈ E6.gammaE64 V M) (hs : EqualityScope M V U) :
    E6.E68HypOrMax M V U := by
  rcases hs with h1 | hmax
  · exact Or.inl h1
  · refine Or.inr fun W hUW hWV => ?_
    by_contra hCW
    have hWΓ : W ∈ E6.gammaE64 V M := by
      refine ⟨hWV, ?_, hCW, ?_⟩
      · intro h0
        apply hU.2.1
        rw [h0] at hUW
        exact le_bot_iff.1 hUW.le
      · exact (twoPrimeResidual_mono (inf_le_inf_left M (Subgroup.centralizer_le hUW.le))).trans
          hU.2.2.2
    exact hUW.ne (hmax W hWΓ hUW.le).symm

theorem case3P_of_case3 (hU : U ∈ E6.gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (h3 : E6.E68Case3 T M V U L) : Case3P T M V U L := by
  obtain ⟨hm, hq, hsc, h1, h2⟩ := h3
  exact ⟨hm, hq, le_inf_centralizer_component hU.1 hL,
    fun hs => hsc (hypOrMax_of_equalityScope hU hs), h1, h2⟩

theorem case5P_of_case5 (hU : U ∈ E6.gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (h5 : E6.E68Case5 M V U L) : Case5P M V U L := by
  obtain ⟨hm, hsc, h1, h2⟩ := h5
  exact ⟨hm, le_inf_centralizer_component hU.1 hL,
    fun hs => hsc (hypOrMax_of_equalityScope hU hs), h1, h2⟩

end Scope

section Case1

variable {G : Type} [Group G] {T M V U L : Subgroup G}

theorem case1P_of_case1 {hV : CFSG.Open.IsElemAbelian 2 V} (hZ : Subgroup.center ↥L = ⊥)
    (h1 : E6.E68Case1 hV T M U L) : Case1P hV T M U L := by
  obtain ⟨n, hmodel, -, hBor, hcyc, hcard, hm, hle, hdec⟩ := h1
  have e : ↥L ≃* (↥L ⧸ Subgroup.center ↥L) := mulEquivQuotientCenter hZ
  refine ⟨n, ?_, hBor, hcyc, hcard, hm, hle, hdec⟩
  rcases hmodel with ⟨h2, hm2⟩ | ⟨ho, h3, hm2⟩ | ⟨h1', hm2⟩ | ⟨h2, hm2⟩
  · exact Or.inl ⟨h2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm2⟩
  · exact Or.inr (Or.inl ⟨ho, h3, CFSG.SectionRank.suzukiModel_of_mulEquiv e hm2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1', CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hm2⟩)))

end Case1

end RonanE68

end CFSG.Quasithin
