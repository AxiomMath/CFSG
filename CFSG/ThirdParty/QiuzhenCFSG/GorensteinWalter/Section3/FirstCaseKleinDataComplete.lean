module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData

namespace CFSG
end CFSG
open CFSG

/-!
# Complete structural data for the Klein-four branch
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem firstCase_klein_data_complete
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ d : FirstCaseKleinData c, ∃ K : Subgroup G,
      IsHallIn K c.FU ∧ K ≠ ⊥ ∧
        ∀ s : G, s ∈ c.Hhat → IsInvolution s →
          s ∉ twoCoreOf c.Hhat →
          (K : Set G) = invertedElements c.U s ∧
            ⁅c.Hhat, Subgroup.zpowers s⁆ ≤
              Subgroup.centralizer (c.FU : Set G) := by
  obtain ⟨r, hr, hrV⟩ :=
    firstCase_klein_exists_reflection_not_mem_twoCore hmin c hfirst hklein
  obtain ⟨K, _hKr, hKHall, hKne, hKall⟩ :=
    firstCase_klein_commutator_centralizes_fitting hmin c hfirst hklein
      r hr hrV
  let d : FirstCaseKleinData c :=
    { V := twoCoreOf c.Hhat
      V_eq := rfl
      V_klein := firstCase_klein_V_klein c hklein
      S_card := firstCase_klein_S_card hmin c hfirst hklein
      quotient_d6 := firstCase_klein_quotient_d6 hmin c hfirst hklein }
  refine ⟨d, K, hKHall, hKne, ?_⟩
  intro s hsH hsInv hsV
  obtain ⟨hKs, hcomm⟩ := hKall s hsH hsInv hsV
  exact ⟨by simpa [IsInvertedSubgroup] using hKs, hcomm⟩

end CFSG.GorensteinWalter
