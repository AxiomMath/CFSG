module

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepTwA5RowDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndepTwA5RowInput_holds
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) :
    GGTwoNodeIndepTwA5RowInput := by
  intro G _ _ p B Bs x L D J y K hH hp X z hXz labJ labX hΛJ hΛX hlJ hlX hrow hzX hp3 htag
  exact (ggTwA5Three_frame hRig hLB hPJ hH hXz hp3 hΛX hlX htag).2.1 hzX

theorem ggTBXDatumResInput_of_rest
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (h : GGTBXDatumResInputRest) : GGTBXDatumResInput := by
  intro G _ _ p B Bs x L D J y K hH hp
  constructor
  · intro hM
    obtain ⟨hperf, lab, hlab, hraw⟩ := hM
    by_cases hc : lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1
    · obtain ⟨htw, hr5, hp3, hdvd⟩ := hc
      have hl : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
        largeEvenRawDatum_mono (fun R _ I F hQ => by
          obtain ⟨-, -, θ, -⟩ := hQ
          exact ⟨θ⟩) hraw
      exact (ggTwA5Three_frame hRig hLB hPJ hH (Or.inl ⟨rfl, rfl⟩) hp3 hlab hl
        ⟨htw, hr5, hdvd⟩).1
    · refine (h G p B Bs x L D J y K hH).1 ⟨hperf, lab, hlab, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, hθ⟩ := hQ
        exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw
  · intro hM
    obtain ⟨hperf, lab, hlab, hraw⟩ := hM
    by_cases hc : lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1
    · obtain ⟨htw, hr5, hp3, hdvd⟩ := hc
      have hl : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
        largeEvenRawDatum_mono (fun R _ I F hQ => by
          obtain ⟨-, -, θ, -⟩ := hQ
          exact ⟨θ⟩) hraw
      exact (ggTwA5Three_frame hRig hLB hPJ hH (Or.inr ⟨rfl, rfl⟩) hp3 hlab hl
        ⟨htw, hr5, hdvd⟩).1
    · refine (h G p B Bs x L D J y K hH).2 ⟨hperf, lab, hlab, ?_⟩
      exact largeEvenRawDatum_mono (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, hθ⟩ := hQ
        exact ⟨hs, hna, θ, ⟨⟨hθ.1, hc⟩, hθ.2⟩⟩) hraw

end CFSG.StandardType

end
