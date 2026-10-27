module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3EvenCentPerfectSU
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

theorem u3EvenCentPerfect : U3EvenCentPerfect := by
  intro X _ _ n r hX hr hr3 A P hA hP hrP hAP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.statedClassicalModel_of_lieModel_PSU3 hX
  have hn : 2 ≤ n := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX
  have h : UnitaryFieldData 2 n K := unitaryFieldDataOfCard hK
  have : Finite (unitarySU 2 n K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  let ψ := unitaryPSUEquiv h (n := 3) (by norm_num)
  let φ : unitarySU 2 n K 3 →* X :=
    e.symm.toMonoidHom.comp (ψ.toMonoidHom.comp (unitaryProj h 3))
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨g, hg⟩ := unitaryProj_surjective h 3 (ψ.symm (e x))
    exact ⟨g, by simp [φ, hg]⟩
  have hkerφ : φ.ker = (unitaryProj h 3).ker := by
    ext g
    simp [φ, MonoidHom.mem_ker]
  have hker : φ.ker ≤ Subgroup.center _ := by
    rw [hkerφ, ker_unitaryProj]
    exact unitaryScalars_le_center h 3
  have hrker : ¬ r ∣ Nat.card φ.ker := by
    rw [hkerφ, ker_unitaryProj, card_unitaryScalars h (n := 3) (by norm_num)]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1)))
    omega
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_centralizer_of_central_cover φ hφ hker hr
    hrker (fun a Q har hQ hrQ haQ =>
      mem_centralizer_of_isPerfect_unitarySU3 h hn hr (by omega) har hQ hrQ haQ)
    hA hP hrP hAP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
