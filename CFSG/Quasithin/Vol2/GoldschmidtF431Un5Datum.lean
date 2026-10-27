module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LocWire
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieBrA
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieMapA

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin.H13.F431.Lift CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Quasithin.H13.Sec53F.Unit

theorem un5StdDatum_of
    (hS1 : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2),
      StdTwo (hypPSU (un5FD hF) 2 1) (hypProjUnitriangular (un5FD hF) 2 1) (u5PtP (un5FD hF))
        (u5LnP (un5FD hF)) (z5Y (un5FD hF)) (t5Y (un5FD hF)))
    (hSV : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2),
      UnStdV (hypPSU (un5FD hF) 2 1) (hypProjUnitriangular (un5FD hF) 2 1) (u5PtP (un5FD hF))
        (u5LnP (un5FD hF)) (z5Y (un5FD hF)) (t5Y (un5FD hF)) (v5Y (un5FD hF)))
    (hSL : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)
      (ζ : traceZero (unitaryInvolution F 2 2)) [Fact ((ζ : F) ≠ 0)],
      ∃ V Uc R K : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
          Subgroup.center (SU (unitaryInvolution F 2 2) 5)),
        UnStdLoc _ (un5System hF ζ).U (un5Eps hF ζ (z5Y (un5FD hF)))
          (un5Eps hF ζ (t5Y (un5FD hF))) V Uc R K) : Un5StdDatum := by
  intro F _ _ _ hF ζ _
  obtain ⟨V, Uc, R, K, hL⟩ := hSL F hF ζ
  have S1 := stdTwo_map (un5Eps hF ζ) (hS1 F hF)
  have SV := unStdV_map (un5Eps hF ζ) (hSV F hF)
  rw [un5Eps_map_U] at S1 SV
  exact ⟨_, _, _, _, _, V, Uc, R, K, un5Eps_map_P hF ζ, S1, SV, hL⟩

end CFSG.Quasithin.H13.F431.Un
