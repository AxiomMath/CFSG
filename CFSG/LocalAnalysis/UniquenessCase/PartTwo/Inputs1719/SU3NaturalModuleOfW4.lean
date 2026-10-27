module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3Modules
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_SU3NaturalModuleAltTwo : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y K : Subgroup (MulAut W)) (n : ℕ),
      K ≤ Y → CFSG.Open.IsComponentOf K Y → K ≠ ⊥ → IsSU3 ↥K n → 3 ≤ n →
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      fixV (⨆ X ∈ conjSet K Y, X) = ⊥ →
      E3.mParam Y ≤ 2 * n + 2 →
      ∀ Z : Subgroup W, Z = ⊥ →
        IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X Z)) →
        ∀ I : Subgroup W, I ∈ irrSet K →
          (E3.mParam (autSub (autQuot Y Z) (I.map (QuotientGroup.mk' Z))) : ℚ) *
            ((rk ↥(commV (autQuot K Z)) : ℚ) /
              (rk ↥(I.map (QuotientGroup.mk' Z)) : ℚ)) ≤ E3.mParam Y →
          S17.CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K n ∧
            E3.mParam Y = 2 * n

theorem k_SU3NaturalModule_of_w4 (h128 : W4Lem12_8) (h36 : W4Lem3_6)
    (hMin : K_SU3MinDegree) (hAlt : K_SU3NaturalModuleAltTwo) : K_SU3NaturalModule := by
  intro W _ _ hWsq Y K n hKY hKcomp hKne hSU hn3 hO2 hbasic hfix hmY
  let H : Subgroup (MulAut W) := ⨆ X ∈ conjSet K Y, X
  have h128' := h128 W hWsq Y hO2 hbasic K hKcomp H rfl
  rcases h128' with h1 | h2 | h3
  · have hd : 6 * n ≤ dMinDeg ↥K := hMin ↥K n hSU (by omega)
    omega
  · obtain ⟨hsum, I, hI, hratio⟩ := h2
    exact hAlt W hWsq Y K n hKY hKcomp hKne hSU hn3 hO2 hbasic hfix hmY
      (fixV H) hfix hsum I hI hratio
  · obtain ⟨R, e, -, -, -, -, hmE, hde⟩ := h3
    have hd : 6 * n ≤ dMinDeg ↥K := hMin ↥K n hSU (by omega)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
