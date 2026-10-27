module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.KGLangTorALinCont
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniCont
import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem kgLangAxisTorAInput_holds :
    KGLangAxisTorAInput := by
  intro p lab hp hp2 hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpd⟩ : (t = .A ∨ t = .twA) ∧ p ∣ l + 1 := hS
  have hd : 3 ≤ l + 1 := by
    have h1 := Nat.le_of_dvd (by omega) hpd
    have h2 := hp.two_le
    omega
  rcases htag with rfl | rfl
  · obtain ⟨hn, -⟩ : 1 ≤ n ∧ (1 ≤ l ∧ (l = 1 → 2 ≤ n)) := hlab
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    exact NbrGraphLinear.recipeLinear_all (d := l + 1) (N := 2 ^ n) (Q₀ := Q)
      (Q := KGLangAxisTorACont p ⟨.A, l, n⟩)
      (fun F _ _ hF => kgLangTorA_lin_cont hp hp2 (lab := ⟨.A, l, n⟩) rfl hd hn F hF) hQ
  · obtain ⟨hn, -, hl2n⟩ : 1 ≤ n ∧ 2 ≤ l ∧ (l = 2 → 2 ≤ n) := hlab
    have hq : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
      rintro ⟨h3, h2⟩
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl2n (by omega))
      omega
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    exact recipeUnitary_and (d := l + 1) (q := 2 ^ n) (Q := Q)
      (P := KGLangAxisTorACont p ⟨.twA, l, n⟩)
      (fun F _ _ hF => kgLangTorA_uni_cont hp hp2 (lab := ⟨.twA, l, n⟩) rfl hd hq hn F hF) hQ

end CFSG.StandardType
