module

import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSFitting
import CFSG.Adapters.GeneralizedFitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8h_fstar_not_central {Γ : Type} [Group Γ] [Finite Γ] {B : Subgroup Γ} {d : Γ}
    (hne : B ≠ ⊤) (hprod : B ⊔ CFSG.pPrimeCore 3 Γ = ⊤) (hd : orderOf d = 3)
    (hcent : centralizer ({d} : Set Γ) ≤ B) :
    ¬ Fstar (CFSG.pPrimeCore 3 Γ) ≤ centralizer ({d} : Set Γ) := by
  intro hFst
  set I : Subgroup Γ := CFSG.pPrimeCore 3 Γ with hI
  haveI hIn : I.Normal := by rw [hI]; exact CFSG.pPrimeCore_normal
  have h3 : ¬ 3 ∣ Nat.card ↥I := by
    rw [hI]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hdn : d ∈ Subgroup.normalizer (I : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hIn]
    exact Subgroup.mem_top d
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  set β : MulAut ↥I := CFSG.LocalAnalysis.RankThreeTheoremC.FPFS.conjAut I d hdn with hβdef
  have hβF : ∀ f ∈ genFittingFStar ↥I, β f = f := by
    intro f hf
    have hfF : (f : Γ) ∈ Fstar I := ⟨f, hf, rfl⟩
    have hcomm : (f : Γ) * d = d * (f : Γ) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hFst hfF)
    apply Subtype.ext
    rw [hβdef, CFSG.LocalAnalysis.RankThreeTheoremC.FPFS.coe_conjAut]
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  haveI hFnormal : (genFittingFStar ↥I).Normal := by
    rw [CFSG.Adapters.genFittingFStar_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal ↥I
  have hC : Subgroup.centralizer (genFittingFStar ↥I : Set ↥I) ≤ genFittingFStar ↥I :=
    CFSG.Adapters.generalized_fitting_self_centralizing ↥I
  have hβp : β ^ 3 = 1 := by
    rw [hβdef]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.FPFS.conjAut_pow_eq_one I d hdn hd3
  have hβ1 : β = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.FPFS.aut_eq_one_of_fixes_selfCentralizing
      (genFittingFStar ↥I) hC β hβF hβp h3
  have hIle : I ≤ centralizer ({d} : Set Γ) := by
    intro g hg
    have hfix : β ⟨g, hg⟩ = ⟨g, hg⟩ := by rw [hβ1]; rfl
    have hval : d * g * d⁻¹ = g := by
      have h1 := congrArg (fun x : ↥I => (x : Γ)) hfix
      rw [hβdef, CFSG.LocalAnalysis.RankThreeTheoremC.FPFS.coe_conjAut] at h1
      simpa using h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mul_inv_eq_iff_eq_mul).1 hval).symm
  have hIB : I ≤ B := le_trans hIle hcent
  have hBtop : B = ⊤ := (sup_eq_left.2 hIB).symm.trans hprod
  exact hne hBtop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
