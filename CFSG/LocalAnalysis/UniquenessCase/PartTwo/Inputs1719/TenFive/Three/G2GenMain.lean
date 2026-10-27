module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.G2GenCheck
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.G2GenInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.G2GenOuter
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import Certificates.Certificate1208102
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.CGT.PushingUpLit.CGT6.EmbG23

theorem involGenG2_of_native
    (hin : ∀ t : G23, t * t = 1 → t ≠ 1 → IsGenGood (MulAut.conj t))
    (hout : IsGenGood phi) : InvolGenG2 := by
  intro S _ _ hm
  obtain ⟨e⟩ := exists_equiv_g23 (hm.chevalleyExceptionalModel (by decide))
  refine InvolGen.of_mulEquiv e.symm ?_
  intro σ hσ
  have hσ2 : σ * σ = 1 := by
    rw [← pow_two, ← hσ]
    exact pow_orderOf_eq_one σ
  have hσne : σ ≠ 1 := by
    rintro rfl
    simp at hσ
  by_cases hσin : σ ∈ (MulAut.conj : G23 →* MulAut G23).range
  · obtain ⟨t, ht⟩ := hσin
    have htne : t ≠ 1 := by
      rintro rfl
      apply hσne
      rw [← ht]
      ext x
      simp [MulAut.conj_apply]
    have hconj : MulAut.conj (t * t) = 1 := by
      rw [map_mul, ht, hσ2]
    have hcenter : t * t ∈ Subgroup.center G23 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun f : MulAut G23 => f y) hconj
      simp only [MulAut.one_apply, MulAut.conj_apply] at hy
      calc y * (t * t) = ((t * t) * y * (t * t)⁻¹) * (t * t) := by rw [hy]
        _ = (t * t) * y := by group
    have hbot : Subgroup.center G23 = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    rw [hbot, Subgroup.mem_bot] at hcenter
    simpa [ht] using hin t hcenter htne
  · obtain ⟨⟨ψ, hψ⟩, -⟩ := exists_conj_phi σ hσ2 hσin
    have hσeq : σ = ψ⁻¹ * phi * ψ := by
      calc σ = ψ⁻¹ * (ψ * σ * ψ⁻¹) * ψ := by group
        _ = ψ⁻¹ * phi * ψ := by rw [hψ]
    have hσeq' : σ = ψ⁻¹ * phi * (ψ⁻¹)⁻¹ := by simpa using hσeq
    exact IsGenGood.conj hσeq' hout

theorem involGenG2_holds : InvolGenG2 :=
  involGenG2_of_native (g23_inner_genGood_of_check g2GenCheck_eq_true)
    (g23_phi_genGood_of_check g2GenCheck_eq_true)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
