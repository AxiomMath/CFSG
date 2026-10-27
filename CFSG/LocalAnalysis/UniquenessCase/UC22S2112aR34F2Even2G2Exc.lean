module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Cases
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2ExcNoSwap
import CFSG.LocalAnalysis.UniquenessCase.UC22G2PrimeCent
import CFSG.LocalAnalysis.UniquenessCase.UC22G2FunCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot


theorem uc22s2112r34_g2_centralizer_commutator_eq {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h6 : 6 ≤ p ^ f)
    (hadm : StatedLieAdmissible .G2 n p f) (hX : LieModel X .G2 n p f) {K : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) {x : X} (hxK : x ∈ K) (hxr : (orderOf x).Prime)
    (hx5 : 5 ≤ orderOf x) (hxp : orderOf x ≠ p) :
    centralizer ((⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆ : Subgroup X) :
      Set X) = K := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h6
  obtain ⟨ψ, hψ⟩ := uc22s2112r34_g2_exists_mulEquiv_fund hp2 hadm hX hK
  have hxy : x = ψ (ψ.symm x) := (ψ.apply_symm_apply x).symm
  have hoy : orderOf (ψ.symm x) = orderOf x := by
    conv_rhs => rw [hxy]
    exact (MulEquiv.orderOf_eq ψ _).symm
  have hyr : ψ.symm x ^ orderOf x = 1 := by
    rw [← hoy]
    exact pow_orderOf_eq_one _
  have hy1 : ψ.symm x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hoy
    omega
  have hcard : 6 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    exact h6
  have hchar : orderOf x ≠ ringChar (GaloisField p f) := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hxp
  have hmem : ∀ A : Subgroup (adjointGroup .G2 (GaloisField p f)),
      x ∈ A.map ψ.toMonoidHom → ψ.symm x ∈ A := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hA
    simpa using ha
  rw [hxy, uc22s2112r34_centralizer_commutator_centralizer_map]
  rcases hψ with rfl | rfl
  · rw [uc22g2_centralizer_commutator_long hcard hxr hx5 hchar (hmem _ hxK) hyr hy1]
  · rw [uc22g2_centralizer_commutator_short hcard hxr hx5 hchar (hmem _ hxK) hyr hy1]

theorem uc22s2112r34_g2_fund_eq_of_mem {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h6 : 6 ≤ p ^ f)
    (hadm : StatedLieAdmissible .G2 n p f) (hX : LieModel X .G2 n p f) {K K' : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K') {x : X}
    (hx : x ∈ K ⊓ K') (hxr : (orderOf x).Prime) (hx5 : 5 ≤ orderOf x) (hxp : orderOf x ≠ p) :
    K = K' :=
  (uc22s2112r34_g2_centralizer_commutator_eq hp2 h6 hadm hX hK hx.1 hxr hx5 hxp).symm.trans
    (uc22s2112r34_g2_centralizer_commutator_eq hp2 h6 hadm hX hK' hx.2 hxr hx5 hxp)

theorem uc22ExcTwoFun_g2 : UC22ExcTwoFun .G2 := by
  intro X _ _ _ p hp hp7 hX
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h6 : 6 ≤ p ^ 1 := by
    rw [pow_one]
    omega
  have hadm := hX.admissible
  refine ⟨fun S K₁ K₂ h₁ h₂ hne hcomm => Or.inr ?_, fun K K' hK hK' x hx hxr hx5 hxp => ?_⟩
  · have h₁' : K₁ ∈ F14.FunSet (fundPred (p ^ 1)) X (S : Subgroup X) := by
      rwa [pow_one]
    have h₂' : K₂ ∈ F14.FunSet (fundPred (p ^ 1)) X (S : Subgroup X) := by
      rwa [pow_one]
    exact uc22s2112r34_g2_noSwapInput hp (by omega) hX S h₁ h₂ hcomm
      (g2_centralizer_funSet_le hp hp2 hadm hX h6 S h₁' h₂' hne)
      (g2_centralizer_funSet_le hp hp2 hadm hX h6 S h₂' h₁' hne.symm)
  · have hK₁ : IsFundamentalOver (p ^ 1) K := by
      rwa [pow_one]
    have hK₂ : IsFundamentalOver (p ^ 1) K' := by
      rwa [pow_one]
    exact uc22s2112r34_g2_fund_eq_of_mem hp2 h6 hadm hX hK₁ hK₂ hx hxr hx5 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22
