module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt

theorem ggRootSylowCentral_spinMinus {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) :
    GGRootSylowCentral (minusDatum n hirr) .POmegaMinus := by
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := n) hirr)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ggRootSylowCentral_of_longRoot_reduced (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr) (SpinMinusClosed.bruhatExtras hirr hn) rfl
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ) (SpinMinusClosed.coprime_card_torus hirr)
    (fun γ₀ hγ₀ _ x hx y hy => ?_) fun γ hγ => hγ.longRoot_of_twisted (Or.inr (Or.inl rfl))
  obtain ⟨s, rfl⟩ := SpinMinusClosed.exists_x_eq_of_mem hirr hγ₀ hx
  obtain ⟨u, rfl⟩ := SpinMinusClosed.exists_x_eq_of_mem hirr hγ₀ hy
  exact (SpinMinusClosed.x_add hirr γ₀ s u).symm.trans
    ((congrArg (SpinMinusClosed.x hirr γ₀) (add_comm s u)).trans
      (SpinMinusClosed.x_add hirr γ₀ u s))

end CFSG.StandardType
