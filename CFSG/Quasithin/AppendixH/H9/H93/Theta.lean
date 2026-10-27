module

public import CFSG.Quasithin.AppendixH.H9.H93.Theta.OuterInvolution

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem thetaIso_of_outer_involution (n : ℕ) (t : MulAut (PairN n)) (ht : t ∈ Mg n)
    (htL : t ∉ Lg n) (ht2 : orderOf t = 2) : ThetaIso n t := by
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin n) (ZMod 2), t = pairActN n A * swapN n :=
    (mem_Mg_iff.mp ht).resolve_left htL
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  exact thetaIso_of_outer_form A hA htt

end CFSG.ASVolI.ChH
