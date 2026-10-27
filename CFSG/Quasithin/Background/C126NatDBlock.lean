module

public import CFSG.Quasithin.Background.C126NatDComm

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2

variable {G : Type} [Group G] [Finite G]

theorem oneBlock_of_block {H T M V P : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hNat : NatCase H T V hV)
    (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T) (hPM : ¬ P ≤ M) (hPT : P ⊔ T = H)
    (hMinP : MinParabolic P (baum T) (P ⊓ M)) (hBlk : IsL2OrA3Block P (twoResidual P)) :
    OneBlock H T := by
  obtain ⟨I, c⟩ := exists_natCtx hmin hF hred hJ hNat
  have hTH : T ≤ H := hmin.isSylow.1
  have hSH : baum T ≤ H := inf_le_left.trans hTH
  have hPH : P ≤ H := hPK.trans (sup_le (twoResidual_le H) hSH)
  obtain ⟨L, hL, hLP⟩ := c.exists_factor_le_rho hPH hSP hPK hPM hMinP
  have hρ := c.rho_twoResidual_eq (hPH.trans c.hHN) hL (c.rho_eq hPH hSP hMinP hL hLP)
  have hKH : twoResidual P ≤ H := (twoResidual_le P).trans hPH
  have hK1 : twoResidual P ≤ conjClosure (twoResidual P) T := fun z hz => by
    simpa using mem_conjClosure T.one_mem hz
  refine ⟨twoResidual P, ⟨⟨hBlk.1.1, hKH, c.isSubnormal_K1 hRF hSP hPK hL hρ hBlk.1.1.1⟩,
    hBlk.2.elim Or.inl fun h => Or.inr (Or.inl h)⟩, c.commutator_K1_eq hRF hSP hPK hL hρ,
    le_antisymm ?_ (sup_le hTH (conjClosure_le fun h hh z hz => ?_))⟩
  · have hP : baum T ⊔ twoResidual P = P := sup_twoResidual_eq hMinP.isSylow
    calc H = P ⊔ T := hPT.symm
      _ ≤ T ⊔ conjClosure (twoResidual P) T := sup_le (hP.symm.le.trans (sup_le
          (inf_le_left.trans le_sup_left) (hK1.trans le_sup_right))) le_sup_left
  · exact H.mul_mem (H.mul_mem (hTH hh) (hKH hz)) (H.inv_mem (hTH hh))

end CFSG.Quasithin.C126.Nat
