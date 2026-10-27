module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6EndNode

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

theorem coverProducerOn_of_rationalProducerOn
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (tag : LargeEvenLieTag) (h : RationalProducerOn Omega tag) :
    CoverProducerOn Omega tag := by
  intro p lab hlab hpair htag Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hpair htag Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L _ _ psi hpsi hker hcomm e he hind
  obtain ⟨phi, hphi, hInd⟩ := hind
  have : Fact p.Prime := ⟨hpair.1⟩
  have hepow : e ^ p = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one e
  have hphiPow : phi ^ p = 1 :=
    TableBExc.pow_eq_one_of_induces hpsi hInd hepow
  have hphiNe : phi ≠ 1 := by
    intro hphiEq
    have heEq : e = 1 := ggAut_eq_one_of_induced_one psi hker hcomm e (fun l => by
      simpa only [hphiEq, MulAut.one_apply] using (hInd l).symm)
    have hpOne : 1 = p := by simpa only [heEq, orderOf_one] using he
    exact hpair.1.ne_one hpOne.symm
  exact ⟨phi, hphi, hInd, hP phi hphi (orderOf_eq_prime hphiPow hphiNe)⟩

end CFSG.StandardType.GGK0MarkedKacIface1587
