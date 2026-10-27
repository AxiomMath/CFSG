module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3OfProducers
public import CFSG.LocalAnalysis.StandardType.GGK1ScExcPair
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreOutdiag
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreLift
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreCentralTorsion

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.GGK0ExcB3Prod

variable
  (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

theorem ggK0ExcRealizedCentre_centred :
    GGK0ExcRealizedCentre Omega fun p lab => GGKacCentred lab p := by
  intro p lab hΛ hpair hcen Q hQ
  refine largeEvenRawDatum_mono ?_ ((largeEvenLabelAll_and
    (ggK0Schur_excPair p lab hΛ ⟨hpair, hcen⟩)
    (pElement_inner_of_centred hΛ hpair hcen)) Q hQ)
  rintro R _ I F ⟨hq, hcop, hinner⟩
  refine ⟨hq, ?_⟩
  intro L' _ _ ψ hψ hker hperf e hord phi hphiI hphi ρ _ hrz
  haveI : Fact p.Prime := ⟨hpair.1⟩
  obtain ⟨ER, hER, hcard, hfix, hcent, hIfix⟩ := PB3_assembly hpair hcen ρ hrz hinner
  obtain ⟨E, hEab, hEcard, hEfix, hEcent, hElift⟩ :=
    lift_elemAbelian_central hpair.1 ψ hψ hker (hcop L' ψ hψ hker hperf) e phi hphi ER hER hfix
      hcent
  refine ⟨E, hEab, hEcard.trans hcard, hEfix, hEcent, ?_⟩
  intro A heA hAel hAind z hz a ha
  obtain ⟨φa, hφaI, hφa⟩ := hAind a ha
  have hae : a * e = e * a := congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨e, heA⟩)
  have hcomm : φa * phi = phi * φa := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have h1 : (a * e) l = (e * a) l := by rw [hae]
    simp only [MulAut.mul_apply] at h1 ⊢
    rw [hphi, hφa, hφa, hphi, h1]
  exact hElift a φa hφa (fun y hy => hIfix y hy φa hφaI hcomm) z hz

theorem ggK0ExcRealizedCentre_all : GGK0ExcRealizedCentre Omega fun _ _ => True :=
  GGK0ExcRealizedCentre.mono (S' := fun p lab => ¬ GGKacCentred lab p ∨ GGKacCentred lab p)
    (fun p lab _ _ => (Classical.em (GGKacCentred lab p)).symm)
    ((ggK0ExcRealizedCentre_notCentred Omega).union (ggK0ExcRealizedCentre_centred Omega))

end CFSG.StandardType.GGK0ExcCentreU

end
