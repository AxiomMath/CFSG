module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRealized
public import CFSG.LocalAnalysis.StandardType.GGNSJoinGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

@[expose] def NSTypeA5 {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (m : ℕ) (e : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex e

@[expose] def NSTypeD {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  GGIsWeylMatrixD M

theorem nsTypeAD_iff {ι : Type} (M : CoxeterMatrix ι) : NSTypeAD M ↔ NSTypeA5 M ∨ NSTypeD M :=
  Iff.rfl

theorem nsRegularCfg_cases {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (h : NSRegularCfg p B Bs x L D J 𝒦) :
    NSRegularCfgOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M) p B Bs x L D J 𝒦 ∨
      NSRegularCfgOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M) p B Bs x L D J 𝒦 := by
  obtain ⟨h1, h2, ι, M, e, hpres, hT, hbig⟩ := h
  rcases hT with hA | hD
  · exact Or.inl ⟨h1, h2, ι, M, e, hpres, hA, hbig⟩
  · exact Or.inr ⟨h1, h2, ι, M, e, hpres, hD, hbig⟩

theorem nsJA2Input_of_types
    (hA : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hD : NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)) : NSJA2Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg
  rcases nsRegularCfg_cases hcfg with h | h
  · exact hA G p B Bs x L D J 𝒦 h
  · exact hD G p B Bs x L D J 𝒦 h

theorem nsNbrQFourInput_of_types
    (hA : NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hD : NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)) :
    NSNbrQFourInput := by
  intro G _ _ B Bs x L D J 𝒦 hcfg
  rcases nsRegularCfg_cases hcfg with h | h
  · exact hA G B Bs x L D J 𝒦 h
  · exact hD G B Bs x L D J 𝒦 h

theorem nsNbrLocalGenInput_of_types
    (hA : NSNbrLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hD : NSNbrLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)) :
    NSNbrLocalGenInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0 hns hguard
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  rcases hT with hA' | hD'
  · exact hA G p B Bs x L D J 𝒦 hcfg0 hns ⟨ι, M, e, hpres, hA', hbig⟩
  · exact hD G p B Bs x L D J 𝒦 hcfg0 hns ⟨ι, M, e, hpres, hD', hbig⟩

end NSJoin

end CFSG.StandardType

end
