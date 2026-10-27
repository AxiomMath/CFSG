module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Orth
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Shape
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26Final

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.F53Push CFSG.Quasithin.F53Mod CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem sitSigma_false_nonresidual (hA : F53Amalgam H M S) (hb : 1 < bMin H M)
    {δ μ : Geo H M} {U : Subgroup G} (hSig : SitSigma δ μ U) (hQ : Qv μ ≤ U)
    (h : pCoreOf 2 U ≤ Qv δ ∨ ¬ Qv δ ≤ Qv μ) : False := by
  have hPn := SitSigma.stab_le_normalizer_of_le hQ
  by_cases hR : pCoreOf 2 U ≤ Qv δ
  · rcases SitSigma.false_or_orth_of_O2Ubar_trivial hA hb hSig hQ hR with hF | ⟨hq5, hO⟩
    · exact hF
    · exact hSig.false_of_orth hA hb hQ hR hq5 hO
  · exact hSig.false_of_D12 (baumannS3_holds G) hA hPn hR (h.resolve_left hR)
      (hSig.shape_three_of_not_le hA hPn hR)

end CFSG.Quasithin.F53
