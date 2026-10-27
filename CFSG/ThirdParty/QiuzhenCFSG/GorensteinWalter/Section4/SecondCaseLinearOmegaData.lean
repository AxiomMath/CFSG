module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaDataOfAlignedSylow

namespace CFSG
end CFSG
open CFSG

/-!
# The concrete linear omega-data producer

This compatibility wrapper specializes the source-faithful aligned-Sylow
producer to the later endpoint where the fixed ambient Sylow subgroup is
already contained in the selected component.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Construct synchronized linear omega data after the later endpoint
`S ≤ E`, by applying the aligned producer to the restrictions of `S`. -/
public theorem secondCase_linear_omegaData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hSleE : (c.S : Subgroup G) ≤ d.E) :
    Nonempty (SecondCaseLinearOmegaData c w d) := by
  classical
  have hSleM : (c.S : Subgroup G) ≤ w.M := hSleE.trans d.E_component.1
  have hSMp : IsPGroup 2 ((c.S : Subgroup G).subgroupOf w.M) :=
    c.S.isPGroup'.comap_subtype
  have hSMidx : ¬ 2 ∣ ((c.S : Subgroup G).subgroupOf w.M).index := by
    have hdvd : ((c.S : Subgroup G).subgroupOf w.M).index ∣
        (c.S : Subgroup G).index := by
      simpa [Subgroup.relIndex] using
        (Subgroup.relIndex_dvd_index_of_le
          (H := (c.S : Subgroup G)) (K := w.M) hSleM)
    intro h2
    exact c.S.not_dvd_index (h2.trans hdvd)
  let SM : Sylow 2 (↥w.M) := hSMp.toSylow hSMidx
  have hSEp : IsPGroup 2 ((c.S : Subgroup G).subgroupOf d.E) :=
    c.S.isPGroup'.comap_subtype
  have hSEidx : ¬ 2 ∣ ((c.S : Subgroup G).subgroupOf d.E).index := by
    have hdvd : ((c.S : Subgroup G).subgroupOf d.E).index ∣
        (c.S : Subgroup G).index := by
      simpa [Subgroup.relIndex] using
        (Subgroup.relIndex_dvd_index_of_le
          (H := (c.S : Subgroup G)) (K := d.E) hSleE)
    intro h2
    exact c.S.not_dvd_index (h2.trans hdvd)
  let SE : Sylow 2 (↥d.E) := hSEp.toSylow hSEidx
  have hSMamb : (SM : Subgroup w.M).map w.M.subtype =
      (c.S : Subgroup G) := by
    change ((c.S : Subgroup G).subgroupOf w.M).map w.M.subtype =
      (c.S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hSleM
  have hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      (c.S : Subgroup G) := by
    change ((c.S : Subgroup G).subgroupOf d.E).map d.E.subtype =
      (c.S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hSleE
  have hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G) := by
    rw [hSMamb]
  have hSEamb_join : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E := by
    rw [hSEamb, hSMamb]
    exact (inf_eq_left.mpr hSleE).symm
  obtain ⟨od, _hsSE, _hsS, _hsS0, _hF_eq, _hBcentSE, _hKnormSE,
      _hKcomm⟩ :=
    secondCase_linear_omegaData_of_alignedSylow
    hmin c w d K hK e SM hSMleS SE hSEamb_join
  exact ⟨od⟩

end CFSG.GorensteinWalter
