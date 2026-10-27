module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2AlignedSylowDecomposition

namespace CFSG
end CFSG
open CFSG

/-!
# The fixed-ambient-Sylow decomposition in the PSL₂ branch

This compatibility wrapper specializes the source-faithful aligned-Sylow
producer to the later endpoint where the fixed ambient Sylow subgroup is
already contained in the selected component.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- After the later endpoint `S ≤ E`, specialize the aligned equations-(1)--(3)
decomposition to the restrictions of the fixed ambient Sylow subgroup. -/
public theorem secondCase_psl2_fixedAmbientSylow_decomposition
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hSleE : (c.S : Subgroup G) ≤ d.E) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E), ∃ s : d.E,
          let q : d.E →* d.E ⧸ Subgroup.center d.E :=
            QuotientGroup.mk' (Subgroup.center d.E)
          let qt : d.E ⧸ Subgroup.center d.E := q ⟨c.t, d.t_mem_E⟩
          let UEbar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
            ((c.U ⊓ d.E).subgroupOf d.E).map q
          s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
            IsCyclic T ∧ qt ∈ T ∧ q s ∉ T ∧
            ((SE.mapSurjective
                (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
                Subgroup (d.E ⧸ Subgroup.center d.E)) ≤
              T ⊔ Subgroup.zpowers (q s)) ∧
            Subgroup.normalizer (Subgroup.zpowers qt :
              Set (d.E ⧸ Subgroup.center d.E)) =
              T ⊔ Subgroup.zpowers (q s) ∧
            BenderGlauberman.IsInvertedBy (q s) T ∧
            (∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
              (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                Odd (orderOf x)) →
                X ≤ Subgroup.centralizer
                  ({qt} : Set (d.E ⧸ Subgroup.center d.E)) →
                X ≤ T) ∧
            UEbar ≤ T ∧
            IsCyclic UEbar ∧
            BenderGlauberman.IsInvertedBy (q s) UEbar ∧
            (s : G) ∈ (c.S : Subgroup G) ∧ (s : G) ∉ c.S0 ∧
            ∃ K B : Subgroup G,
              (K : Set G) =
                invertedElements (c.U ⊓ w.M) (s : G) ∧
              IsCyclic K ∧
              B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
              B ≤ Subgroup.centralizer
                (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) ∧
              K ≤ d.E ∧
              (K.subgroupOf d.E).map
                  (QuotientGroup.mk' (Subgroup.center d.E)) = UEbar ∧
              (K.subgroupOf d.E) ⊓ Subgroup.center d.E = ⊥ ∧
              ((SE : Subgroup d.E).map d.E.subtype) ≤
                Subgroup.normalizer (K : Set G) ∧
              K ⊔ B = c.U ⊓ w.M ∧
              ∃ K0 F : Subgroup G,
                K0 = fittingSubgroupOf c.U ⊓ K ∧
                F = fittingSubgroupOf c.U ⊓ B ∧
                F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G) ∧
                K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M := by
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
  rcases secondCase_psl2_alignedSylow_decomposition
      hmin c w d K hK e SM hSMleS SE hSEamb_join with
    ⟨hSMcent, hSEeq, hrest⟩
  exact ⟨SM, hSMcent, SE, hSEeq, hrest⟩

end CFSG.GorensteinWalter
