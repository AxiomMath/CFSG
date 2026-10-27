module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrCell
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGSecFiveRouteCfg.exists_mem_bCoordinateBlock {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 0 < n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∃ K ∈ 𝒦, ∃ i0 : Fin n,
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 := by
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  by_contra hno
  have hno' : ∀ K ∈ 𝒦, ∀ j : Fin n,
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≠ bCoordinateBlock n p j := by
    intro K hKmem j hj
    exact hno ⟨K, hKmem, j, hj⟩
  have hsup : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      ⨆ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
    rw [← hEta]
    simp only [ggAutomizerJoin, Subgroup.map_sup, Subgroup.map_iSup]
  have hKle : ∀ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤
      coordProdStab n p := by
    intro K hKmem
    obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hKmem
    rcases GGSecFiveRouteCfg.nbr_coordType (y := y) (K := K) hX hTCJ hRig hTPn hA8 hraw
        hiso hFC hR hB eta hEta hy
        (le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K hKmem))
        with ⟨j, hj | hj⟩ | ⟨δ, hδ, hδeq⟩
    · exact absurd hj (hno' K hKmem j)
    · rw [hj]
      exact dCoordinateBlock_le_coordProdStab j
    · rw [hδeq]
      exact aPermutationFull_map_conj_le_coordProdStab hδ
  have hLle : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rw [hLA]
    exact aPermutationFull_le_coordProdStab
  have hle : bSignedFull n p ≤ coordProdStab n p := by
    rw [← hsup]
    exact sup_le hLle (iSup₂_le hKle)
  exact sgnAut_not_mem_coordProdStab hp hp2 ⟨0, hn⟩
    (hle (Subgroup.subset_closure (Or.inl ⟨⟨0, hn⟩, rfl⟩)))

section Assembly


theorem ggSecFiveBPermUniNbrInput_of_inputs (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) : GGSecFiveBPermUniNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n e _ hn eta hEta hLA _ _ _ hB hL
  obtain ⟨K, hK𝒦, i0, hAut⟩ := hR.exists_mem_bCoordinateBlock hX hTCJ hRig hTPn hA8 hraw
    hiso hFC hB (by omega) eta hEta hLA
  obtain ⟨f, hf, hL'⟩ := hL.exists_n_eq_of_two_le
  have hJ := hR.ggHasLabel_J_of_uniLabel hn (fun h => absurd h (by omega)) eta hLA hL'
    (Or.inl hB) (fun _ => hB)
  exact ⟨f, K, i0, hf, hR.uniCell_of_bCoordinateBlock hT hLift hTCJ hI3 hRig hraw hiso hLB
    hPJ hTE6R hn eta hK𝒦 i0 hAut (by omega) (fun _ => hf) hL' hJ⟩

theorem ggSecFiveBPermUniQTwoNbrInput_of_inputs (hX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) : GGSecFiveBPermUniQTwoNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n e _ hn eta hEta hLA _ _ _ hB hL hz
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨K, hK𝒦, i0, hAut⟩ := hR.exists_mem_bCoordinateBlock hX hTCJ hRig hTPn hA8 hraw
    hiso hFC hB (by omega) eta hEta hLA
  have hL1 := hL.n_eq_one_of_le_one hp hp2
  have hJ := hR.ggHasLabel_J_of_uniLabel (by omega) (fun _ => hz) eta hLA hL1 (Or.inl hB)
    (fun _ => hB)
  exact ⟨K, i0, hR.uniCell_of_bCoordinateBlock hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R
    (by omega) eta hK𝒦 i0 hAut le_rfl (fun h => absurd h (by omega)) hL1 hJ⟩

end Assembly

end CFSG.StandardType

end
