module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperPos
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrCell
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoLineTwoOmega
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


private theorem qTwoNbrLineOneCell {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (h5 : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L)
    {F : Type} [Field F]
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    {k : Fin n} (hJk : J = (TableBUE.blockSU (K := F) (n := 1) (Finset.univ.erase k)).map σ)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hKA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p k)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) :
    GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta 1 K k ∨
      GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta 1 K k := by
  have : Finite F := hfield.finite
  have hSk : (Finset.univ.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hS3 : 3 ≤ (Finset.univ.erase k).card := by omega
  have hSq : ((Finset.univ.erase k).card, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : (Finset.univ.erase k).card = 3 := congrArg Prod.fst h
    omega
  have hcard : (Finset.univ.erase k).card - 1 = n - 2 := by omega
  have hJ : GGHasLabel ⟨.twA, n - 2, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
    rw [hJk, ← hcard]
    exact GGSecFiveBPermUniLFrame.ggHasLabel_map_blockSU (S := Finset.univ.erase k)
      hLF hfield hS3 hSq
  exact hR.uniCell_of_bCoordinateBlock hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R
    (by omega) eta hK𝒦 k hKA le_rfl (fun h => by omega) hL hJ

private theorem qTwoNbrLineTwoCell {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L)
    {F : Type} [Field F]
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    {a a' : Fin n} (haa' : a ≠ a')
    (hroot : ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    (hcard4 : 4 ≤ (({a, a'} : Finset (Fin n))ᶜ).card)
    (hJline : J = (TableBUE.blockSU (K := F) (n := 1) ({a, a'} : Finset (Fin n))ᶜ).map σ)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hKA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn n p ({a, a'} : Finset (Fin n))ᶜ)
    (hCP : GGLabelCenterPCyclicInput) (hMp : GGInnerDiagMpInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) :
    7 ≤ n ∧ ∃ (K : Subgroup G) (a a' : Fin n), a ≠ a' ∧
      (∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧
      GGSecFiveBPermProperQTwoSpPairCell p Bs L 𝒦 n eta K a a' := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := hfield.finite
  have hpq : p ∣ 2 ^ 1 + 1 := by
    obtain ⟨lab, hlab, hhas, R, hRgrp, I, Fset, θ, hP⟩ :=
      largeEvenMarking_exists_hasLabel hL
    have h1 : p ∣ 2 ^ lab.n + 1 := by
      have h := hP.1.1
      unfold GGSecFiveBPermUniLabel at h
      exact h.2.2
    rwa [hP.1.2] at h1
  have hIcard : (({a, a'} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Finset.card_pair haa', Fintype.card_fin]
  rcases Nat.lt_or_ge n 7 with h6 | h7
  · obtain rfl : n = 6 := by omega
    exact (GGConfig.false_of_qTwo_six hR.1.1 rfl hpq eta hLF hfield haa' hroot hJline).elim
  · have hI3' : 3 ≤ (({a, a'} : Finset (Fin n))ᶜ).card := by omega
    have hSq : ((({a, a'} : Finset (Fin n))ᶜ).card, 2 ^ 1) ≠ (3, 2) := by
      intro h
      have h1 : (({a, a'} : Finset (Fin n))ᶜ).card = 3 := congrArg Prod.fst h
      omega
    have hlab := GGSecFiveBPermUniLFrame.ggHasLabel_map_blockSU
      (S := ({a, a'} : Finset (Fin n))ᶜ) (f := 1) hLF hfield hI3' hSq
    have hJ2 : GGHasLabel ⟨.twA, (({a, a'} : Finset (Fin n))ᶜ).card - 1, 1⟩
        (↥J ⧸ Subgroup.center ↥J) := by
      rw [hJline]
      exact hlab
    obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
    have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
    have hZ := ggNbr_card_center_le_of_centerPCyclic hCP hR.1.1 hInnK
    have hK := hR.uniNbr_label_of_bBlockOn hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R
      eta hK𝒦 (I := ({a, a'} : Finset (Fin n))ᶜ) hI3' hKA hZ le_rfl (fun h => by omega) hpq hJ2
    have hI1 : (({a, a'} : Finset (Fin n))ᶜ).card + 1 = n - 1 := by omega
    rcases hK.uniNbrLabel_iso (by omega) le_rfl (fun h => by omega) with hSp | hOm | hOm
    · refine ⟨by omega, K, a, a', haa', hroot, hL, hK𝒦, ?_, hKA⟩
      have hsub : (({a, a'} : Finset (Fin n))ᶜ).card + 1 - 1 = n - 2 := by omega
      exact hsub ▸ hSp
    · exact (GGConfig.false_of_qTwo_line_two_omega hMp hp2 hpq (by omega) hR.1.1 hB hInnK eta
        haa' hKA
        (Or.inl (hI1 ▸ hOm))).elim
    · exact (GGConfig.false_of_qTwo_line_two_omega hMp hp2 hpq (by omega) hR.1.1 hB hInnK eta
        haa' hKA
        (Or.inr (hI1 ▸ hOm))).elim

theorem ggSecFiveBPermProperQTwoNbrInput_of_inputs (hTBF : GGTBFixInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hRoot : GGSecFiveBProperRootInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hI3 : GGNbrSubcomponentInput) (hPJ : GGStdSubPrimeInput)
    (hTE6R : GGTwE6ThreeNbrRankInput) (hCP : GGLabelCenterPCyclicInput)
    (hMp : GGInnerDiagMpInput) : GGSecFiveBPermProperQTwoNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ _ eta hJoin hAut _ _ _ hB hL
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hL1 := GGInnerDiagOnLabel.n_eq_one_of_le_one hp hp2 hL
  obtain ⟨F, hFld, hFin, hChar, σ, χ, hfield, hLF, hline⟩ :=
    hR.exists_qTwo_line_of_ne hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hRoot hB eta
      hJoin hAut hL1
  let : Field F := hFld
  rcases hline with ⟨k, hJk, K, hK𝒦, hKA⟩ |
    ⟨a, a', haa', hroot, hcard4, hJline, K, hK𝒦, -, hKA⟩
  · exact Or.inl ⟨K, k, qTwoNbrLineOneCell hR (GGConfig.five_le_of_ne hR.1.1 hB eta) eta hL1
      hfield hLF hJk hK𝒦 hKA hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R⟩
  · exact Or.inr (qTwoNbrLineTwoCell hR hB eta hL1 hfield hLF haa' hroot hcard4 hJline hK𝒦
      hKA hCP hMp hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R)

end CFSG.StandardType

end
