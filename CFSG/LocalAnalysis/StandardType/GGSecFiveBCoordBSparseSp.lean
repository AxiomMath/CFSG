module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {G : Type} [Group G]

section Inputs


theorem ggSecFiveBCoordBSparseLargeInput_of_sp_twD (hSp : GGSecFiveBCoordBSparseSpLargeInput)
    (hTw : GGSecFiveBCoordBSparseTwDLargeInput) : GGSecFiveBCoordBSparseLargeInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hD
  have hLab' : GGInnerDiagOnLabel (fun p lab =>
      (GGSecFiveBCoordBLabel n p lab ∧ (lab.n ≠ 1 ∧ (lab.tag = .B ∨ lab.tag = .C))) ∨
        (GGSecFiveBCoordBLabel n p lab ∧ (lab.n ≠ 1 ∧ lab.tag = .twD))) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ hPl => ⟨?_, hPl.2⟩) hLab
    obtain ⟨⟨hl, h1⟩, -⟩ := hPl
    have hl' := hl
    rcases hl' with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, -, -, h1', -⟩ | ⟨-, -, h1', -⟩
    · exact Or.inl ⟨hl, h1, ht⟩
    · exact Or.inr ⟨hl, h1, ht⟩
    · exact absurd h1' h1
    · exact absurd h1' h1
  rcases hLab'.elim_or with h | h
  · exact hSp G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD
  · exact hTw G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL h hB hRM hG0 hSpC hSpSpC hOmC hD

theorem ggSecFiveBCoordBSparseTwDLargeInput_of_four_five
    (h4 : GGSecFiveBCoordBSparseOn fun n _ lab => n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD)
    (h5 : GGSecFiveBCoordBSparseOn fun n _ lab => 5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD) :
    GGSecFiveBCoordBSparseTwDLargeInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hD
  rcases Nat.lt_or_eq_of_le hn with h5' | h4'
  · exact h5 G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hPl => ⟨⟨hPl.1.1, h5', hPl.1.2⟩, hPl.2⟩) hLab)
      hB hRM hG0 hSpC hSpSpC hOmC hD
  · exact h4 G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hPl => ⟨⟨hPl.1.1, h4'.symm, hPl.1.2⟩, hPl.2⟩)
        hLab)
      hB hRM hG0 hSpC hSpSpC hOmC hD

end Inputs

section Cover


theorem GGInnerDiagOnLabel.exists_statedSp_of_spLarge {p n : ℕ} (hn : 4 ≤ n)
    {Bs L : Subgroup G} [Finite G]
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n ≠ 1 ∧ (lab.tag = .B ∨ lab.tag = .C))) p Bs L) :
    ∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      (GGHasLabel ⟨.B, n - 1, f⟩ (↥L ⧸ Subgroup.center ↥L) ∨
        GGHasLabel ⟨.C, n - 1, f⟩ (↥L ⧸ Subgroup.center ↥L)) ∧
      Nonempty (↥L ≃* StatedSp (n - 1) (GaloisField 2 f)) := by
  obtain ⟨lab, hlab2, ⟨hl, h1, htag⟩, hhas, -⟩ := hLab.exists_label_eq
  have hperf : commutator ↥L = ⊤ := hLab.1
  rcases lab with ⟨tag, rank, f⟩
  dsimp only at hlab2 h1 htag hhas
  have hf2 : 2 ≤ f := by
    have h1f : 1 ≤ f := hlab2.1
    omega
  unfold GGSecFiveBCoordBLabel at hl
  dsimp only at hl
  rcases hl with ⟨-, hrank, hdiv⟩ | ⟨htw, -, -⟩ | ⟨htD, -, -, -, -⟩ |
    ⟨htA, -, hf1', -⟩
  · obtain rfl : rank = n - 1 := by simpa using hrank
    rcases hdiv with hpd | ⟨hf1', -⟩
    · refine ⟨f, hf2, hpd, ?_, ?_⟩
      · rcases htag with rfl | rfl
        · exact Or.inl hhas
        · exact Or.inr hhas
      · refine nonempty_mulEquiv_statedSp_of_hasLabel hperf (by omega) hf2 ?_
        rcases htag with rfl | rfl
        · exact Or.inl hhas
        · exact Or.inr hhas
    · exact absurd hf1' h1
  · rcases htag with rfl | rfl
    · exact absurd htw (by decide)
    · exact absurd htw (by decide)
  · rcases htag with rfl | rfl
    · exact absurd htD (by decide)
    · exact absurd htD (by decide)
  · exact absurd hf1' h1

theorem nonempty_mulEquiv_statedSp_of_quotient_mulEquiv [Finite G] {L K : Subgroup G}
    (hK : commutator ↥K = ⊤) {m f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f)
    (hlab : GGHasLabel ⟨.B, m, f⟩ (↥L ⧸ Subgroup.center ↥L) ∨
      GGHasLabel ⟨.C, m, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (↥K ⧸ Subgroup.center ↥K)) :
    Nonempty (↥K ≃* StatedSp m (GaloisField 2 f)) := by
  refine nonempty_mulEquiv_statedSp_of_hasLabel hK hm hf ?_
  rcases hlab with h | h
  · exact Or.inl (ggHasLabel_of_mulEquiv e h)
  · exact Or.inr (ggHasLabel_of_mulEquiv e h)

theorem ggSecFiveBCoordBSparseSpLargeInput_of_spFour (hSF : GGSecFiveBCoordBSpFourInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) : GGSecFiveBCoordBSparseSpLargeInput := by
  have hE := ggSecFiveBCoordBSparseEndpointOn_holds fun _ _ lab =>
    lab.n ≠ 1 ∧ (lab.tag = .B ∨ lab.tag = .C)
  have hE4 := ggSecFiveBCoordBSparseEndpointFourOn_holds fun _ _ lab =>
    lab.n ≠ 1 ∧ (lab.tag = .B ∨ lab.tag = .C)
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hSpC hSpSpC hOmC hD
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨K, hKmem, hKL⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta h𝒦 hL
  obtain ⟨y, hyK⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := hB ▸ hyK.1.2.1
  obtain ⟨f, hf, hpd, hlabL, ⟨eL⟩⟩ := hLab.exists_statedSp_of_spLarge hn
  have hlab0 : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hLab
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by omega) eta h𝒦 hL
    hyK (hRM y K hyK) hKL hy with ⟨j, hj, hblk, hax⟩ | ⟨⟨δ, hδ, hKδ⟩, -⟩
  · have hKperf : commutator ↥K = ⊤ := (hR.1.2.2.1.2 y K hyK).1
    rcases Nat.lt_or_eq_of_le hn with h5 | h4
    · have h5' : 5 ≤ n := h5
      obtain ⟨hKb, ⟨eLK⟩⟩ :=
        hE G p B Bs x L D J 𝒦 hR n e hP h5' eta i0 h𝒦 hL hLab hB hRM y hy K j hKmem
          hyK hj hax hblk
      have hKsp : Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) :=
        nonempty_mulEquiv_statedSp_of_quotient_mulEquiv hKperf (by omega) hf hlabL eLK
      exact (hSpSpC ⟨f, K, hf, h5', hKmem, ⟨eL⟩, hKsp, j, hj, hKb⟩).elim
    · obtain ⟨hKb, ⟨eLK⟩⟩ :=
        hE4 G p B Bs x L D J 𝒦 hR n e hP h4.symm eta i0 h𝒦 hL hLab hB hRM y hy K j hKmem
          hyK hj hax hblk
      have hKsp : Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) :=
        nonempty_mulEquiv_statedSp_of_quotient_mulEquiv hKperf (by omega) hf hlabL eLK
      refine hSF G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hlab0 hB hRM hG0 f K ?_
      exact ⟨hf, h4.symm, hKmem, ⟨eL⟩, hKsp, j, hj, hKb⟩
  · exact (hD ⟨K, hKmem, δ, hδ, hKδ⟩).elim

end Cover

end CFSG.StandardType

end
