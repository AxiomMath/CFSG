module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinB
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperPos
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniJLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcSix
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal

theorem GuardedLargeEvenLabel.of_uniNbrLabel {m f : ℕ} (hm : 4 ≤ m) {lab : LargeEvenLabel}
    (h : GGSecFiveBPermUniNbrLabel m f lab) : GuardedLargeEvenLabel lab := by
  rcases h.2 with ⟨hBC, hr⟩ | ⟨hD, hr, -⟩ | ⟨hD, hr, -⟩
  · exact Or.inl ⟨hBC, by omega⟩
  · exact Or.inr (Or.inl ⟨Or.inl hD, by omega⟩)
  · exact Or.inr (Or.inl ⟨Or.inr hD, by omega⟩)


theorem GGSecFiveRouteCfg.exists_guarded_nbr_of_bPermUni (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hI3 : GGNbrSubcomponentInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    (hRoot : GGSecFiveBProperRootInput) (hCP : GGLabelCenterPCyclicInput)
    (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hU : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab) p Bs L) :
    ∃ (y : G) (K : Subgroup G), K ∈ 𝒦 ∧ GGNbr p B x D J y K ∧ y ∈ ggG0 p B x L D J ∧
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have hBG0 : Bs ≤ ggG0 p B x L D J :=
    hR.bstar_le_ggG0_of_B hTBF hWI hP ⟨n, Equiv.refl _, by omega,
      (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hn4 : n ≠ 4 := by
    rintro rfl
    exact not_ggInnerDiagOnLabel_unitary_four hR.1.1
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨⟨Or.inl h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩) hU)
  have hfin : ∀ {m f : ℕ} {K : Subgroup G}, K ∈ 𝒦 → 4 ≤ m →
      GGInnerDiagOnLabel (fun _ lab => GGSecFiveBPermUniNbrLabel m f lab) p Bs K →
      ∃ (y : G) (K : Subgroup G), K ∈ 𝒦 ∧ GGNbr p B x D J y K ∧ y ∈ ggG0 p B x L D J ∧
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) := by
    intro m f K hK𝒦 hm hlab
    obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
    exact ⟨y, K, hK𝒦, hnb, hBG0 (hR.1.1.2.1.1 hnb.1.2.1),
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => GuardedLargeEvenLabel.of_uniNbrLabel hm h.1) hlab⟩
  have hU' : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) ∨
      (GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1)) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨?_, h.2⟩) hU
    rcases le_or_gt 2 lab.n with h2 | h2
    · exact Or.inl ⟨h.1, h2⟩
    · exact Or.inr ⟨h.1, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n)
      (T := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) hU' with hU4 | hU2
  ·
    obtain ⟨f, hf, hUf⟩ := hU4.exists_n_eq_of_two_le
    have hpf : p ∣ 2 ^ f + 1 := by
      obtain ⟨lab, _, _, R, _, I, Fset, θ, hP'⟩ := largeEvenMarking_exists_hasLabel hUf
      have h := hP'.1.1.2.2
      rwa [hP'.1.2] at h
    by_cases hB : B = Bs
    · obtain ⟨K, hK𝒦, i0, hKA⟩ := hR.exists_mem_bCoordinateBlock hX hTCJ hRig hTPn hA8 hraw
        hiso hFC hB (by omega) eta hJoin hAut
      have hJ := hR.ggHasLabel_J_of_uniLabel hn (fun h => absurd h (by omega)) eta hAut hUf
        (Or.inl hB) (fun _ => hB)
      exact (hfin hK𝒦 hn (hR.uniNbr_label hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R
        hn eta hK𝒦 i0 hKA (by omega) (fun _ => hf) hpf hJ))
    · obtain ⟨K, hK𝒦, i0, hKA⟩ := hR.exists_mem_bCoordinateBlock_of_ne hTBF hX hTCJ hRig hTPn
        hA8 hraw hiso hFC hLB hRoot hB eta hJoin hAut hU4
      obtain ⟨a, a', haa', hroot⟩ := hRoot G p B Bs x L D J 𝒦 hR hB n eta hJoin hAut
      have hJ := hR.ggHasLabel_J_of_uniLabel hn (fun h => absurd h (by omega)) eta hAut hUf
        (Or.inr ⟨a, a', haa', hroot⟩) (fun h => absurd h (by omega))
      exact (hfin hK𝒦 hn (hR.uniNbr_label hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ hTE6R
        hn eta hK𝒦 i0 hKA (by omega) (fun _ => hf) hpf hJ))
  ·
    have hL1 := hU2.n_eq_one_of_le_one hp hp2
    have hpq : p ∣ 2 ^ 1 + 1 := by
      obtain ⟨lab, _, _, R, _, I, Fset, θ, hP'⟩ := largeEvenMarking_exists_hasLabel hL1
      have h := hP'.1.1.2.2
      rwa [hP'.1.2] at h
    have hn5 : 5 ≤ n := by omega
    by_cases hB : B = Bs
    · by_cases hz : Line63.H5.twoCenter L = ⊥
      · obtain ⟨K, hK𝒦, i0, hKA⟩ := hR.exists_mem_bCoordinateBlock hX hTCJ hRig hTPn hA8 hraw
          hiso hFC hB (by omega) eta hJoin hAut
        have hJ := hR.ggHasLabel_J_of_uniLabel hn (fun _ => hz) eta hAut hL1 (Or.inl hB)
          (fun _ => hB)
        exact (hfin hK𝒦 hn (hR.uniNbr_label hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ
          hTE6R hn eta hK𝒦 i0 hKA le_rfl (fun h => absurd h hn4) hpq hJ))
      · by_cases hn6 : n = 6
        · subst hn6
          exact (hR.false_of_uniQTwoSix_twoCenter_ne_bot hRig hU62 eta hJoin hAut hB hU2 hz).elim
        · exact absurd (twoCenter_eq_bot_of_uniLabel_two hRig hR hn5 hn6 hU2) hz
    · obtain ⟨F, hFld, hFin, hChar, σ, χ, hfield, hLF, hline⟩ :=
        hR.exists_qTwo_line_of_ne hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hRoot hB eta
          hJoin hAut hL1
      let : Field F := hFld
      have : Finite F := hfield.finite
      rcases hline with ⟨k, hJk, K, hK𝒦, hKA⟩ |
        ⟨a, a', haa', hroot, hcard4, hJline, K, hK𝒦, -, hKA⟩
      ·
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
        exact (hfin hK𝒦 hn (hR.uniNbr_label hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ
          hTE6R hn eta hK𝒦 k hKA le_rfl (fun h => absurd h hn4) hpq hJ))
      ·
        have hIcard : (({a, a'} : Finset (Fin n))ᶜ).card = n - 2 := by
          rw [Finset.card_compl, Finset.card_pair haa', Fintype.card_fin]
        rcases Nat.lt_or_ge n 7 with h6 | h7
        · obtain rfl : n = 6 := by omega
          exact (GGConfig.false_of_qTwo_six hR.1.1 rfl hpq eta hLF hfield haa' hroot
            hJline).elim
        · have hI3' : 3 ≤ (({a, a'} : Finset (Fin n))ᶜ).card := by omega
          have hSq : ((({a, a'} : Finset (Fin n))ᶜ).card, 2 ^ 1) ≠ (3, 2) := by
            intro h
            have h1 : (({a, a'} : Finset (Fin n))ᶜ).card = 3 := congrArg Prod.fst h
            omega
          have hJ2 : GGHasLabel ⟨.twA, (({a, a'} : Finset (Fin n))ᶜ).card - 1, 1⟩
              (↥J ⧸ Subgroup.center ↥J) := by
            rw [hJline]
            exact GGSecFiveBPermUniLFrame.ggHasLabel_map_blockSU
              (S := ({a, a'} : Finset (Fin n))ᶜ) (f := 1) hLF hfield hI3' hSq
          obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
          have hZ := ggNbr_card_center_le_of_centerPCyclic hCP hR.1.1 (hR.1.2.2.1.2 y K hnb)
          exact (hfin hK𝒦 (by omega) (hR.uniNbr_label_of_bBlockOn hT hLift hTCJ hI3 hRig
            hraw hiso hLB hPJ hTE6R eta hK𝒦 (I := ({a, a'} : Finset (Fin n))ᶜ) hI3' hKA hZ le_rfl
            (fun h => by omega) hpq hJ2))

end CFSG.StandardType

end
