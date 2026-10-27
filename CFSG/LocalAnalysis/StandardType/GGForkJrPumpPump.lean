module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpSeven
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transfer

variable {G : Type} [Group G] [Finite G]

private theorem ggForkLatticeLabel_of_split {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hp5 : 5 ≤ p) (hs : LargeEvenSplit p lab) :
    GGForkLatticeLabel p lab := by
  have hprod : (2 ^ lab.n - 1) * (2 ^ lab.n + 1) = 4 ^ lab.n - 1 := by
    have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    have h4 : 4 ^ lab.n = 2 ^ lab.n * 2 ^ lab.n := by rw [← mul_pow]; norm_num
    rw [h4]
    zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ lab.n * 2 ^ lab.n ≠ 0)]
    ring
  have hdvd : p ∣ 4 ^ lab.n - 1 := by
    rcases hs with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, hp3⟩
    · rw [← hprod]; exact h.mul_right _
    · rw [← hprod]; exact h.mul_left _
    · rw [← hprod]; exact h.mul_right _
    · exfalso; omega
  have hn1 : lab.n ≠ 1 := by
    intro hn
    have hle : p ≤ 3 := by
      have hdvd1 : p ∣ 4 ^ 1 - 1 := by rwa [hn] at hdvd
      have h := Nat.le_of_dvd (by norm_num) hdvd1
      norm_num at h
      exact h
    omega
  exact ⟨hp5, Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hlab.1 (Ne.symm hn1)), hdvd⟩

theorem ggForkPump_of_known (hKG : GGForkLatticeKGInput) (hKG3 : GGForkE6TwoNoReflKGInput)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hres : GGForkNbrSevenExcl) : GGForkPump := by
  intro G _ _ p B Bs x L D J hcfg hop hInn hNT hsc hp5
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := by omega
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  refine ⟨?_, fun y K hnb => ?_⟩
  ·
    have hmarkL := hcfg.1.2.2.2.2.2.2.2.1
    obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hmarkL
    have hmark := ggInnerDiagOn_relabel hRig hInn.1 hlab hhas
    have hM : GGInnerDiagOnLabel GGForkLatticeLabel p Bs L := by
      have hlat : GGForkLatticeLabel p lab := ggForkLatticeLabel_of_split hlab hp5 hH.1
      refine largeEvenMarking_mono ?_ hmark
      rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
      subst h1
      exact ⟨hlat, h2, h3⟩
    obtain ⟨hL, lab', hlab', hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => GGForkLatticeLabel p lab)
      (fun lab hlab hs => hKG p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
    obtain ⟨R', _, I', F', -, -, θ', ⟨hs', hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ' hBsN hlift
    exact ggAutLattice_of_marking hp hp2 hBs hSC hL θ' hBsN
      (fun b hb => ggLAut_mem_of_induces L θ' hBsN h3 hb) hr h3' hT
  ·
    have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
    rcases ggNbr_latticeLabel_or_seven hRig hraw hiso hcfg hInn hp5 hnb with hM | hM | ⟨hp7, hA8⟩
    ·
      left
      obtain ⟨hK, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
        (S := fun lab => GGForkLatticeLabel p lab)
        (fun lab hlab hs => hKG p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
      obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw'
      exact ggAutLattice_of_marking hp hp2 hBs hSC hK θ hBsN
        (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
        (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hBsN hlift)
        (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT
    ·
      right
      obtain ⟨hK', lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
        (S := fun lab => GGForkE6TwoLabel p lab)
        (fun lab hlab hs => by rw [hs.2]; exact hKG3)
        (fun _ _ _ _ _ _ hP => hP.1) hM
      obtain ⟨R', _, I', F', -, -, θ', ⟨hs', hBsN', h3'⟩, r, hlift, hT⟩ :=
        largeEvenRawDatum_exists hraw'
      rw [← hs'.1] at hlift hT
      exact ggNoRefl_of_marking hp hp2 hBs hSC hK' θ' hBsN'
        (fun b hb => ggLAut_mem_of_induces K θ' hBsN' h3' hb)
        (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK' θ' hBsN' hlift)
        (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN') hT
    ·
      exfalso
      subst hp7
      exact hres G B Bs x L D J hcfg hop hInn hNT hsc y K hnb hA8

end Transfer

end CFSG.StandardType
