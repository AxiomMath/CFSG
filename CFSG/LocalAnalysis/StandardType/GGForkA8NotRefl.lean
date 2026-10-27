module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpPump

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem not_ggReflGenerated_of_hom_three {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)}
    (χ : ↥A →* Multiplicative (ZMod 3)) (hχ : χ ≠ 1) : ¬ GGReflGenerated p A := by
  intro hA
  apply hχ
  have key : ∀ x : Multiplicative (ZMod 3), x ^ 2 = 1 → x = 1 := by decide
  have hle : A ≤ (χ.ker).map A.subtype := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    rintro φ ⟨hφA, hφr⟩
    refine ⟨⟨φ, hφA⟩, ?_, rfl⟩
    show χ ⟨φ, hφA⟩ = 1
    apply key
    rw [← map_pow]
    have h2 : (⟨φ, hφA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hφr.1)
    rw [h2, map_one]
  ext a
  obtain ⟨b, hb, hba⟩ := hle a.2
  have : b = a := Subtype.ext hba
  subst this
  simpa using hb


@[expose] def GGForkA8NotReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 7 B Bs x L D J → GGInnerDiagAll 7 B Bs x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr 7 B x D J y K →
        GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K) →
        ∃ χ : ↥(ggAutomizer K Bs) →* Multiplicative (ZMod 3), χ ≠ 1

@[expose] def GGForkNbrSevenExcl' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 7 B Bs x L D J → GGOpAutTrivial 7 Bs → GGInnerDiagAll 7 B Bs x L D J →
      GGNoTransvection 7 Bs →
      ∀ (y : G) (K : Subgroup G), GGNbr 7 B x D J y K → GGReflGenerated 7 (ggAutomizer K Bs) →
        ¬ GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K)

theorem ggForkNbrSevenExcl'_of_notRefl (hA8 : GGForkA8NotReflInput) : GGForkNbrSevenExcl' := by
  intro G _ _ B Bs x L D J hC _ hID _ y K hK hRG hlab
  obtain ⟨χ, hχ⟩ := hA8 G B Bs x L D J hC hID y K hK hlab
  exact not_ggReflGenerated_of_hom_three χ hχ hRG

section Transfer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggForkLatticeLabel_of_split' {p : ℕ} {lab : LargeEvenLabel}
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

theorem ggForkPump'_of_known (hKG : GGForkLatticeKGInput) (hKG3 : GGForkE6TwoNoReflKGInput)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hres : GGForkNbrSevenExcl') : GGForkPump' := by
  intro G _ _ p B Bs x L D J hcfg hop hInn hNT hW hp5
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := by omega
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  refine ⟨?_, fun y K hnb => ?_⟩
  ·
    have hmarkL := hcfg.1.2.2.2.2.2.2.2.1
    obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hmarkL
    have hmark := ggInnerDiagOn_relabel hRig hInn.1 hlab hhas
    have hM : GGInnerDiagOnLabel GGForkLatticeLabel p Bs L := by
      have hlat : GGForkLatticeLabel p lab := ggForkLatticeLabel_of_split' hlab hp5 hH.1
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
      exact hres G B Bs x L D J hcfg hop hInn hNT y K hnb (hW y K hnb) hA8

end Transfer

theorem ggForkPump'_of_notRefl (hKG : GGForkLatticeKGInput) (hKG3 : GGForkE6TwoNoReflKGInput)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hA8 : GGForkA8NotReflInput) : GGForkPump' :=
  ggForkPump'_of_known hKG hKG3 hRig hraw hiso (ggForkNbrSevenExcl'_of_notRefl hA8)

theorem ggForkPumpOr_of (h : GGForkPump) (h' : GGForkPump') : GGForkPumpOr := by
  intro G _ _ p B Bs x L D J hC hO hI hT hSW hp
  rcases hSW with hs | hW
  · exact h G p B Bs x L D J hC hO hI hT hs hp
  · exact h' G p B Bs x L D J hC hO hI hT hW hp

theorem ggSecFiveWeylCase_of_prime_three {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J)
    (hW : GGSecFiveWeylCase' 3 B Bs x D J) : GGSecFiveWeylCase 3 B Bs x D J :=
  ⟨ggScalarsPmOne_of_prime_three hC rfl, hW⟩

end CFSG.StandardType
