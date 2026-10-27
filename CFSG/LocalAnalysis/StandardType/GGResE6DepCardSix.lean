module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixRank5
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabel
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
public import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResTwoSettledDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggResLeviDatumExact2_any_of_dep_L
    {G : Type} [Group G] [Finite G] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelDep ggTypLE6) :
    GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, trivial,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩

theorem ggResLeaf_e6Dep_cardSix (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L) :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      p = 3 ∧ Nat.card Bs = 3 ^ 6 ∧
      GGResLeviDatumExact2 p Bs L J K ggSelDep ggTypLE6 ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE hP
  obtain ⟨hp3, hcard, hD, hno3, hres, hrowTN, hrowC, hrowSU⟩ := hP
  haveI : Fact p.Prime := hfact
  have hDdep : GGResLeviDatumExact2 p Bs L J K ggSelDep ggTypLE6 := hD
  subst hp3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  rcases (by omega : Nat.card Λa = 1 ∨ Nat.card Λa = 2 ∨ Nat.card Λa = 3) with
    hΛa1 | hΛa2 | hΛa3
  ·
    have hOrbK : GGResCentBoundNbrInput := ggResCentBoundNbrInput_holds
    exact ggResE6Dep_cardSix_rank5 hH hOrbK hcard hS2 hΛa1 hWML hCLL hWMK hCKK htyp hlin
      hrefl hpairL hpairK hsel hfL hfK hclosL hclosK hdel
  ·
    have hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L := fun h => hrowTN (Or.inl h)
    have hnoSU : ¬ GGResRowAt ggRowSUCorank2 3 J L := fun h => hrowSU (Or.inl h)
    have hMark := hH.e6_marking_of_original_L_E6_datum hDdep hnoRowL hnoSU
    have hDany : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 :=
      ggResLeviDatumExact2_any_of_dep_L hDdep
    have hMark' : GGInnerDiagOnLabel
        (fun _ lab => (GGE6DepLabel lab ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)) 3 Bs L :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨by
        rcases hP.1 with ⟨ht, hd⟩ | ⟨ht, hd⟩
        · exact Or.inl ⟨Or.inl ⟨ht, hd⟩, hd⟩
        · exact Or.inr ⟨Or.inr ⟨ht, hd⟩, ht, hd⟩, hP.2⟩) hMark
    rcases hMark'.elim_or with hsplit | htw
    ·
      exact (hH.not_e6_exactTwo_either_of_splitE6_L hsplit hnoRowL (Or.inl hDany)).elim
    ·
      have hResid : GGTwE6ExactTwoPSU5Residual (G := G) Bs L J :=
        hH.twE6_exactTwo_either_classification htw (Or.inl hDany) hnoRowL
      obtain ⟨e6, -⟩ := htyp
      have hΛ6 : Fintype.card Λ = 6 := by simpa using Fintype.card_congr e6.symm
      have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
        rw [Fintype.card_subtype]; simp
      have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
        change Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card
        rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
      have hT4 : Fintype.card {i : Λ // i ∉ S} = 4 := by omega
      have hK6 : Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) = 6 := by
        rw [Fintype.card_sum, hT4, ← Nat.card_eq_fintype_card, hΛa2]
      obtain ⟨e, he⟩ :=
        rank_six_CK_E6_of_witness (ML := ML) (CL := CL) hH hWMK hCKK hlin hpairK hclosK hK6 hcard
      obtain ⟨fK, hfK'⟩ := hfK
      have hφmem : ∀ o : {i : Λ // i ∉ S} ⊕ Λa,
          φ (o.map Subtype.val id) ∈ ggAutomizer K Bs := by
        intro o
        rw [hclosK]
        refine Subgroup.subset_closure ?_
        rcases o with j | a
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr ⟨a, rfl⟩
      exact (narrow_tableP_excludes_twA4_twE6 hH hB36 hResid hcard hCKK e he fK ι
        (fun o => φ (o.map Subtype.val id)) (fun o => h (o.map Subtype.val id))
        (fun o => α (o.map Subtype.val id)) (fun o v => hlin (o.map Subtype.val id) v)
        (fun o o' => hpairK o o') hφmem).elim
  ·
    have hrev : GGResLeviDatumCard (Nat.card Λa) 3 Bs K J L ggSelAny ggTypAny :=
      ggResLeviDatumCard_reverse_of_witness (S := S) (by omega) (by omega)
        hWML hCLL hWMK hCKK hlin hrefl hpairL hpairK hfL hfK hclosL hclosK hdel hclosJ
    have h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
      simpa only [hΛa3] using hrev
    exact absurd (Or.inr h3) hno3

theorem ggResLeaf_e6Dep (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L) :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      p = 3 ∧ GGResLeviDatumExact2 p Bs L J K ggSelDep ggTypLE6 ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE hP
  obtain ⟨hp3, hD, hno3, hres, hrowTN, hrowC, hrowSU⟩ := hP
  haveI : Fact p.Prime := hfact
  subst hp3
  rcases hH.card_Bs_six_or_seven_of_original_L_E6_datum hD with h6 | h7
  · exact ggResLeaf_e6Dep_cardSix hB36 G 3 B Bs x L D J y K hH hF hS hE
      ⟨rfl, h6, hD, hno3, hres, hrowTN, hrowC, hrowSU⟩
  · exact hH.weyl_join_of_original_L_E6_dep_card_seven hD h7

theorem ggResLeaf_e6ExactTwo (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L) :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      p = 3 ∧ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypLE6 ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  classical
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE hP
  obtain ⟨hp3, hD, hno3, hres, hrowTN, hrowC, hrowSU⟩ := hP
  haveI : Fact p.Prime := hfact
  subst hp3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, _,
    hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  by_cases hLI : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))
  · apply hH.e6_exactTwo_independent_L_weyl_join
    exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hLI,
      hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩
  · apply ggResLeaf_e6Dep hB36 G 3 B Bs x L D J y K hH hF hS hE
    refine ⟨rfl, ?_, hno3, hres, hrowTN, hrowC, hrowSU⟩
    exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS2, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK, hLI,
      hfL, hfK, hclosL, hclosK, hdel, hclosJ⟩

theorem ggResMultiNodeRestTwoCellInput_e6Split_three
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L) :
    GGResMultiNodeRestTwoCellInput
      (fun p lab => p = 3 ∧ lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) := by
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE hP
  obtain ⟨hD, _, _, hL, _, _, _, hno3, hres, htwo, hC, hSU⟩ := hP
  haveI : Fact p.Prime := hfact
  have hp3 : p = 3 := by
    obtain ⟨lab, _, _, _, _, _, _, _, hmark⟩ :=
      largeEvenMarking_exists_hasLabel hL
    exact hmark.1.1
  have hLtor : GGInnerDiagOnLabel ggE6TorusLabel p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun _ h => Or.inl ⟨h.2.1, h.2.2⟩) hL
  have hDE6 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypLE6 :=
    hH.levi_typLE6_of_e6Torus_L (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds hLtor hD
  exact ggResLeaf_e6ExactTwo hB36 G p B Bs x L D J y K hH hF hS hE
    ⟨hp3, hDE6, hno3, hres, htwo, hC, hSU⟩

theorem ggResMultiNodeRestTwoCellInput_twE6Plus_three
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L) :
    GGResMultiNodeRestTwoCellInput
      (fun p lab => p = 3 ∧ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) := by
  intro G _ _ p B Bs x L D J y K hH hfact hF hS hE hP
  obtain ⟨hD, _, _, hL, _, _, _, hno3, hres, htwo, hC, hSU⟩ := hP
  haveI : Fact p.Prime := hfact
  have hp3 : p = 3 := by
    obtain ⟨lab, _, _, _, _, _, _, _, hmark⟩ :=
      largeEvenMarking_exists_hasLabel hL
    exact hmark.1.1
  subst hp3
  have hLtw : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun _ h => h.2) hL
  have hDE6 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypLE6 :=
    hH.levi_typLE6_of_twE6_qplus_L hLtw hD
  exact ggResLeaf_e6ExactTwo hB36 G 3 B Bs x L D J y K hH hF hS hE
    ⟨rfl, hDE6, hno3, hres, htwo, hC, hSU⟩

end CFSG.StandardType
