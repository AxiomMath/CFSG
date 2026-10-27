module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoSideTypes
public import CFSG.LocalAnalysis.StandardType.GGResQTwoA2Endpoint
public import CFSG.LocalAnalysis.StandardType.GGResQTwoBTwoEndpoint
public import CFSG.LocalAnalysis.StandardType.GGResQTwoGOForm
public import CFSG.LocalAnalysis.StandardType.GGResQTwoTits
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
public import CFSG.LocalAnalysis.StandardType.GGResQTwoFamily
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R

public section

namespace CFSG.StandardType

open CFSG.Assembly

noncomputable section

set_option autoImplicit false

theorem ggResQTwo_cardBs_of_fin3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hH : GGResHyp 3 B Bs x L D J y K) (hFix : GGTBFixInput)
    (e : Fin 3 ≃ Λ)
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hsel : LinearIndependent (ZMod 3) h) :
    Nat.card Bs = 81 := by
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  have hspan := ggResI_span_top hFix hH ι hφ hAL hsel
  have hcardΛ : Fintype.card Λ = 3 := by
    simpa using (Fintype.card_congr e).symm
  have hdim : Module.finrank (ZMod 3) V = 4 := by
    rw [ggResI_finrank hspan hsel, hcardΛ]
  have hV : Nat.card V = 3 ^ 4 := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 V, hdim]
  calc
    Nat.card Bs = Nat.card V := card_eq_of_ggLin ι
    _ = 81 := by rw [hV]; norm_num

theorem GGResLeviDatumCell.exists_residualTag
    {G : Type} [Group G] [Finite G] {Bs L J K : Subgroup G}
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell) :
    ∃ tag, GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      (GGResQTwoResidualCellTag tag) := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hselI, hfL, hfK, hAL, hAK, hdel, hJ,
    hcell⟩ := hD
  obtain ⟨tag, hcellTag⟩ := GGResQTwoResidualCell.exists_tag hcell
  exact ⟨tag, Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hselI, hfL, hfK, hAL, hAK, hdel, hJ,
    hcellTag⟩

theorem GGResLeviDatumCell.cardBs_of_residualTag
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {tag : GGResQTwoResidual}
    (hH : GGResHyp 3 B Bs x L D J y K) (hFix : GGTBFixInput)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      (GGResQTwoResidualCellTag tag)) :
    Nat.card Bs = 81 := by
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    -, -, -, -, -, hφ, -, hL, hK, hselI, hfL, hfK, hAL, hAK, -, hJ,
    hcell⟩ := hD
  obtain ⟨n, C, ib, ic, e₁, e₂, e, hCe, hib, hrow, hcol, hCKaa, hshape⟩ := hcell
  have hn : n = 3 := ggResQTwoResidualShape_n_eq_three tag n C ib ic e₁ e₂ _ _ hshape
  subst hn
  have hsel : LinearIndependent (ZMod 3) h := by simpa [ggSelI] using hselI
  exact ggResQTwo_cardBs_of_fin3 hH hFix e hφ hAL hsel

theorem GGResLeviDatumCell.cardBs_of_residual
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hFix : GGTBFixInput)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell) :
    Nat.card Bs = 81 := by
  obtain ⟨tag, hDtag⟩ :=
    GGResLeviDatumCell.exists_residualTag (G := G) (Bs := Bs) (L := L) (J := J) (K := K) hD
  exact GGResLeviDatumCell.cardBs_of_residualTag (G := G) (B := B) (Bs := Bs) (x := x)
    (L := L) (D := D) (J := J) (y := y) (K := K) (tag := tag) hH hFix hDtag

theorem ggResQTwo_hasLabel_of_linearMarking
    {L : Type} [Group L] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (hmark : LargeEvenMarking L
      (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) :
    GGHasLabel ⟨.A, n, 1⟩ (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, -, hhas, R, _, I, F, θ, hQ⟩ := largeEvenMarking_exists_hasLabel hmark
  have hEq : lab = ⟨.A, n, 1⟩ := by
    rcases lab with ⟨tag, rank, exp⟩
    rcases hQ with ⟨rfl, rfl, rfl⟩
    rfl
  simpa [hEq] using hhas

theorem ggResQTwo_goShape_of_linearMarking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {n : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K) (hFix : GGTBFixInput)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell)
    (hn : n = 5 ∨ n = 6)
    (hmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) :
    GGResGOFourShape 3 Bs L K := by
  refine ⟨rfl, ?_, ggResQTwoGOForm hH hFix hD⟩
  rcases hn with rfl | rfl
  · exact Or.inl (ggResQTwo_hasLabel_of_linearMarking (n := 5) (Or.inl rfl) hmark)
  · exact Or.inr (ggResQTwo_hasLabel_of_linearMarking (n := 6) (Or.inr rfl) hmark)

theorem ggResQTwo_tits_dispatch
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hFix : GGTBFixInput)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hnotSp6 : ¬ GGInnerDiagOnLabel GGLabSp6 3 Bs L) :
    (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
      LargeEvenMarking ↥L
        (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) := by
  have hcard81 : Nat.card Bs = 81 :=
    GGResLeviDatumCell.cardBs_of_residual hH hFix hD
  have hcard : Nat.card Bs = 3 ^ 4 := by
    rw [hcard81]
    norm_num
  have h3A : 3 ∣ Nat.card (ggAutomizer L Bs) :=
    ggResQTwo_actual_residual_h3A hD
  rcases ggQTwoEnds_of_card_bstar_of_noTransvection_three hH.1 hcard hq hH.2.2.2.1 h3A with
    hsp | hlin | homega
  · exact absurd hsp hnotSp6
  · exact Or.inl hlin
  · exact Or.inr homega

theorem ggResQTwo_omega_endpoint
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {tag : GGResQTwoResidual}
    (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      (GGResQTwoResidualCellTag tag))
    (hLmark : LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1))
    (hFix : GGTBFixInput) :
    False := by
  by_cases hB2 : tag = .B3b0c2 ∨ tag = .C3b0c2
  · exact ggResQTwoBTwoOmegaEndpoint hLB hRig hH
      (GGResLeviDatumCell.cardBs_of_residualTag hH hFix hD) hB2 hD hLmark hFix
  · have hB2' : tag ≠ .B3b0c2 ∧ tag ≠ .C3b0c2 := by
      simpa only [not_or] using hB2
    exact ggResQTwoA2Endpoint hH hD hLmark hB2'.1 hB2'.2

theorem ggResCaseIQTwoRestInput_holds
    :
    GGResCaseIQTwoRestInput := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hFix : GGTBFixInput := ggTBFixInput_holds
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨hLD, hq, hnotGO⟩ := hP
  have hp : p = 3 := FrameRoute.p_eq_three_of_qTwo hH.1 hq
  subst hp
  rcases ggResQTwo_actual_family_of_holds hH hLD hFork hStd hE6 hq hFix with
    hcell | hWeyl
  · obtain ⟨tag, hDtag⟩ :=
      GGResLeviDatumCell.exists_residualTag (G := G) (Bs := Bs) (L := L) (J := J) (K := K)
        hcell
    have hnotSp6 : ¬ GGInnerDiagOnLabel GGLabSp6 3 Bs L :=
      not_ggInnerDiagOnLabel_sp6 hH.1
    rcases ggResQTwo_tits_dispatch hH hFix hcell hq hnotSp6 with
      ⟨n, hn, hmark⟩ | homega
    · exact (hnotGO (ggResQTwo_goShape_of_linearMarking hH hFix hcell hn hmark)).elim
    · exact (ggResQTwo_omega_endpoint hLB hRig hH hDtag homega hFix).elim
  · exact hWeyl

end

end CFSG.StandardType

end
