module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH1
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveClassical
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJA2OfKGCent
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJA2PhanDOfEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem largeEvenInLambda2_A3 {t : LargeEvenLieTag} (ht : t = .A ∨ t = .twA) {f : ℕ}
    (hf : 1 ≤ f) : LargeEvenInLambda2 ⟨t, 3, f⟩ := by
  rcases ht with rfl | rfl <;> simp [LargeEvenInLambda2] <;> omega

theorem exists_label_A3_of_weylOfType
    (hcfg : GGConfig p B Bs x L D J) (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ f : ℕ, 1 ≤ f ∧
      ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
       (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))) := by
  rcases ggInnerDiagOnLabel_split (T := GGTBTorCov) (ggF4H1_original_marking hcfg hcard)
    with hres | htor
  · exact (ggF4H1_no_residual_label hcfg hT hcard hres (ggF4Small_card_A3 hA3)).elim
  · exact ggF4H1_toral_label hcfg htor hA3

theorem ggRealized_of_label_A3
    (hP : GGStdSubPrimeInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hp5 : 5 ≤ p) {t₀ : LargeEvenLieTag} (ht₀ : t₀ = .A ∨ t₀ = .twA)
    {f : ℕ} (hf : 2 ≤ f) (hlab : GGHasLabel ⟨t₀, 3, f⟩ (L ⧸ Subgroup.center L))
    {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer L Bs) (ht : GGIsReflection p t) :
    GGRealized p Bs t := by
  have hM : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGRealClassTag lab.tag) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => by
        obtain ⟨rfl, h2, h3⟩ := h
        refine ⟨⟨hf, ?_⟩, h2, h3⟩
        rcases ht₀ with rfl | rfl
        exacts [Or.inl rfl, Or.inr (Or.inl rfl)])
      (ggInnerDiagOn_relabel ggLabelRigidInput_holds hInn.1
        (largeEvenInLambda2_A3 ht₀ (by omega)) hlab)
  exact ggRealized_of_reflRealizedIn_L hP hcfg
    (ggReflRealizedQFourInputFiveClassical_holds ggLabelRigidInput_holds hraw hiso G p B Bs x L D
      J hcfg hInn hT hp5 L (Or.inl rfl) hM) htA ht

theorem exists_A2_pair_of_label_A3
    (hL : GGLBalanceInput) {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {f : ℕ} (hf : 2 ≤ f)
    (hlab : (p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
      (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))) :
    ∃ r₁ ∈ ggAutomizer J Bs, ∃ r₂ ∈ ggAutomizer J Bs,
      GGIsReflection p r₁ ∧ GGIsReflection p r₂ ∧ orderOf (r₁ * r₂) = 3 := by
  have hInn : GGInnerDiagOn Bs L := hR.1.2.2.1.1
  rcases hlab with ⟨hd, h⟩ | ⟨hd, h⟩
  · have hsplit : GGSplitLie p L := ggSplitLie_of_rowSA (GGConfig.tableB_facts hR.1.1).1
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hl => by
          obtain ⟨rfl, -⟩ := hl
          exact ⟨Or.inl ⟨rfl, le_rfl⟩, hd⟩)
        (ggInnerDiagOn_relabel ggLabelRigidInput_holds hInn
          (largeEvenInLambda2_A3 (Or.inl rfl) (by omega)) h))
    exact ggSecFiveJA2Input_of_lBalance hL G p B Bs x L D J 𝒦 (ggSecFiveRouteCfg'_of_routeCfg hR)
      hsplit
  · exact nsJA2_of_esuLabel ggSecFiveNSCornerInput_holds hR
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hl => by
          obtain ⟨rfl, h2, h3⟩ := hl
          exact ⟨⟨⟨Or.inl ⟨rfl, le_rfl⟩, hd⟩, fun h => by have h1 : f = 1 := h.1; omega⟩, h2, h3⟩)
        (ggInnerDiagOn_relabel ggLabelRigidInput_holds hInn
          (largeEvenInLambda2_A3 (Or.inr rfl) (by omega)) h))

end CFSG.StandardType

end
