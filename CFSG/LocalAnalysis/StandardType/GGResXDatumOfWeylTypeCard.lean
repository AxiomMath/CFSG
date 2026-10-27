module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylType
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGWeylTypeRankFamilyOn (r : ℕ) (T : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → T p lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW p r R I

@[expose] def GGRankLOn (r : ℕ) (T : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G), GGConfig p B Bs x L D J → GGNoTransvection p Bs →
      GGInnerDiagOnLabel T p Bs L → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
        p ^ r ≤ Nat.card (ggGamma L hN).range

@[expose] def GGRankNbrOn (r : ℕ) (T : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G), GGConfig p B Bs x L D J → GGNoTransvection p Bs →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel T p Bs K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), p ^ r ≤ Nat.card (ggGamma K hN).range

theorem ggResXDatum_nbr_of_weylTypeCard (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    (hr3 : 3 ≤ r) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (hP : LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW p r R I)
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), p ^ r ≤ Nat.card (ggGamma K hN).range) :
    GGResXDatum p Bs K := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := GGInnerDiagOn.le_normalizer hInnK
  have hZ := ggNbr_card_center_le_of_centerPCyclic hcyc hcfg hInnK
  obtain ⟨R, _, θ, I, F, hBsI, hT⟩ := exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas hP hN
  obtain ⟨hW, hG2⟩ := ggWeylReflectionGroup_of_ggTorusWeylTypeW_card hcfg hr3 hNoTr hnb hInnK.1 θ
    hN hBsI (hr hN) hT hZ
  exact ggResXDatum_of_weylReflectionGroup hp2 hBs hNoTr hW hG2

theorem ggResXDatum_L_of_weylTypeCard (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] (hr3 : 3 ≤ r) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hInnL : GGInnerDiagOn Bs L) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (hP : LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW p r R I)
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), p ^ r ≤ Nat.card (ggGamma L hN).range) :
    GGResXDatum p Bs L := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hInnL
  obtain ⟨R, _, θ, I, F, hBsI, hT⟩ := exists_innerDiagDatum_of_labelAll hRig hInnL hlab hhas hP hN
  have hTB := ggTorusTBGroup_of_card hcfg hr3 hInnL.1 θ hN hBsI (hr hN)
  obtain ⟨hW, hG2⟩ := ggWeylReflectionGroup_of_ggTorusWeylTypeW_TB hcfg hNoTr θ hN hTB hT
    (card_bstar_inf_center_le hcfg)
  exact ggResXDatum_of_weylReflectionGroup hp2 hBs hNoTr hW hG2

theorem ggResXDatum_nbr_of_weylTypeCardOn {r : ℕ} {T : ℕ → LargeEvenLabel → Prop}
    (hF : GGWeylTypeRankFamilyOn r T) (hr3 : 3 ≤ r) (hrK : GGRankNbrOn r T)
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hnb : GGNbr p B x D J y K) (hK : GGInnerDiagOnLabel T p Bs K) : GGResXDatum p Bs K := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hT, -⟩ := largeEvenMarking_exists_hasLabel hK
  have hInnK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hK
  exact ggResXDatum_nbr_of_weylTypeCard hRig hcyc hr3 hcfg hNoTr hnb hInnK hlab hhas
    (hF p Fact.out hp2 lab hlab hT) (hrK G p B Bs x L D J hcfg hNoTr y K hnb hK)

theorem ggResXDatum_L_of_weylTypeCardOn {r : ℕ} {T : ℕ → LargeEvenLabel → Prop}
    (hF : GGWeylTypeRankFamilyOn r T) (hr3 : 3 ≤ r) (hrL : GGRankLOn r T)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hL : GGInnerDiagOnLabel T p Bs L) :
    GGResXDatum p Bs L := by
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hT, -⟩ := largeEvenMarking_exists_hasLabel hL
  have hInnL : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hL
  exact ggResXDatum_L_of_weylTypeCard hRig hr3 hcfg hNoTr hInnL hlab hhas
    (hF p Fact.out hp2 lab hlab hT) (hrL G p B Bs x L D J hcfg hNoTr hL)

theorem ggTBXDatumResOn_of_weylTypeCard {r : ℕ} {S T : ℕ → LargeEvenLabel → Prop}
    (hF : GGWeylTypeRankFamilyOn r T) (hr3 : 3 ≤ r) (hrL : GGRankLOn r T)
    (hrK : GGRankNbrOn r T) (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (h : GGTBXDatumResOn (fun p lab => S p lab ∧ ¬ T p lab)) : GGTBXDatumResOn S := by
  intro G _ _ p B Bs x L D J y K hH _
  refine ⟨fun hL => ?_, fun hK => ?_⟩
  · rcases ggInnerDiagOnLabel_split (T := T) hL with h1 | h2
    · exact (h G p B Bs x L D J y K hH).1 h1
    · exact ggResXDatum_L_of_weylTypeCardOn hF hr3 hrL hRig hH.1 hH.2.2.2.1 h2
  · rcases ggInnerDiagOnLabel_split (T := T) hK with h1 | h2
    · exact (h G p B Bs x L D J y K hH).2 h1
    · exact ggResXDatum_nbr_of_weylTypeCardOn hF hr3 hrK hRig hcyc hH.1 hH.2.2.2.1 hH.2.2.2.2.1 h2

theorem ggPZNbrResDatumOn_of_weylTypeCard {r : ℕ} {S T : ℕ → LargeEvenLabel → Prop}
    (hF : GGWeylTypeRankFamilyOn r T) (hr3 : 3 ≤ r) (hrK : GGRankNbrOn r T)
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ T p lab)) : GGPZNbrResDatumOn S := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb hMark
  rcases ggInnerDiagOnLabel_split (T := T) hMark with h1 | h2
  · exact h G p B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBsY hnb h1
  · exact (ggResXDatum_nbr_of_weylTypeCardOn hF hr3 hrK hRig hcyc hprem.1.1 hprem.1.2.2.2.1 hnb
      h2).toSurj

end CFSG.StandardType

end
