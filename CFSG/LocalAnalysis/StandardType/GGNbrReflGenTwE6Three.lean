module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Open

section Core

variable {G : Type} [Group G] [Finite G]

theorem ggTorusTBGroup_of_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hr3 : 3 ≤ r)
    {X : Subgroup G} (hX : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hN).range) :
    GGTorusTBGroup p r R I X (ggQuotHom θ) (ggGamma X hN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma X hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := by
    have : IsMulCommutative ↥Bs := hBs.1
    exact fun a b => mul_comm' a b
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom X hN θ b l⟩
  have h3 : p ^ 3 ≤ Nat.card γ.range := le_trans (Nat.pow_le_pow_right hp.pos hr3) hr
  exact ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hX, hA, hAI, hr, h3,
    ggTorusSelfCent_ggGamma hN hSC⟩

theorem ggTorusTBGroup_of_nbr_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hr3 : 3 ≤ r)
    {y : G} {K : Subgroup G} (_hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) :
    GGTorusTBGroup p r R I K (ggQuotHom θ) (ggGamma K hN).range :=
  ggTorusTBGroup_of_card hcfg hr3 hK θ hN hBsI hr

theorem ggReflGenerated_of_ggTorusReflGenW_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hr3 : 3 ≤ r)
    (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK : commutator K = ⊤) {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    {I : Set (MulAut R)} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) (hT : GGTorusReflGenW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  exact ggReflGenerated_of_weylReflSet hp hp2 hBs hSC hNoTr hN hZ
    (hT K (ggQuotHom θ) (ggGamma K hN).range
      (ggTorusTBGroup_of_nbr_card hcfg hr3 hnb hK θ hN hBsI hr))

theorem exists_innerDiagDatum_of_labelAll (hRig : GGLabelRigidInput) {Bs K : Subgroup G}
    (hInnK : GGInnerDiagOn Bs K) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) {P : LargeEvenRawCont}
    (hP : LargeEvenLabelAll lab P) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R) (I F : Set (MulAut R)),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) ∧ P R I F := by
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab) (P' := P)
    (fun lab' _ h' => by rw [h']; exact hP)
    (fun lab' R _ I F θ hPmark => hPmark.1) hmark
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN', hind⟩, hPP⟩ := hPθ
  refine ⟨R, ‹Group R›, θ, I, F, ?_, hPP⟩
  intro b hb
  obtain ⟨φ, hφI, hindφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
  have hφeq : φ = ggLAut K θ ⟨b⁻¹⁻¹,
      (Subgroup.normalizer (K : Set G)).inv_mem (hN' (Bs.inv_mem hb))⟩ :=
    eq_ggLAut_of_induces K θ (hN' (Bs.inv_mem hb)) hindφ
  have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem
      (hN' (Bs.inv_mem hb))⟩ : Subgroup.normalizer (K : Set G)) = ⟨b, hN hb⟩ :=
    Subtype.ext (inv_inv b)
  rw [hφeq, hb_eq] at hφI
  exact hφI

theorem largeEvenSplit_of_twE6BadLabel {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTwE6BadLabel p lab) : LargeEvenSplit p lab := by
  obtain ⟨ht, rfl, hd⟩ := h
  exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, ht], by simp [ht], hd⟩)

theorem ggInnerDiagOnLab_of_twE6BadMarking (hRig : GGLabelRigidInput) {p : ℕ}
    {Bs K : Subgroup G} (hInnK : GGInnerDiagOn Bs K)
    (hbad : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGTwE6BadLabel p lab) :
    GGInnerDiagOnLab GGTwE6BadLabel p Bs K := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hbl⟩ := largeEvenMarking_exists_hasLabel hbad
  exact largeEvenMarking_mono (fun lab' _ _ _ _ _ hP => by
      obtain ⟨rfl, hN, hind⟩ := hP
      exact ⟨hbl, largeEvenSplit_of_twE6BadLabel hbl, hN, hind⟩)
    (ggInnerDiagOn_relabel hRig hInnK hlab hhas)

theorem ggNbrReflGen_of_twE6Three (hR : GGTwE6ThreeNbrRankInput) (hW : GGTwE6ThreeNbrWeylInput)
    (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hbad : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGTwE6BadLabel p lab)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hbl⟩ := largeEvenMarking_exists_hasLabel hbad
  have hp3 : p = 3 := hbl.2.1
  subst hp3
  have hInnL := ggInnerDiagOnLab_of_twE6BadMarking hRig hInnK hbad
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  have h5 := hR G 3 B Bs x L D J hcfg rfl y K hnb hInnL hN
    (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)
  obtain ⟨R, _, θ, I, F, hBsI, hWR⟩ :=
    exists_innerDiagDatum_of_labelAll hRig hInnK hlab hhas (hW lab hlab hbl) hN
  exact ggReflGenerated_of_ggTorusReflGenW_card hcfg (by norm_num) hNoTr hnb hInnK.1 θ hN hBsI
    h5 hWR hZ

end Core

theorem ggNbrReflGenNonSplitFull_of_rank (h : GGNbrReflGenNonSplitInput)
    (hR : GGTwE6ThreeNbrRankInput) (hW : GGTwE6ThreeNbrWeylInput) (hRig : GGLabelRigidInput)
    (hZ : GGNbrBstarCenterInput) : GGNbrReflGenNonSplitFull := by
  intro G _ _ p B Bs x L D J hRest y K hK hns hq
  have hDisj : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      (p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel p lab) ∨ GGTwE6BadLabel p lab) :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ hd => by
      by_cases hb : GGTwE6BadLabel p lab
      · exact Or.inr hb
      · exact Or.inl ⟨hd, hb⟩) hq
  rcases largeEvenMarking_or hDisj with hq' | hbad
  · exact h G p B Bs x L D J hRest y K hK hns hq'
  · exact ggNbrReflGen_of_twE6Three hR hW hRig hRest.1 hRest.2.2.2.1 hK
      (hRest.2.2.1.2 y K hK) hbad (hZ G p B Bs x L D J hRest y K hK)

section Input

theorem ggSecFiveTwE6ResidualInput_of_rank (hR : GGTwE6ThreeNbrRankInput)
    (hW : GGTwE6ThreeNbrWeylInput) (hRig : GGLabelRigidInput) (hZ : GGNbrBstarCenterInput) :
    GGSecFiveTwE6ResidualInput := by
  intro G _ _ p B Bs x L D J hRest _ ⟨y, K, hK, _, hbad, hnr⟩
  exact (hnr (ggNbrReflGen_of_twE6Three hR hW hRig hRest.1 hRest.2.2.2.1 hK
    (hRest.2.2.1.2 y K hK) hbad (hZ G p B Bs x L D J hRest y K hK))).elim

end Input

end CFSG.StandardType

end
