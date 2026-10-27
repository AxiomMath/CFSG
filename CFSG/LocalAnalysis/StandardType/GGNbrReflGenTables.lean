module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggHalfSplit_dvd_of_marking (hRig : GGLabelRigidInput) {X : Type} [Group X] {p : ℕ}
    {c : Prop} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X)) (hHS : LargeEvenHalfSplit p lab c)
    (hq : LargeEvenMarking X fun lab' _ _ _ _ _ => p ∣ (2 ^ lab'.n) ^ 2 - 1) :
    p ∣ (2 ^ lab.n) ^ 2 - 1 := by
  rcases largeEvenHalfSplit_dvd hlab hHS with h | ⟨rfl, hex⟩
  · exact h
  · obtain ⟨labq, hlq, hhq, R, _, I, F, θ, hpq⟩ := largeEvenMarking_exists_hasLabel hq
    have hiso : GGLabelIso labq lab :=
      hRig labq lab (X ⧸ Subgroup.center X) hlq hlab hhq hhas
    have hlabq : labq = lab := eq_of_ggLabelIso_of_exc hex hiso
    rw [hlabq] at hpq
    rcases hex with rfl | rfl <;> exact hpq

variable {G : Type} [Group G] [Finite G]

@[expose] def GGNbrBstarCenterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p

theorem exists_weylDatum_of_halfSplit (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {K : Subgroup G} (hInnK : GGInnerDiagOn Bs K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (r : ℕ),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) ∧
        GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hsplit⟩ := largeEvenMarking_exists_hasLabel hsp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hP : LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I :=
    hTB p hp hp2 lab hlab (GGNbrSplitLabel.halfSplit hsplit) hsplit
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab)
    (P' := fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I)
    (fun lab' _ h' => by rw [h']; exact hP)
    (fun lab' R _ I F θ hPmark => hPmark.1) hmark
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN', hind⟩, r, hlift, hT⟩ := hPθ
  refine ⟨R, ‹Group R›, θ, I, r, ?_, hlift, hT⟩
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

theorem ggNbrReflGen_of_halfSplit (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, r, hBsI, hlift, hT⟩ :=
    exists_weylDatum_of_halfSplit hTB hRig hcfg hInnK hsp hN
  exact ggReflGenerated_of_ggTorusReflGenW hcfg hNoTr hnb hInnK.1 θ hN hBsI hlift hT hZ

theorem ggNbr_halfSplit_of_secFiveRest (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) :
    LargeEvenMarking ↥K fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) := by
  have hcfg : GGConfig p B Bs x L D J := h.1
  have hInnK : GGInnerDiagOn Bs K := h.2.2.1.2 y K hK
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hK.1, D, J, hcfg.2.2, hK.2⟩).2
  rcases largeEvenMarking_or h5 with hh | hh
  · exact hh
  · exact absurd hh (ggNbr_not_primeField hraw hiso hp hp2 hxBs hInnK)

theorem ggNbrReflGen_of_tableB (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    (hZ : GGNbrBstarCenterInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) :
    GGReflGenerated p (ggAutomizer K Bs) :=
  ggNbrReflGen_of_halfSplit hTB hRig h.1 h.2.2.2.1 hK (h.2.2.1.2 y K hK) hsp
    (hZ G p B Bs x L D J h y K hK)

theorem existsUnique_overGamma_of_tableB (hTB : GGNbrTableBWeylInput) (hRig : GGLabelRigidInput)
    (hZ : GGNbrBstarCenterInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∀ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      ∃! c : MulAut ↥Bs, c ∈ ggAutomizer K Bs ∧ GGOverGamma hN c a := by
  have hInnK : GGInnerDiagOn Bs K := h.2.2.1.2 y K hK
  obtain ⟨R, _, θ, I, r, hBsI, hlift, hT⟩ :=
    exists_weylDatum_of_halfSplit hTB hRig h.1 hInnK hsp hN
  exact existsUnique_overGamma_of_ggTorusReflGenW h.1 h.2.2.2.1 hK hInnK.1 θ hN hBsI hlift hT
    (hZ G p B Bs x L D J h y K hK)

end CFSG.StandardType

end
