module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowNSDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Cover

theorem ggNbrTableBWeylTypeSplitInput_of_families
    (hA : GGNbrTableBWeylTypeSplitOn fun _ lab => lab.tag = .A)
    (hBC : GGNbrTableBWeylTypeSplitOn fun _ lab => lab.tag = .B ∨ lab.tag = .C)
    (hD : GGNbrTableBWeylTypeSplitOn fun _ lab => lab.tag = .D)
    (hExc : GGNbrTableBWeylTypeSplitOn fun p lab => ¬ lab.tag = .A ∧ ¬ lab.tag = .B ∧
      ¬ lab.tag = .C ∧ ¬ lab.tag = .D ∧ ¬ (lab.tag = .E6 ∧ p = 3))
    (hE6 : GGNbrTableBWeylTypeSplitOn fun p lab => lab.tag = .E6 ∧ p = 3) :
    GGNbrTableBWeylTypeSplitInput := by
  intro p hp hp2 lab hlab _ hhs hsp
  by_cases hA' : lab.tag = .A
  · exact hA p hp hp2 lab hlab hA' hhs hsp
  by_cases hB : lab.tag = .B
  · exact hBC p hp hp2 lab hlab (Or.inl hB) hhs hsp
  by_cases hC : lab.tag = .C
  · exact hBC p hp hp2 lab hlab (Or.inr hC) hhs hsp
  by_cases hD' : lab.tag = .D
  · exact hD p hp hp2 lab hlab hD' hhs hsp
  by_cases hE : lab.tag = .E6 ∧ p = 3
  · exact hE6 p hp hp2 lab hlab hE hhs hsp
  exact hExc p hp hp2 lab hlab ⟨hA', hB, hC, hD', hE⟩ hhs hsp

end Cover

section Datum

variable {G : Type} [Group G] [Finite G]

theorem exists_weylTypeDatum_of_halfSplit (hTB : GGNbrTableBWeylTypeSplitInput)
    (hRig : GGLabelRigidInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {K : Subgroup G} (hInnK : GGInnerDiagOn Bs K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (r : ℕ),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) ∧
        GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hsplit⟩ := largeEvenMarking_exists_hasLabel hsp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hP : LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I :=
    hTB p hp hp2 lab hlab trivial (GGNbrSplitLabel.halfSplit hsplit) hsplit
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab)
    (P' := fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I)
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

theorem ggNbrWeylReflGroup_of_halfSplit (hTB : GGNbrTableBWeylTypeSplitInput)
    (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hsp : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  obtain ⟨R, _, θ, I, r, hBsI, hlift, hT⟩ :=
    exists_weylTypeDatum_of_halfSplit hTB hRig hcfg hInnK hsp hN
  exact ggWeylReflectionGroup_of_ggTorusWeylTypeW hcfg hNoTr hnb hInnK.1 θ hN hBsI hlift hT hZ

end Datum

section Cell

theorem ggSecFivePumpNbrNSSplitInput_of_weylType
    (hTB : GGNbrTableBWeylTypeSplitInput) (hRig : GGLabelRigidInput)
    (hZ : GGNbrBstarCenterInput) : GGSecFivePumpNbrNSSplitInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ y K hK _ hsp
  exact ggNbrWeylReflGroup_of_halfSplit hTB hRig hcfg.1.1 hcfg.1.2.2.2.1 hK
    (hcfg.1.2.2.1.2 y K hK) hsp (hZ G p B Bs x L D J hcfg.1 y K hK)

end Cell

end CFSG.StandardType

end
