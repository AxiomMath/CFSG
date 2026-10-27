module

public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGKGTag
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGTablePRow.eq_of_tag_BC {p : ℕ} {J X : LargeEvenLabel}
    (hBC : J.tag = .B ∨ J.tag = .C) (h : GGTablePRow p J X) :
    X = ⟨.C, J.rank + 1, J.n⟩ ∨ (J.rank = 3 ∧ X = ⟨.F4, 0, J.n⟩) := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨-, -, -, hX⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  all_goals first
    | exact hX
    | (exfalso
       rcases hBC with hB | hB <;> rw [hB] at h1 <;> simp at h1)
    | (exfalso
       have ht := congrArg LargeEvenLabel.tag h1
       rcases hBC with hB | hB <;> rw [hB] at ht <;> simp at ht)

theorem ggNbr_hasLabel_C_or_F4 (hTP : GGNbrTablePNbrInputOnL GGRegimeBCL)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} {m f : ℕ}
    (hcfg : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L) (hK : GGInnerDiagOn Bs K)
    (hnb : GGNbr p B x D J y K) (hm : 3 ≤ m) (hf : 1 ≤ f)
    (hlabL : GGHasLabel ⟨.C, m + 1, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hlabJ : GGHasLabel ⟨.C, m, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel ⟨.C, m + 1, f⟩ (↥K ⧸ Subgroup.center ↥K) ∨
      (m = 3 ∧ GGHasLabel ⟨.F4, 0, f⟩ (↥K ⧸ Subgroup.center ↥K)) := by
  have hΛJ : LargeEvenInLambda2 ⟨.C, m, f⟩ :=
    ⟨hf, show 2 ≤ m by omega, fun h => absurd (show m = 2 from h) (by omega)⟩
  have hΛL : LargeEvenInLambda2 ⟨.C, m + 1, f⟩ :=
    ⟨hf, show 2 ≤ m + 1 by omega, fun h => absurd (show m + 1 = 2 from h) (by omega)⟩
  obtain ⟨lab, hlab, hHas, -⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨labJ', labK', hΛJ', -, hrow, hJ', hK'⟩ :=
    hTP G p B Bs x L D J y K hcfg hL hK hnb ⟨.C, m + 1, f⟩ ⟨.C, m, f⟩ lab hΛL hΛJ hlab
      ⟨Or.inr rfl, hm, Or.inr rfl, rfl, rfl⟩ hlabL hlabJ hHas
  obtain ⟨hBC, hrk, hn⟩ := KG.kg_labelIso_C (hRig ⟨.C, m, f⟩ labJ' _ hΛJ hΛJ' hlabJ hJ')
  rcases hrow.eq_of_tag_BC hBC with hX | ⟨h3, hX⟩
  · left
    rwa [hX, hrk, hn] at hK'
  · right
    rw [hX, hn] at hK'
    exact ⟨by omega, hK'⟩


theorem card_ggAutomizer_of_hasLabel_F4 (hRig : GGLabelRigidInput)
    (hCP : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {f : ℕ} (hcfg : GGConfig 3 B Bs x L D J)
    (hNoTr : GGNoTransvection 3 Bs) (hK : GGInnerDiagOn Bs K) (hf : 3 ∣ 2 ^ f + 1)
    (hF4 : GGHasLabel ⟨.F4, 0, f⟩ (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(ggAutomizer K Bs) = 1152 := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · norm_num at hf
    · exact h
  refine card_ggAutomizer_of_f4Three hcfg hNoTr ?_
    (ggNbr_card_center_le_of_centerPCyclic hCP hcfg hK)
  refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hK ⟨hf1, rfl⟩ hF4)
  rintro lab R _ I F θ ⟨rfl, hN, hind⟩
  exact ⟨⟨rfl, rfl, hf⟩, hN, hind⟩

theorem ggNbr_hasLabel_C_of_le_bCoordinateBlock (hTP : GGNbrTablePNbrInputOnL GGRegimeBCL)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} {n : ℕ}
    (hcfg : GGConfig 3 B Bs x L D J) (hNoTr : GGNoTransvection 3 Bs) (hL : GGInnerDiagOn Bs L)
    (hK : GGInnerDiagOn Bs K) (hnb : GGNbr 3 B x D J y K) (hn : 5 ≤ n)
    (hlabL : GGHasLabel ⟨.C, n - 1, 1⟩ (↥L ⧸ Subgroup.center ↥L))
    (hlabJ : GGHasLabel ⟨.C, n - 2, 1⟩ (↥J ⧸ Subgroup.center ↥J))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {j : Fin n}
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bCoordinateBlock n 3 j) :
    GGHasLabel ⟨.C, n - 1, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
  have h1 : n - 1 = n - 2 + 1 := by omega
  rw [h1] at hlabL ⊢
  rcases ggNbr_hasLabel_C_or_F4 hTP hRig hcfg hL hK hnb (by omega) le_rfl hlabL hlabJ with
    h | ⟨h3, hF4⟩
  · exact h
  · have hle := Subgroup.card_le_of_le hAK
    rw [Subgroup.card_map_of_injective (MulAut.congr eta).injective,
      card_ggAutomizer_of_hasLabel_F4 hRig hCP hcfg hNoTr hK (by norm_num) hF4,
      card_bCoordinateBlock Nat.prime_three (by norm_num), show n = 5 by omega] at hle
    norm_num [Nat.factorial] at hle

end CFSG.StandardType
