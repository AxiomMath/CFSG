module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42Plane
public import CFSG.Quasithin.Vol2.Asc94.He42Ident

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.A94.He42Plane

variable {G : Type} [Group G] [Finite G]

theorem HeSetup.typeL34_of
    (S : HeSetup G) (hB : S.BaseFacts) (hU : S.StepUniq)
    (hK : S.StepKer) (hperf : commutator ↥S.L = ⊤)
    (hcover : ∀ g ∈ S.L, ∃ h ∈ S.L1, ∃ m ∈ S.L2, ∃ h' ∈ S.L1, g = h * m * h') :
    Subgroup.center ↥S.L = S.B.subgroupOf S.L ∧
      CFSG.ComponentClassification.AS81.TypeL34 (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot S.L) := by
  have hL1le : S.L1 ≤ S.L := le_sup_left
  have hL2le : S.L2 ≤ S.L := le_sup_right
  have hBK : S.B ≤ S.K := hB.B_le_Z.trans (hB.Z_le_A.trans (hB.A_le_J.trans hB.J_le_K))
  have hBL1 : S.B ≤ S.L1 := hBK.trans hB.K_le_L1
  have hBL2 : S.B ≤ S.L2 := hBK.trans hB.K_le_L2
  have hBL : S.B ≤ S.L := hBL1.trans hL1le
  have hLcent : S.L ≤ Subgroup.centralizer (S.B : Set G) :=
    sup_le hB.L1_le_centralizer hB.L2_le_centralizer
  have hinf : S.L1.subgroupOf S.L ⊓ S.L2.subgroupOf S.L = S.K.subgroupOf S.L := by
    rw [← hB.L1_inf_L2]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have h5₁ : (S.L1.subgroupOf S.L ⊓ S.L2.subgroupOf S.L).relIndex (S.L1.subgroupOf S.L) = 5 := by
    rw [hinf, Subgroup.relIndex_subgroupOf hL1le]
    exact hB.relIndex_K_L1
  have h5₂ : (S.L1.subgroupOf S.L ⊓ S.L2.subgroupOf S.L).relIndex (S.L2.subgroupOf S.L) = 5 := by
    rw [hinf, Subgroup.relIndex_subgroupOf hL2le]
    exact hB.relIndex_K_L2
  have hcov' : ∀ g : ↥S.L, ∃ h ∈ S.L1.subgroupOf S.L, ∃ m ∈ S.L2.subgroupOf S.L,
      ∃ h' ∈ S.L1.subgroupOf S.L, g = h * m * h' := by
    intro g
    obtain ⟨h, hh, m, hm, h', hh', hg⟩ := hcover (g : G) g.2
    exact ⟨⟨h, hL1le hh⟩, Subgroup.mem_subgroupOf.2 hh, ⟨m, hL2le hm⟩,
      Subgroup.mem_subgroupOf.2 hm, ⟨h', hL1le hh'⟩, Subgroup.mem_subgroupOf.2 hh',
      Subtype.ext hg⟩
  have huniq' : ∀ h ∈ S.L1.subgroupOf S.L, ∀ g ∈ S.L2.subgroupOf S.L,
      g ∉ S.L1.subgroupOf S.L → ∀ l ∈ S.L1.subgroupOf S.L, ∀ m ∈ S.L2.subgroupOf S.L,
        g * l = h * m → h ∈ S.L2.subgroupOf S.L := by
    intro h hh g hg hgn l hl m hm hgl
    have hgl' : (g : G) * (l : G) = (h : G) * (m : G) := congrArg Subtype.val hgl
    have hgn' : (g : G) ∉ S.L1 := fun h' => hgn (Subgroup.mem_subgroupOf.2 h')
    exact Subgroup.mem_subgroupOf.2 (hU (h : G) (Subgroup.mem_subgroupOf.1 hh) (g : G)
      (Subgroup.mem_subgroupOf.1 hg) hgn' (l : G) (Subgroup.mem_subgroupOf.1 hl) (m : G)
      (Subgroup.mem_subgroupOf.1 hm) hgl')
  have hplane := CFSG.Quasithin.A94.He42Plane.isSteinerPlane_lineSet h5₁ h5₂ hcov' huniq'
  have hBcard : Nat.card (S.B.subgroupOf S.L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB.card_B]
  have hL₁card : Nat.card (S.L1.subgroupOf S.L) = 3840 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1le).toEquiv, hB.card_L1]
  have hBKs : S.B.subgroupOf S.L ≤ S.L1.subgroupOf S.L ⊓ S.L2.subgroupOf S.L := by
    intro b hb
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (hBL1 (Subgroup.mem_subgroupOf.1 hb)),
      Subgroup.mem_subgroupOf.2 (hBL2 (Subgroup.mem_subgroupOf.1 hb))⟩
  have hBcent : ∀ b ∈ S.B.subgroupOf S.L, ∀ g : ↥S.L, b * g = g * b := by
    intro b hb g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hLcent g.2) (b : G) (Subgroup.mem_subgroupOf.1 hb)
  have hker : ∀ g : ↥S.L, (∀ p : ↥S.L ⧸ S.L1.subgroupOf S.L, g • p = p) →
      g ∈ S.B.subgroupOf S.L := by
    intro g hg
    refine Subgroup.mem_subgroupOf.2 (hK (g : G) g.2 ?_)
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y : ↥S.L, (y : G) = x := ⟨⟨x, hx⟩, rfl⟩
    have hfix : (QuotientGroup.mk (g * y) : ↥S.L ⧸ S.L1.subgroupOf S.L) = QuotientGroup.mk y :=
      hg (QuotientGroup.mk y)
    have h2 : (g * y)⁻¹ * y ∈ S.L1.subgroupOf S.L := QuotientGroup.eq.1 hfix
    have h3 : ((g : G) * (y : G))⁻¹ * (y : G) ∈ S.L1 := Subgroup.mem_subgroupOf.1 h2
    have e : (y : G)⁻¹ * (g : G) * (y : G) = (((g : G) * (y : G))⁻¹ * (y : G))⁻¹ := by group
    rw [e]
    exact S.L1.inv_mem h3
  exact CFSG.Quasithin.A94.He42Ident.typeL34_of_plane (S.L1.subgroupOf S.L)
    (S.L2.subgroupOf S.L) (S.B.subgroupOf S.L) hplane hBcard hL₁card hBKs hBcent hker hperf

end CFSG.Quasithin.A94.He42
