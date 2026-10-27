module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_known_data (hRig : GGLabelRigidInput) (hKG : GGE6DepBlockKnown) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) {K : Subgroup G} (hE : GGE6DepPerpCfg p Bs L K) :
    ∃ (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (R : Type) (_ : Group R)
      (I : Set (MulAut R)) (ψ : ↥L →* R), GGE6DepBlocks R I ∧
        GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range ∧
        Nat.card (ggGamma L hBsN).range = 3 ^ 5 := by
  classical
  obtain ⟨hp3, hcardBs, -, lab₀, hlab₀, hmarkL, -⟩ := hE
  rw [hp3] at hcfg
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  obtain ⟨lab, hlab, hhas, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ :=
    largeEvenMarking_exists_hasLabel hmarkL
  rw [hlab_eq] at hlab hhas
  have hM := ggInnerDiagOn_relabel hRig hinn hlab hhas
  obtain ⟨hL, lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = lab₀)
    (fun lab hlab hs => hKG lab (hs ▸ hlab₀) hlab)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hs, hBsN, h3⟩ := hP
  have hBl : GGE6DepBlocks R I := hP' hsimple hna
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb
  have hker : (ggGamma L hBsN).ker =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card (ggGamma L hBsN).ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hcfg.card_bstar_inf_centralizer_L
  have h1 : Nat.card (ggGamma L hBsN).range * 3 = 3 ^ 6 := by
    have h := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hkercard] at h
    rw [h, hcardBs]
  have hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5 := by
    have h2 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h2] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hBsN).range := le_of_eq hcard.symm
  have h33 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by rw [hcard]; norm_num
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hL θ hBsN hBsI hr h33
  exact ⟨hBsN, R, inferInstance, I, ggQuotHom θ, hBl, hTB, hcard⟩

end CFSG.StandardType

end
