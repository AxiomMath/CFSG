module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownData
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_known_data_zl_of_marking (hRig : GGLabelRigidInput) (hZL : GGE6DepZLKnown) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) (hp3 : p = 3) (hcardBs : Nat.card Bs = 3 ^ 6)
    (hmarkL : LargeEvenMarking L (fun lab _ _ _ _ _ => GGE6DepLabel lab)) :
    ∃ (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (R : Type) (_ : Group R)
      (I : Set (MulAut R)) (ψ : ↥L →* R)
      (Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥L)
      (w : Fin 6 → ↥L),
        GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range ∧
        Nat.card (ggGamma L hBsN).range = 3 ^ 5 ∧ Subgroup.center ↥L ≤ ψ.ker ∧
        GGE6ThreeWeylModelWith ψ.ker (ggGamma L hBsN).range Φ T w ∧
        ∀ z ∈ ψ.ker, orderOf z = 3 → z ∈ ggE6WeylCobdry (ggGamma L hBsN).range w := by
  classical
  subst hp3
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  obtain ⟨lab, hlab, hhas, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ :=
    largeEvenMarking_exists_hasLabel hmarkL
  let lab₀ := lab
  have hlab₀ : GGE6DepLabel lab₀ := hlab_eq
  have hMk := ggInnerDiagOn_relabel hRig hinn hlab hhas
  obtain ⟨hL, lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = lab₀) (fun lab hlab hs => hZL lab (hs ▸ hlab₀) hlab)
    (fun _ _ _ _ _ _ hP => hP.1) hMk
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hs, hBsN, h3⟩ := hP
  have hMod : GGE6DepZLProp R I := hP' hsimple hna
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
  obtain ⟨Φ, T, w, hmodel, hcob⟩ := hMod ↥L (ggQuotHom θ) (ggGamma L hBsN).range hTB hcard
  exact ⟨hBsN, R, inferInstance, I, ggQuotHom θ, Φ, T, w, hTB, hcard,
    (ker_ggQuotHom θ).ge, hmodel, hcob⟩


theorem ggE6Dep_known_data_zl (hRig : GGLabelRigidInput) (hZL : GGE6DepZLKnown) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) {K : Subgroup G} (hE : GGE6DepPerpCfg p Bs L K) :
    ∃ (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (R : Type) (_ : Group R)
      (I : Set (MulAut R)) (ψ : ↥L →* R)
      (Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup ↥L)
      (w : Fin 6 → ↥L),
        GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range ∧
        Nat.card (ggGamma L hBsN).range = 3 ^ 5 ∧ Subgroup.center ↥L ≤ ψ.ker ∧
        GGE6ThreeWeylModelWith ψ.ker (ggGamma L hBsN).range Φ T w ∧
        ∀ z ∈ ψ.ker, orderOf z = 3 → z ∈ ggE6WeylCobdry (ggGamma L hBsN).range w := by
  obtain ⟨hp3, hcardBs, _, lab, hlabel, hmark, _⟩ := hE
  exact ggE6Dep_known_data_zl_of_marking hRig hZL hcfg hinn hp3 hcardBs
    (largeEvenMarking_mono (P := fun lab' _ _ _ _ _ => lab' = lab)
      (fun _ _ _ _ _ _ heq => heq ▸ hlabel) hmark)

end CFSG.StandardType

end
