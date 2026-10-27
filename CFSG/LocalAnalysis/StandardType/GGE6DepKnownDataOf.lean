module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_known_data_model_of (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hcardBs : Nat.card Bs = 3 ^ 6) {lab₀ : LargeEvenLabel} (hlab₀ : GGE6DepLabel lab₀)
    (hmark : LargeEvenMarking X (fun lab _ _ _ _ _ => lab = lab₀)) (hinn : GGInnerDiagOn Bs X)
    (hker : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3) :
    ∃ (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (R : Type) (_ : Group R)
      (I : Set (MulAut R)) (ψ : ↥X →* R),
        GGTorusTBGroup 3 5 R I ↥X ψ (ggGamma X hBsN).range ∧
        Nat.card (ggGamma X hBsN).range = 3 ^ 5 ∧
        GGE6ThreeWeylModel ψ.ker (ggGamma X hBsN).range := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨lab, hlab, hhas, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  rw [hlab_eq] at hlab hhas
  have hMk := ggInnerDiagOn_relabel hRig hinn hlab hhas
  obtain ⟨hL, lab', hlab', hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = lab₀)
    (fun lab hlab hs => hM lab (hs ▸ hlab₀) hlab)
    (fun _ _ _ _ _ _ hP => hP.1) hMk
  obtain ⟨R, _, I, F, hsimple, hna, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hs, hBsN, h3⟩ := hP
  have hMod : GGE6DepModelProp R I := hP' hsimple hna
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3 hb
  have hkerγ : (ggGamma X hBsN).ker =
      (Bs ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hkercard : Nat.card (ggGamma X hBsN).ker = 3 := by
    rw [hkerγ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hker
  have h1 : Nat.card (ggGamma X hBsN).range * 3 = 3 ^ 6 := by
    have h := TableB.card_range_mul_card_ker (ggGamma X hBsN)
    rw [hkercard] at h
    rw [h, hcardBs]
  have hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5 := by
    have h2 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
    rw [h2] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma X hBsN).range := le_of_eq hcard.symm
  have h33 : 3 ^ 3 ≤ Nat.card (ggGamma X hBsN).range := by rw [hcard]; norm_num
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hL θ hBsN hBsI hr h33
  exact ⟨hBsN, R, inferInstance, I, ggQuotHom θ, hTB, hcard,
    hMod ↥X (ggQuotHom θ) (ggGamma X hBsN).range hTB hcard⟩

end CFSG.StandardType

end
