module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralCoverInnerWitness
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralInvolutionHullInjectivity
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.AmbientOddCenterQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G]

theorem elementary_hull_not_normal_of_quasisimple (U : Subgroup G)
    (hUel : IsElemAbelian 2 U)
    (hquasi : IsQuasisimple (Subgroup.normalClosure (U : Set G))) : ¬ U.Normal := by
  let L := Subgroup.normalClosure (U : Set G)
  let : Group.IsPerfect L := ⟨hquasi.1⟩
  let : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hquasi
  intro hn
  let : U.Normal := hn
  have hcomm : IsMulCommutative L := by
    change IsMulCommutative (Subgroup.normalClosure (U : Set G))
    rw [Subgroup.normalClosure_eq_self U]
    exact hUel.1
  exact Group.IsPerfect.not_isMulCommutative L hcomm

theorem ambient_odd_center_eq_center_of_quotient_center_eq_bot
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (hbot : Subgroup.center
      (L.map (QuotientGroup.mk' (ambientOddCenter L))) = ⊥) :
    Subgroup.center L = oddCenterSubgroup L := by
  apply le_antisymm
  · have hmap := (ambientOddCenter_center_image L).trans hbot
    have hle := (Subgroup.center L).map_eq_bot_iff.mp hmap
    rwa [ambientOddCenter_restriction_kernel] at hle
  · exact oddCenterSubgroup_le_center L

theorem ambient_odd_center_odd_center_of_quotient_center_eq_bot [Finite G]
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (hbot : Subgroup.center
      (L.map (QuotientGroup.mk' (ambientOddCenter L))) = ⊥) :
    Odd (Nat.card (Subgroup.center L)) := by
  rw [ambient_odd_center_eq_center_of_quotient_center_eq_bot L hbot]
  exact oddCenterSubgroup_odd_card L

theorem central_involution_ti_hull_odd_quotient_witness [Finite G]
    (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (himage : IsQuasisimple
      ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))))
    (hmodel : fusionIsBenderGroup
      (((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))) ⧸
        Subgroup.center ((Subgroup.normalClosure (U : Set G)).map
          (QuotientGroup.mk' (centralLiftKernel x))))) :
    let L := Subgroup.normalClosure (U : Set G)
    let q := QuotientGroup.mk' (ambientOddCenter L)
    let L₁ := L.map q
    let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
    L₁.Normal ∧ Group.IsPerfect L₁ ∧ IsQuasisimple L₁ ∧
      IsPGroup 2 (Subgroup.center L₁) ∧
      fusionIsBenderGroup (L₁ ⧸ Subgroup.center L₁) ∧
      ∃ w : L₁, orderOf w = 2 ∧ (w : G ⧸ ambientOddCenter L) ∈ U.map q ∧
        (∃ hwT : (w : G ⧸ ambientOddCenter L) ∈
            (T₁ : Subgroup (G ⧸ ambientOddCenter L)),
          (⟨(w : G ⧸ ambientOddCenter L), hwT⟩ :
            (T₁ : Subgroup (G ⧸ ambientOddCenter L))) ∈
              Subgroup.center (T₁ : Subgroup (G ⧸ ambientOddCenter L))) ∧
        w ∉ Subgroup.center L₁ := by
  let L := Subgroup.normalClosure (U : Set G)
  let q := QuotientGroup.mk' (ambientOddCenter L)
  let L₁ := L.map q
  have hstructure := central_involution_hull_structure T U hUT hUel hcard
    hclosed hTI x horder himage hmodel
  let : Group.IsPerfect L := hstructure.2.1
  have hquasi : IsQuasisimple L := hstructure.2.2.1
  have hmodelL : fusionIsBenderGroup (L ⧸ Subgroup.center L) :=
    hstructure.2.2.2.2.2.2
  have hnormal : ¬ U.Normal := elementary_hull_not_normal_of_quasisimple U hUel hquasi
  have hU : U ≠ ⊥ := by
    intro hbot
    simp [hbot] at hcard
  obtain ⟨w, _, _, hworder, hwU, hwL, hwT, hwnoncentral⟩ :=
    ambient_odd_center_ti_hull_witness T U hUT hU hUel hclosed hTI hnormal
      inferInstance hquasi
  have hdata := ambient_odd_center_hull_structure L hquasi hmodelL
  refine ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2,
    ⟨q w, hwL⟩, ?_, hwU, hwT, ?_⟩
  · simpa only [Subgroup.orderOf_mk] using hworder
  · intro hwcenter
    exact hwnoncentral (Subgroup.mem_map.mpr ⟨⟨q w, hwL⟩, hwcenter, rfl⟩)

theorem rank_one_center_two_inner_sylow_witness_eq_bot [Finite G]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (hp : IsPGroup 2 (Subgroup.center L))
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L))
    (w : L) (hwT : (w : G) ∈ (T : Subgroup G))
    (hwcenter : (⟨(w : G), hwT⟩ : (T : Subgroup G)) ∈
      Subgroup.center (T : Subgroup G)) (hwnoncentral : w ∉ Subgroup.center L) :
    Subgroup.center L = ⊥ := by
  rcases hmodel with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · let F := GaloisField 2 f
    have hcard : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
    let eJ := e.trans (glaSL2EquivNative f hf hcard).symm
    let η := eJ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hker : η.ker = Subgroup.center L := by
      rw [MonoidHom.ker_comp_of_injective _ _ eJ.injective, QuotientGroup.ker_mk']
    have hbot := even_linear_cover_inner_sylow_witness_kernel_eq_bot T L f hf hcard
      η (eJ.surjective.comp (QuotientGroup.mk'_surjective _))
      (hker.symm ▸ le_refl _) (hker.symm ▸ hp) w hwT hwcenter hwnoncentral
    exact hker.symm.trans hbot
  · exact (unitaryCover_native_center_quotient_full f hf hp e).1
  · let η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hker : η.ker = Subgroup.center L := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    have hbot : η.ker = ⊥ := by
      apply normal_inner_sylow_witness_kernel_eq_bot T L η (hker.symm ▸ le_refl _)
        (w := w) (hwT := hwT) (hwcenter := hwcenter) (hwnoncentral := hwnoncentral)
      intro hne P
      exact le_of_eq ((suzukiCover_native_nontrivial_Sylow_centralizer a ha η
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
        (hker.symm ▸ le_refl _) (hker.symm ▸ hp) hne).1 P)
    exact hker.symm.trans hbot

theorem central_involution_hull_lifting [Finite G] (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (himage : IsQuasisimple
      ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))))
    (hmodel : fusionIsBenderGroup
      (((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))) ⧸
        Subgroup.center ((Subgroup.normalClosure (U : Set G)).map
          (QuotientGroup.mk' (centralLiftKernel x))))) :
    let L := Subgroup.normalClosure (U : Set G)
    let π := QuotientGroup.mk' (centralLiftKernel x)
    IsQuasisimple L ∧ Odd (Nat.card (Subgroup.center L)) ∧
      fusionIsBenderGroup (L ⧸ Subgroup.center L) ∧
      L ⊓ centralLiftKernel x = ⊥ ∧
      ∃ e : L ≃* L.map π, ∀ a : L, (e a : G ⧸ centralLiftKernel x) = π (a : G) := by
  let L := Subgroup.normalClosure (U : Set G)
  let q := QuotientGroup.mk' (ambientOddCenter L)
  let L₁ := L.map q
  let T₁ := T.mapSurjective (QuotientGroup.mk'_surjective (ambientOddCenter L))
  have hstructure := central_involution_hull_structure T U hUT hUel hcard
    hclosed hTI x horder himage hmodel
  let : Group.IsPerfect L := hstructure.2.1
  have hdata := central_involution_ti_hull_odd_quotient_witness T U hUT hUel hcard
    hclosed hTI x horder himage hmodel
  let : L₁.Normal := hdata.1
  let : Group.IsPerfect L₁ := hdata.2.1
  obtain ⟨w, _, _, ⟨hwT, hwcenter⟩, hwnoncentral⟩ := hdata.2.2.2.2.2
  have hZ₁ : Subgroup.center L₁ = ⊥ :=
    rank_one_center_two_inner_sylow_witness_eq_bot T₁ L₁ hdata.2.2.2.1
      hdata.2.2.2.2.1 w hwT hwcenter hwnoncentral
  have hodd : Odd (Nat.card (Subgroup.center L)) :=
    ambient_odd_center_odd_center_of_quotient_center_eq_bot L hZ₁
  exact ⟨hstructure.2.2.1, hodd, hstructure.2.2.2.2.2.2,
    central_involution_intersection_eq_bot_of_odd_center L x horder hodd,
    centralInvolutionHullEquivOfOddCenter L x horder hodd,
    centralInvolutionHullEquivOfOddCenter_apply L x horder hodd⟩

end CFSG.ShultStronglyClosedTI
