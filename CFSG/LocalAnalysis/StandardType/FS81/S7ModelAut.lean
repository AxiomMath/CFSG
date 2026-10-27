module

public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelWeyl

import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIso

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

section M6d


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem frameCoordHom_frameE8_surjective :
    Function.Surjective (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8) :=
  Finite.injective_iff_surjective.mp frameCoordHom_frameE8_injective

private noncomputable def weylNorm (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    adjointGroup .E8 K :=
  Classical.choose (exists_mem_normalizer_frameTorusE8_torusAct (K := K) hK w)

private theorem weylNorm_mem (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    weylNorm hK w ∈ Subgroup.normalizer (frameTorusE8 K : Set (adjointGroup .E8 K)) :=
  (Classical.choose_spec (exists_mem_normalizer_frameTorusE8_torusAct (K := K) hK w)).1

private theorem weylNorm_spec (hK : Nat.card K = 2) (w : WeylGroup .E8)
    (v : Fin (7 + 1) → ZMod 3) :
    ∃ v' : Fin (7 + 1) → ZMod 3,
      weylNorm hK w * TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v) *
          (weylNorm hK w)⁻¹ =
        TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v') ∧
      ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v' =
        TableBExc.torusAct .E8 3 w (ExcFrameIso.frameCoordHom TableBExcTwo.frameE8 v) :=
  (Classical.choose_spec (exists_mem_normalizer_frameTorusE8_torusAct (K := K) hK w)).2 v

private noncomputable def weylAut (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    MulAut ↥(frameTorusE8 K) :=
  Subgroup.normalizerMonoidHom (frameTorusE8 K)
    ⟨weylNorm hK w, weylNorm_mem hK w⟩

private theorem weylAut_mem_ggInduced (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    weylAut hK w ∈ ggInduced (⊤ : Subgroup (adjointGroup .E8 K)) (frameTorusE8 K) := by
  refine ⟨weylNorm hK w, Subgroup.mem_top _, weylNorm_mem hK w, fun b => ?_⟩
  simp only [weylAut, Subgroup.normalizerMonoidHom_apply_apply_coe]

private noncomputable def weylAutA (hK : Nat.card K = 2) (w : WeylGroup .E8) :
    ↥(ggAutomizer (⊤ : Subgroup (adjointGroup .E8 K)) (frameTorusE8 K)) :=
  ⟨weylAut hK w, Subgroup.subset_closure (weylAut_mem_ggInduced hK w)⟩

private theorem weylAutA_injective (hK : Nat.card K = 2) :
    Function.Injective (weylAutA hK) := by
  intro w w' h
  have haut : weylAut hK w = weylAut hK w' := congrArg Subtype.val h
  have hact : TableBExc.torusAct .E8 3 w = TableBExc.torusAct .E8 3 w' := by
    funext x
    obtain ⟨v, rfl⟩ := frameCoordHom_frameE8_surjective x
    obtain ⟨v1, hv1, hΛ1⟩ := weylNorm_spec hK w v
    obtain ⟨v2, hv2, hΛ2⟩ := weylNorm_spec hK w' v
    have hval : weylAut hK w ⟨TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v),
        ⟨Multiplicative.ofAdd v, rfl⟩⟩ =
        weylAut hK w' ⟨TableBExcTwoTB.tE K TableBExcTwo.frameE8 (Multiplicative.ofAdd v),
        ⟨Multiplicative.ofAdd v, rfl⟩⟩ := by rw [haut]
    have hval' := congrArg Subtype.val hval
    simp only [weylAut, Subgroup.normalizerMonoidHom_apply_apply_coe] at hval'
    rw [hv1, hv2] at hval'
    have hv12 : v1 = v2 := by
      apply Multiplicative.ofAdd.injective
      exact TableBExcTwoTB.tE_injective (K := K) (F := TableBExcTwo.frameE8) hval'
    rw [← hΛ1, ← hΛ2, hv12]
  have hperm : TableBExc.torusPerm .E8 3 w = TableBExc.torusPerm .E8 3 w' := by
    apply Equiv.ext
    intro x
    rw [TableBExc.torusPerm_apply, TableBExc.torusPerm_apply]
    exact congrFun hact x
  exact NoOffExc.torusPerm_injective (τ := .E8) (p := 3) (by decide) hperm

private theorem le_natCard_ggAutomizer_frameTorusE8 (hK : Nat.card K = 2) :
    696729600 ≤ Nat.card (ggAutomizer (⊤ : Subgroup (adjointGroup .E8 K)) (frameTorusE8 K)) := by
  have hle := Nat.card_le_card_of_injective (weylAutA hK) (weylAutA_injective hK)
  rwa [NoOffExc.card_weyl_E8] at hle

theorem le_natCard_ggAutomizer_of_card_E8 (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .E8 K)} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E) :
    696729600 ≤ Nat.card (ggAutomizer (⊤ : Subgroup (adjointGroup .E8 K)) E) := by
  classical
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hK hE hcard
  have hconj := natCard_ggAutomizer_map (M := adjointGroup .E8 K) (G := adjointGroup .E8 K)
    (ι := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective (frameTorusE8 K)
  have hrange : (MulAut.conj c).toMonoidHom.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    refine ⟨c⁻¹ * y * c, ?_⟩
    simp [MulAut.conj_apply]
    group
  have hT : Subgroup.map (MulAut.conj c).toMonoidHom (frameTorusE8 K) = E := by
    simpa only [frameTorusE8] using hc.symm
  rw [hrange, hT] at hconj
  rw [hconj]
  exact le_natCard_ggAutomizer_frameTorusE8 hK

theorem le_natCard_ggAutomizer_range_of_card_E8 {G : Type} [Group G]
    (hK : Nat.card K = 2) (ι : adjointGroup .E8 K →* G) (hι : Function.Injective ι)
    {E : Subgroup G} (hEY : E ≤ ι.range) (hE : IsElemAbelian 3 E) (hcard : 3 ^ 8 ≤ Nat.card E) :
    696729600 ≤ Nat.card (ggAutomizer ι.range E) := by
  have hE0 : (E.comap ι).map ι = E := Subgroup.map_comap_eq_self hEY
  have hcard0 : 3 ^ 8 ≤ Nat.card (E.comap ι) := by
    rw [← Subgroup.card_map_of_injective hι, hE0]
    exact hcard
  have h := le_natCard_ggAutomizer_of_card_E8 hK (isElemAbelian_comap ι hι hE) hcard0
  rw [← natCard_ggAutomizer_map ι hι (E.comap ι), hE0] at h
  exact h

end M6d

end CFSG.StandardType.FrameRoute.FS81

end
