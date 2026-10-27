module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Core
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Families
public import CFSG.LieType.Seitz.Defs
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

@[expose] def Seitz434 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    IsLie42Generic (X ⧸ Subgroup.center X) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E →
      (Nat.card E = 9 ∨ (Nat.card E = 27 ∧ Subgroup.center X = ⊥)) →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

noncomputable def layerConj (G : Type) [Group G] : G →* MulAut (layer G) :=
  haveI : (layer G).Characteristic := layer_characteristic
  MulAut.conjNormal

theorem layerConj_apply_coe {G : Type} [Group G] (g : G) (x : layer G) :
    ((layerConj G g x : layer G) : G) = g * x * g⁻¹ := by
  have : (layer G).Characteristic := layer_characteristic
  exact MulAut.conjNormal_apply g x

theorem layerConj_eq_one_iff {G : Type} [Group G] {g : G} :
    layerConj G g = 1 ↔ g ∈ Subgroup.centralizer (layer G : Set G) := by
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut (layer G) => ((φ ⟨x, hx⟩ : layer G) : G)) hg
    simp only [layerConj_apply_coe, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  · intro hg
    ext x
    rw [layerConj_apply_coe, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hg x x.2
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
      _ = x := by group

theorem card_eq_card_inf_mul_card_map {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    Nat.card X = Nat.card (X ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) *
      Nat.card (X.map (layerConj G)) := by
  set f : X →* MulAut (layer G) := (layerConj G).comp X.subtype with hf
  have hrange : f.range = X.map (layerConj G) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (Subgroup.centralizer (layer G : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
      Subgroup.coe_subtype, layerConj_eq_one_iff]
  have hcard : Nat.card f.ker =
      Nat.card (X ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, hrange, hcard]

namespace Ctx434Core

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

noncomputable abbrev layerStar (_h : Ctx434Core G A M Q) : Subgroup (MulAut (layer G)) :=
  A.map (layerConj G)

theorem isElemAbelian_layerStar (h : Ctx434Core G A M Q) :
    CFSG.Assembly.IsElemAbelian 3 h.layerStar :=
  CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 (layerConj G) A h.isE27.1

theorem card_inf_mul_card_layerStar (h : Ctx434Core G A M Q) :
    Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) *
      Nat.card h.layerStar = 27 := by
  rw [← card_eq_card_inf_mul_card_map A, h.isE27.2]

theorem card_inf_centralizer_layer_eq (h : Ctx434Core G A M Q) :
    Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 1 ∨
      Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
  have hle := h.card_inf_centralizer_layer_le
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) ∣ 27 :=
    ⟨_, h.card_inf_mul_card_layerStar.symm⟩
  have hpos := Nat.card_pos (α := (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G))
  interval_cases hc : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) <;>
    simp_all

theorem map_center_layer_le_pCore (h : Ctx434Core G A M Q) :
    (Subgroup.center (layer G)).map (layer G).subtype ≤ CFSG.pCore 3 G := by
  have : (layer G).Characteristic := layer_characteristic
  have hnorm : ((Subgroup.center (layer G)).map (layer G).subtype).Normal := inferInstance
  have hcomm : IsMulCommutative ((Subgroup.center (layer G)).map (layer G).subtype) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    change (a : G) * b = b * a
    rw [← ha, ← hb]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b').symm
  have hF : (Subgroup.center (layer G)).map (layer G).subtype ≤ fittingSubgroup G :=
    le_sSup ⟨hnorm, inferInstance⟩
  exact hF.trans (fittingSubgroup_le_pCore_three h.theta_eq_bot)

theorem isPGroup_center_layer (h : Ctx434Core G A M Q) :
    IsPGroup 3 (Subgroup.center (layer G)) := by
  have hp : IsPGroup 3 ((Subgroup.center (layer G)).map (layer G).subtype) :=
    (CFSG.pCore_isPGroup (p := 3) (G := G)).to_le h.map_center_layer_le_pCore
  exact hp.of_equiv ((Subgroup.center (layer G)).equivMapOfInjective _
    (layer G).subtype_injective).symm

theorem card_layerStar (h : Ctx434Core G A M Q) :
    Nat.card h.layerStar = 9 ∨ (Nat.card h.layerStar = 27 ∧ Subgroup.center (layer G) = ⊥) := by
  have h27 := h.card_inf_mul_card_layerStar
  rcases h.card_inf_centralizer_layer_eq with h1 | h3
  · right
    rw [h1, one_mul] at h27
    refine ⟨h27, ?_⟩
    rcases h.rank3II_4_38 with ⟨hO, -, -⟩ | ⟨-, hc⟩
    · have hle := h.map_center_layer_le_pCore
      rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (layer G).subtype_injective]
        at hle
      exact hle
    · omega
  · left
    rw [h3] at h27
    omega

theorem card_inf_comap_layerConj (h : Ctx434Core G A M Q) {F : Subgroup (MulAut (layer G))}
    (hFE : F ≤ h.layerStar) (hF3 : F.relIndex h.layerStar = 3) :
    Nat.card (A ⊓ F.comap (layerConj G) : Subgroup G) = 9 := by
  set B := A ⊓ F.comap (layerConj G) with hB
  have hBmap : B.map (layerConj G) = F := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.2
    · intro φ hφ
      obtain ⟨a, ha, rfl⟩ := hFE hφ
      exact ⟨a, ⟨ha, hφ⟩, rfl⟩
  have hBC : B ⊓ Subgroup.centralizer (layer G : Set G) =
      A ⊓ Subgroup.centralizer (layer G : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · intro c hc
      refine ⟨⟨hc.1, ?_⟩, hc.2⟩
      show layerConj G c ∈ F
      rw [layerConj_eq_one_iff.mpr hc.2]
      exact F.one_mem
  have hcardB := card_eq_card_inf_mul_card_map B
  rw [hBC, hBmap] at hcardB
  have hFcard : 3 * Nat.card F = Nat.card h.layerStar := by
    have := Subgroup.relIndex_mul_card (H := F) (K := h.layerStar)
    rwa [hF3, inf_eq_left.mpr hFE] at this
  have h27 := h.card_inf_mul_card_layerStar
  rw [hcardB]
  have h3 : 3 * (Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) *
      Nat.card F) = 27 := by
    rw [← h27, ← hFcard]
    ring
  omega

theorem map_fixedPoints_le (h : Ctx434Core G A M Q) {F : Subgroup (MulAut (layer G))}
    (hFE : F ≤ h.layerStar) (hF3 : F.relIndex h.layerStar = 3) :
    (CFSG.LieType.Seitz.fixedPoints F).map (layer G).subtype ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ F.comap (layerConj G) with hB
  have hBA : B ≤ A := inf_le_left
  have hB9 := h.card_inf_comap_layerConj hFE hF3
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le h.isE27.1 hBA
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, hBe, by rw [hB9]; norm_num⟩
  have hCB : (CFSG.LieType.Seitz.fixedPoints F).map (layer G).subtype ≤
      Subgroup.centralizer (B : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfix : layerConj G b x = x := (CFSG.LieType.Seitz.mem_fixedPoints.mp hx) _ hb.2
    have h1 : b * (x : G) * b⁻¹ = x := by
      rw [← layerConj_apply_coe, hfix]
    calc b * (x : G) = b * x * b⁻¹ * b := by group
      _ = x * b := by rw [h1]
  exact hCB.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hBA hB2).trans h.gamma_le))

theorem layer_le_of_seitzHyperGamma_eq_top (h : Ctx434Core G A M Q)
    (hgen : CFSG.LieType.Seitz.seitzHyperGamma 3 h.layerStar = ⊤) : layer G ≤ M := by
  have hL : layer G = (⊤ : Subgroup (layer G)).map (layer G).subtype := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hL, ← hgen, Subgroup.map_le_iff_le_comap, CFSG.LieType.Seitz.seitzHyperGamma]
  refine iSup₂_le fun F hF => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact h.map_fixedPoints_le hF.1 hF.2

theorem false_of_seitz434 (hS : Seitz434) (h : Ctx434Core G A M Q)
    (hL : IsLie42Generic (layer G ⧸ Subgroup.center (layer G))) : False :=
  h.not_le (h.layer_le_of_seitzHyperGamma_eq_top
    (hS (layer G) h.isQuasisimple h.isPGroup_center_layer hL h.layerStar
      h.isElemAbelian_layerStar h.card_layerStar))

end Ctx434Core

end CFSG.RankThree.PartTwo.Sec4
