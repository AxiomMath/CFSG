module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Subgroup Item434Kit Item434Alt

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem card_inf_centralizer_eq_three (h : Ctx434Core G A M Q)
    (h9 : Nat.card (A.map (layerConj G)) = 9) :
    Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
  have h27 := h.card_inf_mul_card_layerStar
  change _ * Nat.card (A.map (layerConj G)) = 27 at h27
  rw [h9] at h27
  omega

theorem inf_centralizer_ne_bot (h : Ctx434Core G A M Q)
    (h9 : Nat.card (A.map (layerConj G)) = 9) :
    A ⊓ Subgroup.centralizer (layer G : Set G) ≠ ⊥ := by
  intro hbot
  have h3 := card_inf_centralizer_eq_three h h9
  rw [hbot, Subgroup.card_bot] at h3
  omega

theorem forall_not_inducesOuter (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) (h9 : Nat.card (A.map (layerConj G)) = 9)
    (hrk : ∀ a ∈ A, InducesOuter a (layer G) →
      2 ≤ CFSG.Open.pRank 3 (layer G ⊓ Subgroup.centralizer {a})) :
    ∀ a ∈ A, ¬ InducesOuter a (layer G) := by
  have : (layer G).Characteristic := layer_characteristic
  have hne := inf_centralizer_ne_bot h h9
  have hZL : ¬ A ⊓ Subgroup.centralizer (layer G : Set G) ≤
      (Subgroup.center (layer G)).map (layer G).subtype := by
    rw [hZ, Subgroup.map_bot, le_bot_iff]
    exact hne
  rcases (h.rank3II_4_39 hne hZL).2 with ⟨hsup, -⟩ | ⟨a, ha, hout, hr⟩
  · intro a ha
    apply not_inducesOuter_of_mem_sup
    have h1 : a ∈ A ⊔ layer G := Subgroup.mem_sup_left ha
    rw [hsup] at h1
    have hle : A ⊓ Subgroup.centralizer (layer G : Set G) ⊔ layer G ≤
        layer G ⊔ Subgroup.centralizer (layer G : Set G) :=
      sup_le (inf_le_right.trans le_sup_right) le_sup_left
    exact hle h1
  · exact absurd (hrk a ha hout) (by omega)

section Transport

variable {X : Type*} [Group X]

theorem quotConj_pow_three (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} (ha : a ∈ A) :
    quotConj e a ^ 3 = 1 := by
  rw [← map_pow, h.isE27.1.2 a ha, map_one]

omit [Finite G] in
theorem not_mem_range_conj_of_inducesOuter (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} (hout : InducesOuter a (layer G)) :
    quotConj e a ∉ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨haN, hnot⟩ := hout
  rintro ⟨x, hx⟩
  apply hnot
  set ι := layerEquiv e hZ
  refine ⟨ι.symm x, MulEquiv.ext fun y => ?_⟩
  apply layerQuot_injective e hZ
  have h1 : layerQuot e (compAction (layer G) ⟨a, haN⟩ y) = layerQuot e (layerConj G a y) := by
    congr 1
    apply Subtype.ext
    rw [layerConj_apply_coe]
    rfl
  rw [MulAut.conj_apply, h1, ← quotConj_layerQuot, ← hx, map_mul, map_mul, map_inv,
    MulAut.conj_apply]
  have hι : layerQuot e (ι.symm x) = x := ι.apply_symm_apply x
  rw [hι]

theorem two_le_pRank_of_fixed (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} {E : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hfix : ∀ x ∈ E, quotConj e a x = x) :
    2 ≤ CFSG.Open.pRank 3 (layer G ⊓ Subgroup.centralizer {a}) := by
  have hle : liftSub e hZ E ≤ Subgroup.centralizer {a} := by
    rintro _ ⟨y, ⟨d, hd, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set ι := layerEquiv e hZ
    have hconj : layerConj G a (ι.symm d) = ι.symm d := by
      apply layerQuot_injective e hZ
      rw [← quotConj_layerQuot]
      have hd' : layerQuot e (ι.symm d) = d := ι.apply_symm_apply d
      rw [hd', hfix d hd]
    have h1 : a * ((ι.symm d : layer G) : G) * a⁻¹ = ι.symm d := by
      rw [← layerConj_apply_coe, hconj]
    change ((ι.symm d : layer G) : G) * a = a * ((ι.symm d : layer G) : G)
    calc ((ι.symm d : layer G) : G) * a = a * ((ι.symm d : layer G) : G) * a⁻¹ * a := by
          rw [h1]
      _ = a * ((ι.symm d : layer G) : G) := by group
  exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
    ⟨_, le_inf (liftSub_le e hZ E) hle, isElemAbelian_liftSub e hZ hE,
      by rw [card_liftSub, hE9]; norm_num⟩

theorem forall_not_inducesOuter_of_fixed (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) (h9 : Nat.card (A.map (layerConj G)) = 9)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hX : ∀ φ : MulAut X, φ ^ 3 = 1 → φ ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ x ∈ E, φ x = x) :
    ∀ a ∈ A, ¬ InducesOuter a (layer G) := by
  refine forall_not_inducesOuter h hZ h9 fun a ha hout => ?_
  obtain ⟨E, hE, hE9, hfix⟩ := hX (quotConj e a) (quotConj_pow_three h e ha)
    (not_mem_range_conj_of_inducesOuter hZ e hout)
  exact two_le_pRank_of_fixed hZ e hE hE9 hfix

theorem false_of_E27_of_card_nine (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    {D : Subgroup X} (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False :=
  inf_centralizer_ne_bot h h9 (Item434Kit.inf_centralizer_layer_eq_bot h hZ e hD hD27)

end Transport

theorem layer_le_of_closure_fixed (h : Ctx434Core G A M Q)
    (h9 : Nat.card (A.map (layerConj G)) = 9)
    (hgen : Subgroup.closure {x : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ x = x} = ⊤) :
    layer G ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := A ⊓ Subgroup.centralizer (layer G : Set G) with hC
  have hC3 : Nat.card C = 3 := card_inf_centralizer_eq_three h h9
  have hCe : CFSG.Assembly.IsElemAbelian 3 C := Source.isElemAbelian_of_le h.isE27.1 inf_le_left
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsub : {x : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ x = x} ⊆
      (M.comap (layer G).subtype : Set (layer G)) := by
    rintro x ⟨_, ⟨a, ha, rfl⟩, hφ1, hφx⟩
    have haC : a ∉ C := fun haC => hφ1 (layerConj_eq_one_iff.mpr haC.2)
    obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hCe haC (h.isE27.1.2 a ha)
      fun b hb => hAc b hb.1 a ha
    have hBA : C ⊔ Subgroup.zpowers a ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr ha)
    have hB9 : 9 ≤ Nat.card (C ⊔ Subgroup.zpowers a : Subgroup G) := by
      rw [hBcard, hC3]
    have hxa : a * (x : G) * a⁻¹ = x := by rw [← layerConj_apply_coe, hφx]
    have hxB : (x : G) ∈ Subgroup.centralizer ((C ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
      have hCx : C ≤ Subgroup.centralizer ({(x : G)} : Set G) := fun c hc =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hc.2 x x.2).symm
      have hax : a ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc a * (x : G) = a * (x : G) * a⁻¹ * a := by group
          _ = x * a := by rw [hxa]
      have hle : C ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({(x : G)} : Set G) :=
        sup_le hCx (Subgroup.zpowers_le.mpr hax)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
    exact (Subgroup.centralizer_le_normalizer _).trans (normalizer_le h hBA hB9) hxB
  have htop : (⊤ : Subgroup (layer G)) ≤ M.comap (layer G).subtype := by
    rw [← hgen, Subgroup.closure_le]
    exact hsub
  intro x hx
  exact htop (Subgroup.mem_top ⟨x, hx⟩)

theorem center_layer_eq_bot_of_cover (h : Ctx434Core G A M Q)
    (hcov : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* layer G ⧸ Subgroup.center (layer G)), Function.Surjective π →
        π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hker := QuotientGroup.ker_mk' (Subgroup.center (layer G))
  have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center (layer G))).ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  have h1 := hcov (layer G) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (by rw [hker]) hodd
  rwa [hker] at h1

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
