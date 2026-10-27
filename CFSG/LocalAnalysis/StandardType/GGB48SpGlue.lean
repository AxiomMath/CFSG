module

public import CFSG.LocalAnalysis.StandardType.GGB48Reduce
public import CFSG.LocalAnalysis.StandardType.GGB48SpWeyl
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrInner
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.Models.Transport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem center_eq_bot_of_quasisimple_psp63 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (hL : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp 3 2 2) :
    Subgroup.center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  have hL' : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 2 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hL⟩
  have hM : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 2 :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by omega) hL'
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large .PSp hM
      (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl (by norm_num))⟩)))
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y)) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp 3 2 2 = (1, 1) := by decide
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 3 2 2 = (1, 1) := by decide
    have h1 : Nat.card (Multiplicative (ZMod 1)) = 1 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
      Nat.card_prod, h1, mul_one]
  have hdvd :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl (Y ⧸ Subgroup.center Y))
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

section SpGlue

theorem ggB48_of_sp_six_four
    (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {B Bs N : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hinn : GGInnerDiagOn Bs N)
    (hmod : StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSp 3 2 2) :
    48 ≤ Nat.card (ggAutomizer N Bs) := by
  have hqs : CFSG.Assembly.IsQuasisimple N := isQuasisimple_of_largeEvenMarking hinn
  have hY : CFSG.IsQuasisimple ↥N := (TableBSymp.isQuasisimple_iff ↥N).mp hqs
  have hZ : Subgroup.center ↥N = ⊥ := center_eq_bot_of_quasisimple_psp63 hY hmod
  have hnorm : Bs ≤ Subgroup.normalizer (N : Set G) := GGInnerDiagOn.le_normalizer hinn
  obtain ⟨hadm, K, _, _, hK, ⟨eK⟩⟩ := hmod
  have hf : 1 ≤ 2 := hadm.2.1
  have hscalK : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) = ⊥ :=
    statedScalars_subgroupOf_statedSp_eq_bot_of_card (n := 3) (f := 2) hK hf (by norm_num)
  have eProj : StatedProj (StatedSp 3 K) ≃* StatedSp 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hscalK).trans QuotientGroup.quotientBot
  have eAll : (↥N ⧸ Subgroup.center ↥N) ≃* StatedSp 3 K := eK.trans eProj
  have q : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have e₁ : ↥N ≃* StatedSp 3 K := q.symm.trans eAll
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK,
      GaloisField.card 2 2 (by norm_num)]
  let ε : K ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq hcard
  let e : ↥N ≃* StatedSp 3 (GaloisField 2 2) :=
    e₁.trans (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ε 3)
  let φ : StatedSp 3 (GaloisField 2 2) →* G := N.subtype.comp e.symm.toMonoidHom
  have hinj : Function.Injective φ := N.subtype_injective.comp e.symm.injective
  have hrange : φ.range = N := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [φ]⟩
  have hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (m := 2) (f := 2) (by norm_num) hadm hinn φ hinj hrange
  obtain ⟨E, hEN, hEab, hEself, hbound⟩ := ggB48_reduce hBs hZ hnorm hinner
  let E' : Subgroup (StatedSp 3 (GaloisField 2 2)) := E.comap φ
  have hmapE : E'.map φ = E := by
    rw [Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.mpr hEN
  have hE'ab : IsElemAbelian 3 E' := IsElemAbelian.comap hEab hinj
  have hself' : ∀ g : StatedSp 3 (GaloisField 2 2),
      g ∈ Subgroup.centralizer (E' : Set (StatedSp 3 (GaloisField 2 2))) → g ^ 3 = 1 →
      g ∈ E' := by
    intro g hg hg3
    rw [Subgroup.mem_comap]
    apply hEself (φ g)
    · rw [← hrange]
      exact ⟨g, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      rw [← hmapE] at he
      obtain ⟨y, hy, rfl⟩ := he
      have hgy := Subgroup.mem_centralizer_iff.mp hg y hy
      calc φ y * φ g = φ (y * g) := (map_mul φ y g).symm
        _ = φ (g * y) := by rw [hgy]
        _ = φ g * φ y := map_mul φ g y
    · rw [← map_pow, hg3, map_one]
  obtain ⟨W', hW'norm, hW'cent, hW'card⟩ := ggB48_sp_six_four_weyl E' hE'ab hself'
  have hWN : W'.map φ ≤ N := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [← hrange]
    exact ⟨y, rfl⟩
  have hWnorm : W'.map φ ≤ Subgroup.normalizer (E : Set G) := by
    have h2 : W'.map φ ≤ (Subgroup.normalizer (E' : Set _)).map φ := Subgroup.map_mono hW'norm
    have h3 := h2.trans (Subgroup.le_normalizer_map φ (H := E'))
    simpa [hmapE] using h3
  have hWcent : ∀ w ∈ W'.map φ, w ∈ Subgroup.centralizer (E : Set G) → w = 1 := by
    intro w hw hwc
    obtain ⟨y, hy, rfl⟩ := hw
    have hycent : y ∈ Subgroup.centralizer (E' : Set (StatedSp 3 (GaloisField 2 2))) := by
      rw [Subgroup.mem_centralizer_iff] at hwc ⊢
      intro x hx
      have hxE : φ x ∈ E := by
        rw [← hmapE]
        exact ⟨x, hx, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact hwc (φ x) hxE
    rw [hW'cent y hy hycent, map_one]
  have hWcard : 48 ≤ Nat.card (W'.map φ) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hW'card
  exact hWcard.trans (hbound (W'.map φ) hWN hWnorm hWcent)

end SpGlue

end CFSG.StandardType

end
