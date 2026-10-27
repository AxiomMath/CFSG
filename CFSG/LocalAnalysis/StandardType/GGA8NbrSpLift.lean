module

public import CFSG.LocalAnalysis.StandardType.GGB48SpGlue
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.Open

private theorem a8jl_center_eq_bot_of_quasisimple_psp63 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (hL : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp 3 2 3) :
    Subgroup.center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  have hL' : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 3 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hL⟩
  have hM : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 3 :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by omega) hL'
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.griess_classical_of_large .PSp hM
      (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (by norm_num)⟩)))
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y)) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp 3 2 3 = (1, 1) := by decide
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 3 2 3 = (1, 1) := by decide
    have h1 : Nat.card (Multiplicative (ZMod 1)) = 1 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
      Nat.card_prod, h1, mul_one]
  have hdvd :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl (Y ⧸ Subgroup.center Y))
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

theorem ggA8Nbr_spLift
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 3) :
    ∃ ψ : StatedSp 3 (GaloisField 2 3) →* G, Function.Injective ψ ∧ ψ.range = L := by
  have hqs : CFSG.Assembly.IsQuasisimple L := isQuasisimple_of_largeEvenMarking hInnL
  have hY : CFSG.IsQuasisimple ↥L := (TableBSymp.isQuasisimple_iff ↥L).mp hqs
  have hZ : Subgroup.center ↥L = ⊥ := a8jl_center_eq_bot_of_quasisimple_psp63 hY hmod
  obtain ⟨hadm, K, _, _, hK, ⟨eK⟩⟩ := hmod
  have hf : 1 ≤ 3 := hadm.2.1
  have hscalK : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) = ⊥ :=
    statedScalars_subgroupOf_statedSp_eq_bot_of_card (n := 3) (f := 3) hK hf (by norm_num)
  have eProj : StatedProj (StatedSp 3 K) ≃* StatedSp 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hscalK).trans QuotientGroup.quotientBot
  have eAll : (↥L ⧸ Subgroup.center ↥L) ≃* StatedSp 3 K := eK.trans eProj
  have q : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have e₁ : ↥L ≃* StatedSp 3 K := q.symm.trans eAll
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK,
      GaloisField.card 2 3 (by norm_num)]
  let ε : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq hcard
  let e : ↥L ≃* StatedSp 3 (GaloisField 2 3) :=
    e₁.trans (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ε 3)
  let ψ : StatedSp 3 (GaloisField 2 3) →* G := L.subtype.comp e.symm.toMonoidHom
  refine ⟨ψ, ?_, ?_⟩
  · exact L.subtype_injective.comp e.symm.injective
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [ψ]⟩

end CFSG.StandardType.A8Coord

end
