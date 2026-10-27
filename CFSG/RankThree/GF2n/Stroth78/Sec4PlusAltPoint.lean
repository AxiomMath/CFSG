module

public import CFSG.LargeExtraspecial.AS35YUPSL4Maps
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltFive

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltSmall
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LargeExtraspecial.AS35YUSL4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LargeExtraspecial.A2Mod
  (A2Action IsPointMaps commSpaceOf commSpace_le_commSpaceOf transvectionSet)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

section Hub


theorem exists_pointMaps_of_lieModel_psl4
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4)
    (hL : CFSG.Blueprint.LieModel ↥(Xsub S a) .PSL 4 2 1) :
    w = 4 ∧ Subgroup.centralizer (Xsub S a : Set (Hbar z)) = ⊥ ∧
      ∃ (Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(Xsub S a))
        (P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Additive (QbarOf S)),
        Function.Surjective Ψ ∧ Function.Injective Ψ ∧
        A2Action (transvectionSet 4 (ZMod 2)) (qS S) ((rhoX S a).comp Ψ) ∧
        IsPointMaps ((rhoX S a).comp Ψ) (qS S) P Pd ∧
        LinearMap.range P ⊔ LinearMap.range Pd = ⊤ := by
  classical
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).mp hL
  obtain ⟨Ψ, hs, hinj, hA'⟩ := CFSG.LargeExtraspecial.AS35YU.exists_surjective_sl4_of_lieModel_psl4
    (rootClass_Xsub S h h217 h34) (a2Action_Xsub S a) hL
  rcases CFSG.LargeExtraspecial.AS35YU.exists_isPointMaps_or_finrank_le_six hA' with
    ⟨P, Pd, hP⟩ | hle
  swap
  · exfalso
    have h1 := six_lt_finrank_commSpaceOf_rhoX_of_mulEquiv_alt8 S h h217 h34 hZ e
    rw [← MonoidHom.range_eq_top.mpr hs, CFSG.LargeExtraspecial.A2Mod.commSpaceOf_range] at h1
    omega
  have hw5 : w ≤ 5 := (card_Lbar_numerics_of_mulEquiv_alt8 S h h217 h34 hZ e).1
  rcases (show w = 4 ∨ w = 5 by omega) with hw | hw
  · have hdim : finrank (ZMod 2) (Additive (QbarOf S)) = 8 := by
      rw [finrank_QbarOf_eq_two_mul S h.card_F, hw]
    have htop : LinearMap.range P ⊔ LinearMap.range Pd = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hP.finrank_range_sup, hdim]
    refine ⟨hw, ?_, Ψ, P, Pd, hs, hinj, hA', hP, htop⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcomm : ∀ g, rhoLin S c * ((rhoX S a).comp Ψ) g = ((rhoX S a).comp Ψ) g * rhoLin S c := by
      intro g
      rw [MonoidHom.comp_apply, rhoX_apply]
      have hc' : ((Ψ g : ↥(Xsub S a)) : Hbar z) * c = c * ((Ψ g : ↥(Xsub S a)) : Hbar z) :=
        Subgroup.mem_centralizer_iff.mp hc _ (Ψ g).2
      show rhoLin S c * rhoLin S ↑(Ψ g) = rhoLin S ↑(Ψ g) * rhoLin S c
      rw [← rhoLin_mul, ← rhoLin_mul, hc']
    have hfix := hP.apply_eq_self_of_commute hcomm
    apply rhoLin_injective S
    refine LinearEquiv.ext fun x => ?_
    rw [hfix x (htop ▸ Submodule.mem_top)]
    simp [rhoLin]
  · exact (false_of_w_eq_five_of_isPointMaps S h h217 h34 hZ e hs hA' hP hw).elim

end Hub

end CFSG.RankThree.GF2n.Stroth78
