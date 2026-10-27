module

import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveFam
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup InFGroup)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  (W4Lem4_11 IsCoverL3OddOver IsCoverU3OddOver)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar)
open CFSG.Blueprint (LieModel)

private theorem conjSub_ne_bot_of_ne_bot {G : Type} [Group G] {A : Subgroup G} (hA : A ≠ ⊥)
    (g : G) : CFSG.Quasithin.A1b.conjSub g A ≠ ⊥ := by
  intro h
  apply hA
  have h' : A.map (MulAut.conj g).toMonoidHom = ⊥ := h
  exact (Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj g).injective).mp h'

theorem inE_of_inEP {G : Type} [Group G] [Finite G] {j : ℕ} {H : Subgroup G}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InEP j H) : E1.InE j H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T hT Ω hΩ
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T H := CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  by_cases hex : ∃ A ∈ Ω, A ≠ ⊥
  · obtain ⟨A₀, hA₀, hA₀b⟩ := hex
    set Ω' : Set (Subgroup G) := {A | A ∈ Ω ∧ A ≠ ⊥} with hΩ'def
    have hΩ' : E1.IsInvColl H Ω' :=
      ⟨fun A hA => hΩ.le A hA.1, fun A hA => hΩ.isElemAbelian A hA.1,
        fun A hA g hg => ⟨hΩ.conj A hA.1 g hg, conjSub_ne_bot_of_ne_bot hA.2 g⟩⟩
    have h1 := h T hT' Ω' hΩ' ⟨A₀, hA₀, hA₀b⟩ fun A hA => hA.2
    have hW : E1.weakClosure T Ω' = E1.weakClosure T Ω := by
      apply le_antisymm
      · exact iSup₂_le fun A hA => le_iSup₂_of_le A hA.1 le_rfl
      · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
        by_cases hAb : A = ⊥
        · rw [hAb]
          exact bot_le
        · exact le_iSup₂_of_le A ⟨hA, hAb⟩ (le_iSup_of_le hAT le_rfl)
    have hle : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP j H T Ω' ≤ E1.eGen j H T Ω' :=
      iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK =>
        le_iSup₂_of_le A hA (le_iSup_of_le hAT
          (le_iSup₂_of_le K (isE_of_isEP hT hAT (hΩ'.isElemAbelian A hA) hK) le_rfl))
    have hmono : E1.eGen j H T Ω' ≤ E1.eGen j H T Ω :=
      E1.eGen_mono_set j H T fun A hA => hA.1
    have hfin : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP j H T Ω' ⊔
        (H ⊓ normalizer (E1.weakClosure T Ω' : Set G)) ≤
        E1.eGen j H T Ω ⊔ (H ⊓ normalizer (E1.weakClosure T Ω : Set G)) := by
      rw [hW]
      exact sup_le_sup_right (hle.trans hmono) _
    exact le_antisymm (sup_le (E1.eGen_le j H T Ω) inf_le_left) (h1.symm.le.trans hfin)
  · push Not at hex
    have hW : E1.weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun _ => ?_)
      rw [hex A hA]
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_eq_right]
    exact E1.eGen_le j H T Ω

theorem inE_top_of_inEGroup {Q : Type} [Group Q] [Finite Q] (j : ℕ) (h : InEGroup j Q) :
    E1.InE j (⊤ : Subgroup Q) :=
  inE_of_inEP (inEP_top_of_inEGroup j h)

theorem fstar_top_eq_generalizedFitting (Q : Type) [Group Q] [Finite Q] :
    Fstar (⊤ : Subgroup Q) = CFSG.generalizedFitting Q := by
  have h1 : CFSG.Open.genFittingFStar ↥(⊤ : Subgroup Q) =
      CFSG.generalizedFitting ↥(⊤ : Subgroup Q) :=
    CFSG.Adapters.genFittingFStar_eq_foundations _
  have h2 := CFSG.WholeGroup.generalizedFitting_map_mulEquiv (Subgroup.topEquiv (G := Q))
  show (CFSG.Open.genFittingFStar ↥(⊤ : Subgroup Q)).map (⊤ : Subgroup Q).subtype = _
  rw [h1, ← h2]
  rfl

@[expose] def Asch4_11ASPow : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (T : Subgroup Q) (p f : ℕ), p.Prime → p ≠ 2 → 2 ≤ f →
    IsSimpleGroup ↥(CFSG.generalizedFitting Q) →
    (∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a) →
    (LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f ∨
      LieModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f) →
    IsSylowIn 2 T ⊤ → CFSG.generalizedFitting Q ⊔ T = ⊤ → E1.InE 1 (⊤ : Subgroup Q)

end CFSG.LocalAnalysis.WeakClosure81

end
