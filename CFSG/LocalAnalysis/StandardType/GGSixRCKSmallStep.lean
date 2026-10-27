module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallComp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerNormal

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

theorem tagLieType_notSmall_of_presents
    {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ : Subgroup X}
    (h : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) :
    TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥G₀ := by
  refine ⟨t, n, f, ?_, h.2.2.2⟩
  rintro (rfl | rfl | rfl | rfl) <;>
    exact not_ggPresentsG0_of_placeholder _ (by simp) h

theorem notSmall_or_360_of_step1
    (hC : CompTypeLie2Small)
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A L : Subgroup X} {x : X}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hc1 : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ))
    (hAG₀ : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hpG₀ : p ∣ Nat.card ↥G₀)
    (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hL : CFSG.Assembly.IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set X))) :
    TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥L ∨
      Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
  have hLq : CFSG.Open.IsQuasisimple ↥G₀ := GGTwoSig.isQuasisimple_of_presents hpres
  obtain ⟨tG, rG, eG, htG, hMG⟩ := tagLieType_notSmall_of_presents hpres
  have hInn : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn p A G₀ := by
    rcases RCKU33.innDiagOn_or_derived hp hLq hpG₀ hAN hc1 with h | ⟨lab, hd, hm⟩
    · exact h
    · exfalso
      rcases hd with hg | hg
      · exact CFSG.LocalAnalysis.GLTheoremA.I141F.Ord.card_ne_6048_of_lieModel hMG
          (CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der hg hm)
      · refine CFSG.LocalAnalysis.GLTheoremA.MI.evenLieOrder_ne_ordTits
          (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hMG)
          (fun h => htG (Or.inr (Or.inr (Or.inr h)))) ?_
        rw [← CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hMG]
        exact CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der hg hm
  have hyC : ¬ CentMod p G₀ x := by
    intro h
    have hxc : x ∈ Subgroup.centralizer (G₀ : Set X) :=
      RCKU33.u33_mem_centralizer_of_centMod hp hLq hpG₀ h.1
        (fun l hl => h.2 (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers x)))
    have hxbot : x ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hxA, hxc⟩
    rw [hAG₀] at hxbot
    exact hx1 (Subgroup.mem_bot.1 hxbot)
  exact i141DynkinAt_notSmall_comp hC hp hp2 hLq ⟨tG, rG, eG, htG, hMG⟩ hA hInn hxA hyC
    (CFSG.Assembly.isComponentOf_iff_open.1 hL)

end CFSG.StandardType.RCKSmall
