module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03PermModel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Glue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03AltEight
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms

theorem gs03AlphaL4Two_holds :
    GS03AlphaOuterFor fun t n f => t = .PSL ∧ n = 4 ∧ f = 1 := by
  classical
  intro G _ _ S hS hC t n f hR hlie x hx hxS
  obtain ⟨rfl, rfl, rfl⟩ := hR
  haveI : S.Normal := hS
  obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hlie
  have hAGB : AutGenBound (alternatingGroup (Fin 8)) 7
      (fun a => True → a ∉ inner (alternatingGroup (Fin 8))) := by
    refine autGenBound_of_permModel (S := alternatingGroup (Fin 8)) (Ω := Fin 8)
      (alternatingGroup (Fin 8)).subtype (alternatingGroup (Fin 8)).subtype_injective
      ?_ ⊤ le_top ?_ ?_ True ?_
    ·
      intro τ hτ
      apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 8 (by norm_num)
      apply MulEquiv.ext
      intro s
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
      simp only [one_mul, mul_one, inv_one]
      have hs : τ * (s : Equiv.Perm (Fin 8)) = (s : Equiv.Perm (Fin 8)) * τ := by
        simpa only [Subgroup.subtype_apply] using hτ s
      rw [hs]
      simp [mul_assoc]
    ·
      intro g _ s
      rw [Subgroup.range_subtype]
      exact (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem s s.2 g
    ·
      have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
        (by norm_num) (by norm_num)
      have heq : Nat.card (MulAut (alternatingGroup (Fin 8))) =
          Nat.card (Equiv.Perm (Fin 8)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
      rw [Subgroup.card_top]
      exact le_of_eq heq
    ·
      intro g _ hg2 hg1 hgmem
      have hgA : g ∉ alternatingGroup (Fin 8) := by
        have h := hgmem trivial
        rwa [Subgroup.range_subtype] at h
      obtain ⟨s, hs⟩ := gs03_alt8_odd_involution_gen g hg2 hgA
      refine ⟨s, ?_⟩
      rwa [Subgroup.range_subtype]
  obtain ⟨T, hTcard, hTconj, hTgen⟩ :=
    gs03_of_autGenBound hAGB S hC e hx (fun _ => gs03_action_not_inner S hC e hxS)
  exact ⟨T, by simpa [gs03Bound] using hTcard, hTconj, hTgen⟩

end CFSG.LocalAnalysis.WeakClosure81
