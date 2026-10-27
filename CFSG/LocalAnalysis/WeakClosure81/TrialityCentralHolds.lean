module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriality
import CFSG.LocalAnalysis.WeakClosure81.TrialityCentralProof

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadPlus)


theorem trialityCentralInput_holds : TrialityCentralInput := by
  rintro X _ _ s hs hncl hZodd ⟨ε, hT⟩
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨f, ⟨-, hf, -⟩, F, _, _, hF, ⟨φ⟩⟩ := exists_statedClassicalModel_ker_of_trialityData hT
  obtain ⟨hperfS, hmult⟩ := commutator_eq_top_and_card_hopfMultiplier_dvd_four hf hF
  have hKbar : ⁅ε.ker, ε.ker⁆ = ε.ker := by
    have : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus 4 F))) := ⟨hperfS⟩
    exact Subgroup.isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
  obtain ⟨D, hDn, hDmap, hKD, hDperf⟩ := exists_perfect_of_comap
    (QuotientGroup.mk'_surjective (Subgroup.center X)) (QuotientGroup.ker_mk' _) hKbar
  have hDK : ∀ d ∈ D, QuotientGroup.mk' (Subgroup.center X) d ∈ ε.ker := fun d hd => by
    rw [← hDmap]
    exact ⟨d, hd, rfl⟩
  have hDZ := inf_center_eq_bot_of_hopfMultiplier hZodd hmult hDperf
    (φ.toMonoidHom.comp (((QuotientGroup.mk' (Subgroup.center X)).comp D.subtype).codRestrict
      ε.ker fun d => hDK d d.2))
    (by
      intro y
      obtain ⟨⟨k, hk⟩, rfl⟩ := φ.surjective y
      obtain ⟨d, hd, rfl⟩ : k ∈ D.map (QuotientGroup.mk' (Subgroup.center X)) := hDmap.symm ▸ hk
      exact ⟨⟨d, hd⟩, rfl⟩)
    (fun d => by
      show φ _ = 1 ↔ _
      rw [map_eq_one_iff _ φ.injective, ← Subtype.coe_inj]
      exact QuotientGroup.eq_one_iff _)
  exact center_eq_bot_of_perm_three (ρ := ε.comp (QuotientGroup.mk' (Subgroup.center X))) hs2
    hncl hZodd hT.isSwap (fun d hd => hDK d hd) (fun x hx => hKD x hx) hDZ

end CFSG.LocalAnalysis.WeakClosure81
