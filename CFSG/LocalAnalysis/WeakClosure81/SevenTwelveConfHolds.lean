module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfLift
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpMain
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfPSU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem spURootConfiguration_holds : SpURootConfiguration := by
  intro X _ _ m n t hn hpc ht hgen hroot
  have hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp => by
    have h : N ≤ CFSG.pCore 2 X := le_sSup ⟨hN, hp⟩
    rw [hpc] at h
    exact le_bot_iff.mp h
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center hO2
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
    QuotientGroup.ker_mk' _
  have key : ∃ (g₂ g₃ y : X ⧸ Subgroup.center X) (W T : Subgroup (X ⧸ Subgroup.center X)),
      SevenTwelveConfig (Subgroup.zpowers (QuotientGroup.mk t : X ⧸ Subgroup.center X))
        g₂ g₃ y W T := by
    rcases hroot with ⟨k, -, F, _, _, hF, e, he⟩ | ⟨F, _, _, hF, e, he⟩
    · obtain ⟨g₂, g₃, y, W, T, h⟩ := exists_sevenTwelveConfig_statedSp hF hn he
      have hsq : e (QuotientGroup.mk t) * e (QuotientGroup.mk t) = 1 := by
        rw [← map_mul, ← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one, map_one]
      have h' := sevenTwelveConfig_mulEquiv e.symm hsq h
      rw [MulEquiv.symm_apply_apply] at h'
      exact ⟨_, _, _, _, _, h'⟩
    · obtain ⟨g₂, g₃, y, W, T, h⟩ := exists_sevenTwelveConfig_statedProj hF hn he
      have hsq : e (QuotientGroup.mk t) * e (QuotientGroup.mk t) = 1 := by
        rw [← map_mul, ← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one, map_one]
      have h' := sevenTwelveConfig_mulEquiv e.symm hsq h
      rw [MulEquiv.symm_apply_apply] at h'
      exact ⟨_, _, _, _, _, h'⟩
  obtain ⟨g₂, g₃, y, W, T, h⟩ := key
  have hodd' : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker) := by
    rw [hker]
    exact hodd
  exact sevenTwelveConfig_lift (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) hker.le hodd' ht hgen h

end CFSG.LocalAnalysis.WeakClosure81

end
