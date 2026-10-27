module

public import CFSG.Permutation.FiveTransitive.A9SevenFreeOrbitImage

public section

namespace CFSG

namespace FiveTransitive.A9SevenFreeLargeLabels
open A9PrimeFreeOrbitImage

theorem exists_seven
    {L F E : Type} [Group L] [Finite L]
    [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 14)
    (rho : L →* Equiv.Perm F) (hAlt : alternatingGroup F ≤ rho.range)
    (sigma : L →* Equiv.Perm E) (hfree : ¬ 7 ∣ Nat.card sigma.ker)
    (hsupport : ∀ (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F),
      Function.Surjective tau → ∀ b : B, orderOf b = 7 → b.val.support.card ≤ 7) :
    ∃ n : AltPreimage rho, orderOf n = 7 ∧
      7 ≤ Nat.card (Function.fixedPoints (labelHom rho sigma n)) := by
  classical
  obtain ⟨tau,htau,_⟩ := A9SevenFreeOrbitImage.exists_surjective_factor hF rho hAlt sigma hfree
  obtain ⟨n,hn,hnlabel⟩ := A9SevenFreeOrbitImage.exists_seven_with_label_order hF rho hAlt sigma hfree
  let B := (labelHom rho sigma).range
  let b : B := (labelHom rho sigma).rangeRestrict n
  have hb : orderOf b = 7 := (Subgroup.orderOf_coe b).symm.trans hnlabel
  have hs := hsupport B tau htau b hb
  have hfixed : 7 ≤ Nat.card (Function.fixedPoints b.val) := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,b.val.sum_cycleType,
      ← Nat.card_eq_fintype_card,hE]
    omega
  exact ⟨n,hn,hfixed⟩

end FiveTransitive.A9SevenFreeLargeLabels

end CFSG
