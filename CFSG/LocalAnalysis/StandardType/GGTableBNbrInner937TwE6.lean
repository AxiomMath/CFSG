module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSCrComp
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TwE6

theorem largeEvenLabelAll_torusNbrSCrComp_twE6 (hKG : GGNbrKGTwE6ThreeSubSCWeylIrred)
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGNbrInner937TwE6Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCrComp p r R I := by
  obtain ⟨ht, rfl, hd⟩ := h
  have hn : 1 ≤ lab.n := hlab.1
  have h3 : ¬ 3 ∣ 2 ^ lab.n + 1 := by
    have hpos : 0 < 2 ^ lab.n := Nat.two_pow_pos lab.n
    intro h3'
    have h2 : 3 ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h3' hd
    have h2' : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
    rw [h2'] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)
  have hlift := largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_three (by norm_num) hlab ⟨ht, hd⟩
  have hT : LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSCrComp 3 4 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK =>
      ggTorusNbrSCrComp_of_ggTorusNbrSCr
        (ggTorusNbrSCr_of_scWeylIrred Nat.prime_three (TwE6Delta.center_recipeR_eq_bot hn hK)
          (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3 hφ)
          (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3) (hKG K lab.n hn hK hd))
  exact (largeEvenLabelAll_and hlift hT).mono fun _ _ _ _ ⟨hl, hs⟩ => ⟨4, hl, hs⟩

theorem ggTableBNbrInnerInputOn_937TwE6 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hKG : GGNbrKGTwE6ThreeSubSCWeylIrred) : GGTableBNbrInnerInputOn GGNbrInner937TwE6Label :=
  ggTableBNbrInnerInputOn_of_labelsSCrComp hL hPJ fun _ _ _ hlab h =>
    largeEvenLabelAll_torusNbrSCrComp_twE6 hKG hlab h

end TwE6

end CFSG.StandardType

end
