module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddTools
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup
open CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)

section Fam3


namespace FamOdd

theorem ree27_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group) (h : KF135Hyp S p P x u V) :
    False := by
  have hK : Nat.card (GaloisField 3 (2 * 1 + 1)) = 3 ^ (2 * 1 + 1) :=
    GaloisField.card 3 (2 * 1 + 1) (by norm_num)
  haveI : CharP (GaloisField 3 (2 * 1 + 1)) ReeTag.G2.prime :=
    inferInstanceAs (CharP (GaloisField 3 (2 * 1 + 1)) 3)
  obtain ⟨ψ⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.nonempty_reeGamma_equiv hr hK
  set e := φ.trans ψ
  have hcard : Nat.card S = 2 ^ 3 * 3 ^ 9 * 63973 := by
    rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq hK]
    norm_num
  obtain ⟨-, -, hFbar, ⟨R, -, -, -, -, hR3, hcompl⟩, -, -⟩ :=
    small_Ree_outer_three_kernel_field_complement 1 le_rfl (GaloisField 3 (2 * 1 + 1)) hK
  haveI : Finite (ReeTag.G2.reeGamma (GaloisField 3 (2 * 1 + 1)) 1) :=
    Finite.of_equiv S e.toEquiv
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR3
  have hout : Nat.card (Outer S) = 3 ^ (k + 1) := by
    rw [Nat.card_congr (equivalence e).toEquiv, ← hcompl.card_mul_card, hk, hFbar, pow_succ]
  refine false_of_not_dvd_card h fun h3 => ?_
  have heq : Nat.card (Outer S) * Nat.card S = 2 ^ 3 * 3 ^ (k + 10) * 63973 := by
    rw [hout, hcard]
    ring
  rw [heq] at h3
  have h1 := pow_three_dvd_of_dvd_mul h.prime (by linarith [h.seven_le]) h3
  have h2 : p ^ 3 ≤ 63973 := Nat.le_of_dvd (by norm_num) h1
  have h4 : p < 40 := by
    by_contra hge
    have : 40 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (not_lt.1 hge) 3
    omega
  have h7 := h.seven_le
  interval_cases p <;> norm_num at h1

end FamOdd

theorem kF135At_fam3 : KF135At Fam3 := by
  intro S _ _ p P x u V hF h
  obtain ⟨hr, ⟨φ⟩⟩ := hF
  exact (FamOdd.ree27_hyp_false hr φ h).elim

end Fam3

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
