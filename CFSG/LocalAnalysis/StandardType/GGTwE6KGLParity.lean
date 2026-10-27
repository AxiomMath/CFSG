module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem three_dvd_two_pow_add_one_or_sub_one (n : ℕ) : 3 ∣ 2 ^ n + 1 ∨ 3 ∣ 2 ^ n - 1 := by
  have h : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
    induction n with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> omega
  omega

private theorem largeEvenLabelAll_trivial (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun _ _ _ _ => True := fun _ h =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq, trivial⟩) h

theorem ggTwE6OfOutsideAt_twE6 {lab : LargeEvenLabel} (htag : lab.tag = .twE6)
    (h3 : 3 ∣ 2 ^ lab.n + 1) : GGTwE6OfOutsideAt lab :=
  (largeEvenLabelAll_trivial lab).mono fun _ _ _ _ _ => by intros; exact Or.inl ⟨htag, h3⟩

theorem ggTwE6A5LAt_twE6 {lab : LargeEvenLabel} (htag : lab.tag = .twE6)
    (h3 : 3 ∣ 2 ^ lab.n + 1) : GGTwE6A5LAt lab :=
  (largeEvenLabelAll_trivial lab).mono fun _ _ _ _ _ => by
    intros; exact Or.inr (Or.inl ⟨htag, h3⟩)

end CFSG.StandardType.SCFourCover

end
