module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModFixNative
import CFSG.Certificates.Kernel.Cnum.XorCols

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open CFSG.Sporadic.J4.QT CFSG.Certificates.Kernel.Cnum

private theorem act_xor (ℓ : Int) (a b : Nat) : act ℓ (a ^^^ b) = act ℓ a ^^^ act ℓ b := by
  unfold act rowsXor
  exact foldl_xor0 _ _ _ _

private theorem word_xor : ∀ (s : List Int) (a b : Nat),
    s.foldr act (a ^^^ b) = s.foldr act a ^^^ s.foldr act b
  | [], _, _ => rfl
  | ℓ :: s, a, b => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, word_xor s, act_xor]

private theorem band_congr_right {a b c : Bool} (h : b = c) : (a && b) = (a && c) := h ▸ rfl

private def wc (s : List Int) (i : Nat) : Nat := s.foldr act (2 ^ i)

private theorem root_eq (r : Nat) : chkFixRoot r =
    ((fixWords r).all (fun s => s.all (fun ℓ => letters.contains ℓ) && s.foldr act r == r) &&
      (List.range 2048).all fun d =>
        (fixWords r).all (fun s => decide (ca (wc s) d 11 0 < 2048)) &&
          (!(fixWords r).all (fun s => ca (wc s) d 11 0 == d) || d == 0 || d == r)) := by
  unfold chkFixRoot
  refine band_congr_right (all_congr' fun d hd => ?_)
  have hd' : d < 2 ^ 11 := by
    show d < 2048
    exact List.mem_range.1 hd
  have key : ∀ s : List Int, s.foldr act d = ca (wc s) d 11 0 :=
    fun s => lin_eq (g := fun x => s.foldr act x) (word_xor s) hd'
  simp only [key]

private theorem chkFix_true : chkFix = true := by
  unfold chkFix
  rw [root_eq, root_eq]
  decide +kernel

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace Certificates

open CFSG.EvenSporadicStandard.J4Std.DataMod in
theorem certificate25140 : chkFix = true :=
  CFSG.EvenSporadicStandard.J4Std.DataMod.chkFix_true

end Certificates
