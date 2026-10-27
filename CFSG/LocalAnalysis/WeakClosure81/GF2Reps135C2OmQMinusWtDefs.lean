module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat
public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

@[expose] noncomputable def omqMinusZ (n : ℕ) {K : Type*} [Field K] {b c : K}
    (g : spinGroup (quadMinus n K b c)) : ShortField b c :=
  ⟨mat n g (.inr (.inr 0)) (.inr (.inr 0)), mat n g (.inr (.inr 1)) (.inr (.inr 0))⟩

@[expose] noncomputable def omqMinusWt (n : ℕ) {K : Type*} [Field K] {b c : K} {k : Type*}
    [Field k] {m h : ℕ} (ι : K →+* k) (ι' : ShortField b c →+* k) (ν : OmqMinusLat (n - 1) m h)
    (g : spinGroup (quadMinus n K b c)) : k :=
  (∏ i : Fin (n - 1), ι (mat n g (.inl i) (.inl i)) ^ (ν.1 i).val) *
    ι' (omqMinusZ n g) ^ ν.2.val

end CFSG.LocalAnalysis.WeakClosure81
