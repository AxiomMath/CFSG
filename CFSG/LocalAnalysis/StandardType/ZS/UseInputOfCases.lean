module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.ZS.Imprimitive
import CFSG.LocalAnalysis.StandardType.ZS.Transvection

public section

namespace CFSG.StandardType.ZS

open CFSG.StandardType.QTwoLin (IsTransvectionLin TransvectionFree)
open CFSG.Quasithin.SimsG4 (IsImprimitiveOnV)

@[expose] def UseInputAt (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 →
      Module.finrank (ZMod p) U = n → ReflGen p A → AbsIrred p A → Family p A

@[expose] def DimThreeCase : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 →
      Module.finrank (ZMod p) U = 3 → ReflGen p A → AbsIrred p A → ¬ IsImprimitiveOnV A →
        Family p A

@[expose] def DThreeCase : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 →
      4 ≤ Module.finrank (ZMod p) U → ReflGen p A → AbsIrred p A → ¬ IsImprimitiveOnV A →
        TransvectionFree A →
          (∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3) → Family p A

@[expose] def DLargeCase : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 →
      (∀ m, 3 ≤ m → m < Module.finrank (ZMod p) U → UseInputAt m) →
      4 ≤ Module.finrank (ZMod p) U → ReflGen p A → AbsIrred p A → ¬ IsImprimitiveOnV A →
        TransvectionFree A →
          (∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) → Family p A

theorem family_of_cases (h3 : DimThreeCase) (hd3 : DThreeCase) {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2) (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hA : AbsIrred p A)
    (hd : 4 ≤ Module.finrank (ZMod p) U → ¬ IsImprimitiveOnV A → TransvectionFree A →
      (∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) → Family p A) :
    Family p A := by
  by_cases ht : ∃ t ∈ A, IsTransvectionLin t
  · exact family_of_transvection hp hn hgen hA ht
  by_cases himp : IsImprimitiveOnV A
  · exact family_of_imprimitive hp hn hgen hA himp
  have htv : TransvectionFree A := fun g hg hg' => ht ⟨g, hg, hg'⟩
  rcases hn.eq_or_lt with hn3 | hn4
  · exact h3 p U A hp hn3.symm hgen hA himp
  by_cases hlarge : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)
  · exact hd hn4 himp htv hlarge
  refine hd3 p U A hp hn4 hgen hA himp htv fun x hx y hy hrx hry => ?_
  exact not_lt.mp fun hxy => hlarge ⟨x, hx, y, hy, hrx, hry, hxy⟩

theorem useInput_of_cases (h3 : DimThreeCase) (hd3 : DThreeCase) (hd : DLargeCase) :
    UseInput := by
  suffices key : ∀ n, 3 ≤ n → UseInputAt n from
    fun p _ U _ _ _ A hp hn hgen hA => key _ hn p U A hp rfl hgen hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn p _ U _ _ _ A hp hU hgen hA
    subst hU
    exact family_of_cases h3 hd3 hp hn hgen hA
      (hd p U A hp (fun m hm hmn => ih m hmn hm) · hgen hA)

end CFSG.StandardType.ZS
