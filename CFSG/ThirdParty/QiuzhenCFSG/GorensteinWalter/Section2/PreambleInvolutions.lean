module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample

namespace CFSG
end CFSG
open CFSG

/-!
# Involution conjugacy for the Section 2 preamble

The preamble recalls that every involution of the minimal counterexample is
conjugate.  The local assembly is a short consequence of the translated
Gorenstein--Walter Lemma 2.1: simplicity excludes its index-two branch, and
its normal-`2`-complement branch contradicts minimality.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- All involutions of a minimal counterexample are conjugate.  This theorem
contains the local deduction from `minimalCounterexample_isSimple` and
`gw_lemma_2_1`; those two source interfaces remain the upstream classification
dependencies. -/
public theorem fact_2_preamble_involutions_conjugate_proved
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y := by
  classical
  obtain ⟨S⟩ := (Sylow.nonempty (p := 2) (G := G))
  rcases hmin.1 S with ⟨m, hm, e⟩
  have hcardS : Nat.card (↥(S : Subgroup G)) = 2 * 2 ^ m := by
    calc
      Nat.card (↥(S : Subgroup G)) = Nat.card (DihedralGroup (2 ^ m)) :=
        Nat.card_congr e.some.toEquiv
      _ = 2 * 2 ^ m := DihedralGroup.nat_card
  have hpow : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hcardS4 : 4 ≤ Nat.card (↥(S : Subgroup G)) := by
    rw [hcardS]
    omega
  have hcardSG : Nat.card (↥(S : Subgroup G)) ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ (S : Subgroup G).subtype_injective
  have hcardG4 : 4 ≤ Nat.card G := hcardS4.trans hcardSG
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hnoIndexTwo : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
    rintro ⟨N, hNnormal, hNindex⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple N hNnormal with hNbot | hNtop
    · rw [hNbot, Subgroup.index_bot] at hNindex
      omega
    · rw [hNtop, Subgroup.index_top] at hNindex
      omega
  rcases gw_lemma_2_1 hmin.1 with hfirst | hsecond | hthird
  · exact hfirst.2.1
  · exact False.elim (hnoIndexTwo hsecond.1)
  · exact False.elim (hmin.2.1
      (gw_prop9_normalTwoComplement_isDGroup hmin hthird.2))

end CFSG.GorensteinWalter
