module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.StandardType

theorem ggRC_perm_not_monomial {N m : ℕ} (hN : 5 ≤ N) (hm : m < N)
    (π : Equiv.Perm (Fin N) →* Equiv.Perm (Fin m)) (hker : IsMulCommutative π.ker) : False := by
  have hcardN : 5 ≤ Nat.card (Fin N) := by rw [Nat.card_fin]; exact hN
  have hKbot : π.ker = ⊥ := by
    by_contra hne
    haveI : π.ker.Normal := π.normal_ker
    have hnt : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot π.ker).mpr hne
    have hAle : alternatingGroup (Fin N) ≤ π.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal hcardN hnt
    have hcomm : ∀ a b : π.ker, a * b = b * a := isMulCommutative_iff.mp hker
    haveI hAcomm : IsMulCommutative (alternatingGroup (Fin N)) :=
      isMulCommutative_iff.mpr fun a b => by
        apply Subtype.ext
        exact congrArg (Subtype.val : π.ker → Equiv.Perm (Fin N))
          (hcomm ⟨a, hAle a.2⟩ ⟨b, hAle b.2⟩)
    have hle3 : Nat.card (Fin N) ≤ 3 :=
      (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin N)).mp hAcomm
    rw [Nat.card_fin] at hle3
    omega
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hKbot
  have hcard : Nat.card (Equiv.Perm (Fin N)) ≤ Nat.card (Equiv.Perm (Fin m)) :=
    Nat.card_le_card_of_injective π hinj
  rw [Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin] at hcard
  have hlt : Nat.factorial m < Nat.factorial N := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have : Nat.factorial 1 < Nat.factorial N :=
        Nat.factorial_lt_of_lt (by norm_num) (by omega)
      simpa using this
    · exact Nat.factorial_lt_of_lt hmpos hm
  omega

end CFSG.StandardType
