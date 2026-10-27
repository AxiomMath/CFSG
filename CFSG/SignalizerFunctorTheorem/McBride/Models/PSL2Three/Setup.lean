module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.A4
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Arithmetic
import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Open.SignalizerFunctorDefs

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

open CFSG.SignalizerFunctorTheorem.NearModels CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

variable {p : ℕ}

theorem odd_of_coprime (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p))) : Odd p :=
  odd_of_coprime_natCard_psl2 _ hp hcop

theorem three_le_of_odd (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have := hp.two_le
  obtain ⟨k, hk⟩ := hodd
  omega

theorem isSimpleGroup_of_prime (hp : p.Prime) : IsSimpleGroup PSL(2, GaloisField 3 p) := by
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [GaloisField.card 3 p hp.ne_zero]
  calc 4 ≤ 3 ^ 2 := by norm_num
    _ ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le

theorem card_psl2 (hp : p.Prime) :
    Nat.card PSL(2, GaloisField 3 p) = 3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 := by
  rw [CFSG.GorensteinWalter.psl2_card_formula _
    (CFSG.Walter.isOddPrimePower_of_card (GaloisField.card 3 p hp.ne_zero) (by decide)
      hp.pos), GaloisField.card 3 p hp.ne_zero]

theorem card_sylow_two (hp : p.Prime) (hodd : Odd p) (P : Sylow 2 PSL(2, GaloisField 3 p)) :
    Nat.card P = 4 :=
  CFSG.Walter.psl2_sylow_two_card_eq_four _ (GaloisField.card 3 p hp.ne_zero) (by decide) hp.pos
    (Or.inl (three_pow_mod_eight hodd)) P

theorem isA4_fixed (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 3 p)))
    (f : MulAut PSL(2, GaloisField 3 p)) (hf : orderOf f = p) :
    IsA4Subgroup (signalizerFixedSubgroup f) := by
  obtain ⟨e⟩ := psl2_fixedSubgroup_mulEquiv 3 hp hcop f hf
  exact IsA4Subgroup.of_equiv (e.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup)

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
