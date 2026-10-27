module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Congruence
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Integrality
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility

namespace CFSG
end CFSG
open CFSG

/-!
# BG class-sum even parity

For an irreducible representation whose degree is odd, the scalar by which a
conjugacy-class sum acts is congruent to zero modulo two whenever the class
size is even.
-/

noncomputable section

namespace CFSG.BenderGlauberman

open Theory.Character

attribute [local instance] Fintype.ofFinite

/-- The class-sum scalar for an odd-degree irreducible representation is
congruent to zero modulo two when the conjugacy class has even size. -/
public theorem classSumScalar_congruent_zero_of_odd_degree_and_even_class
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho] (g : G)
    (hdegree : Odd (Module.finrank ℂ V))
    (hclass : Even (Nat.card (ConjClasses.mk g).carrier)) :
    CongruentModTwo
      (Theory.Character.classSumScalar (ρ := rho) (ConjClasses.mk g)) 0 := by
  classical
  let s : ℂ := classSumScalar (ρ := rho) (ConjClasses.mk g)
  let n : ℕ := Module.finrank ℂ V
  let m : ℕ := Nat.card (ConjClasses.mk g).carrier
  have hsc := classSumScalar_eq_card_mul_character_div (ρ := rho) (ConjClasses.mk g)
    (x := g) ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  have hchar1 : rho.character 1 = (n : ℂ) := by
    simp [n, Representation.character]
  have hn_ne : (n : ℂ) ≠ 0 := by
    change Odd n at hdegree
    rcases hdegree with ⟨k, hk⟩
    rw [hk]
    exact_mod_cast Nat.succ_ne_zero (2 * k)
  have hEq : (n : ℂ) * s = (m : ℂ) * rho.character g := by
    dsimp [s]
    rw [hsc, hchar1]
    field_simp [hn_ne]
    ring
  have hEvenCongr : CongruentModTwo ((m : ℂ) * rho.character g) 0 := by
    change Even m at hclass
    rcases hclass with ⟨k, hk⟩
    rw [hk]
    have hkχint : IsIntegral ℤ ((k : ℂ) * rho.character g) :=
      (isIntegral_natCast k).mul (character_value_isIntegral rho g)
    simpa [Nat.cast_add, add_mul, two_mul, mul_assoc] using
      CongruentModTwo.two_mul_zero hkχint
  have hMain : CongruentModTwo ((n : ℂ) * s) 0 :=
    (CongruentModTwo.of_eq hEq).trans hEvenCongr
  have hOddCongr : CongruentModTwo ((n : ℂ) * s) s :=
    CongruentModTwo.odd_mul_congr (n := n) hdegree
      (classSumScalar_isIntegral (ρ := rho) (ConjClasses.mk g))
  change CongruentModTwo s 0
  exact hOddCongr.symm.trans hMain

end CFSG.BenderGlauberman
