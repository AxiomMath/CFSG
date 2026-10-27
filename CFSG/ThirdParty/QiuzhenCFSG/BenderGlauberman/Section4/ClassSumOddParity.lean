module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Congruence
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 4 — odd class-sum parity

For an irreducible representation `rho`, the class-sum scalar
`classSumScalar` equals `|C| * rho.character g / rho.character 1`.  When
both the degree and the conjugacy-class size are odd, this scalar is
congruent modulo two to `rho.character g`.
-/

noncomputable section

namespace CFSG.BenderGlauberman

open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- If the degree of an irreducible representation and the size of a
conjugacy class are odd, then the corresponding class-sum scalar is
congruent modulo two to the character value. -/
public theorem classSumScalar_congruent_character_of_odd_degree_and_class
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho] (g : G)
    (hdegree : Odd (Module.finrank ℂ V))
    (hclass : Odd (Nat.card (ConjClasses.mk g).carrier)) :
    CongruentModTwo
      (Theory.Character.classSumScalar (ρ := rho) (ConjClasses.mk g))
      (rho.character g) := by
  classical
  have hsc := classSumScalar_eq_card_mul_character_div (ρ := rho) (ConjClasses.mk g)
    (x := g) ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  have hdegne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Odd.pos hdegree))
  have hchar1 : rho.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  have hmain :
      classSumScalar (ρ := rho) (ConjClasses.mk g) * (Module.finrank ℂ V : ℂ) =
        (Nat.card (ConjClasses.mk g).carrier : ℂ) * rho.character g := by
    rw [hsc, hchar1]
    field_simp [hdegne]
  have hscInt : IsIntegral ℤ (classSumScalar (ρ := rho) (ConjClasses.mk g)) :=
    classSumScalar_isIntegral (ρ := rho) (ConjClasses.mk g)
  have hcharInt : IsIntegral ℤ (rho.character g) :=
    representation_character_isIntegral rho g
  have hdegCong : CongruentModTwo
      ((Module.finrank ℂ V : ℂ) * classSumScalar (ρ := rho) (ConjClasses.mk g))
      (classSumScalar (ρ := rho) (ConjClasses.mk g)) :=
    CongruentModTwo.odd_mul_congr hdegree hscInt
  have hclassCong : CongruentModTwo
      ((Nat.card (ConjClasses.mk g).carrier : ℂ) * rho.character g)
      (rho.character g) :=
    CongruentModTwo.odd_mul_congr hclass hcharInt
  have heqCong : CongruentModTwo
      ((Module.finrank ℂ V : ℂ) * classSumScalar (ρ := rho) (ConjClasses.mk g))
      ((Nat.card (ConjClasses.mk g).carrier : ℂ) * rho.character g) := by
    apply CongruentModTwo.of_eq
    simpa [mul_comm] using hmain
  exact (CongruentModTwo.symm hdegCong).trans (heqCong.trans hclassCong)

end CFSG.BenderGlauberman
