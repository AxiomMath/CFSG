module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Degrees of signed irreducible characters

A signed irreducible character has nonzero integral degree.  This generic
interface packages the positive-degree theorem for an irreducible constituent
with the two possible signs.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The value at the identity of a signed irreducible character is a nonzero
rational integer. -/
public theorem signedIrreducibleCharacter_degree_int
    {G : Type u} [Group G] [Finite G]
    {chi : Section1.ClassFunction G}
    (hchi : Section3.IsSignedIrreducibleCharacter chi) :
    ∃ n : ℤ, n ≠ 0 ∧ chi 1 = (n : ℂ) := by
  rcases hchi with ⟨epsilon, hepsilon, mu, hmu, rfl⟩
  rcases Section12.positive_degree_nat_of_isIrreducibleCharacterOnGroup hmu with
    ⟨m, hmpos, hmdeg⟩
  have hmuOne : mu 1 = (m : ℂ) := by
    simpa [Section1.degree] using hmdeg
  rcases hepsilon with rfl | rfl
  · refine ⟨(m : ℤ), ?_, ?_⟩
    · exact Int.ofNat_ne_zero.2 (Nat.ne_of_gt hmpos)
    · simp [hmuOne]
  · refine ⟨-(m : ℤ), ?_, ?_⟩
    · exact neg_ne_zero.mpr (Int.ofNat_ne_zero.2 (Nat.ne_of_gt hmpos))
    · simp [hmuOne]

end CFSG.GorensteinWalter
