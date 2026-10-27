module

public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Main
public import CFSG.Permutation.UnitaryThreeRecognition.MainOne
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQUniform

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

theorem statedClassicalModel_of_coordHyp_three {G Ω : Type} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) {Q : Subgroup G} {a b : Ω} {j s : G} {p f d : ℕ}
    (S : StdHyp G Q a b j s p f d) (hQ1 : Q ≠ ⊥) {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hconj : ∀ x : K, J.conj x = x ^ (p ^ f))
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) {φ : Q ≃* Coord J}
    (C : CoordHyp Q a b j J φ) (h3 : 3 ∣ p ^ f + 1) {g : G} (hg : s = g⁻¹ * j * g) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  obtain ⟨s', hs'2, hs'a, hs'⟩ := C.exists_point_weyl_of_three S hK hconj h3 hg
  exact S.root.statedClassicalModel_of_sMap_eq_weyl h2 hQ1 S.hb hs'a hs'2 p f S.hpp S.hpodd S.hf
    J hJ hK hfix φ hs'

theorem statedClassicalModel_of_stdHyp_three
    {G Ω : Type} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G Ω] [Finite Ω] (h2 : IsMultiplyPretransitive G Ω 2)
    {Q : Subgroup G} {a b : Ω} {j s : G} {p f : ℕ}
    (S : StdHyp G Q a b j s p f (Nat.gcd (p ^ f + 1) 3)) (hd3 : Nat.gcd (p ^ f + 1) 3 = 3)
    (hcyc : IsCyclic (pairStab G a b)) {g : G} (hg : s = g⁻¹ * j * g) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  have := faithfulSMul_of_stdHyp S
  have hnonab := S.exists_not_commute rfl hcyc
  obtain ⟨K, _, _, J, hK, hJ, hconj, hfix⟩ := exists_unitaryModelField p f S.hpp S.hf
  obtain ⟨φ, C⟩ := heis_coordHyp S hnonab J hJ hK hconj
  have h3 : 3 ∣ p ^ f + 1 := by rw [← hd3]; exact Nat.gcd_dvd_left _ _
  exact statedClassicalModel_of_coordHyp_three h2 S (ne_bot_of_stdHyp S) J hJ hK hconj hfix C h3
    hg

end CFSG.UnitaryThreeRecognition
