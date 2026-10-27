module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2Fb
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FbComm
public import CFSG.RankThree.PartTwo.Sec11.Item116R2J3Check
public import CFSG.Sporadic.J3
public import Certificates.Certificate39140
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem j3_commutator_witness :
    ∃ K : Subgroup NativeSporadic.J3, Nat.card K = 3 ^ 5 ∧
      9 < Nat.card {x : ↥(commutator ↥K) // x ^ 3 = 1} := by
  obtain ⟨K, hK, hc⟩ := commTriple_of_check (spec2 80) (fun _ => trivial) j3CommTripleData
    Certificates.certificate39140
  exact ⟨K, hK.trans (by norm_num [j3CommTripleData, j3SylowCentralData]), hc⟩

private theorem factorization_three_j3 : (50232960 : ℕ).factorization 3 = 5 := by
  rw [show (50232960 : ℕ) = 3 ^ 5 * 206720 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem not_isRankTwoByCyclic_sylow_of_witness {P Y : Type} [Group P] [Finite P] [Group Y]
    (e : P ≃* Y) (K : Subgroup Y) (hK : Nat.card K = 3 ^ 5) (hP : (Nat.card P).factorization 3 = 5)
    (hKc : 9 < Nat.card {x : ↥(commutator ↥K) // x ^ 3 = 1}) (T : Sylow 3 P) :
    ¬ IsRankTwoByCyclic ↥(T : Subgroup P) := by
  intro hT
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hKP : Nat.card (K.map e.symm.toMonoidHom) = 3 ^ (Nat.card P).factorization 3 := by
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hK, hP]
  have h1 : IsRankTwoByCyclic ↥(Sylow.ofCard (K.map e.symm.toMonoidHom) hKP : Subgroup P) :=
    IsRankTwoByCyclic.sylow_conj hT
  have h2 : IsRankTwoByCyclic ↥K :=
    IsRankTwoByCyclic.of_mulEquiv
      (Subgroup.equivMapOfInjective K e.symm.toMonoidHom e.symm.injective).symm h1
  exact not_isRankTwoByCyclic_of_commutator_cubeRoots hKc h2

theorem sylowThreeNotRankTwoByCyclicJ3_holds :
    SylowThreeNotRankTwoByCyclicJ3 := by
  intro P _ _ ⟨e⟩ T
  obtain ⟨K, hK, hKc⟩ := j3_commutator_witness
  have hP : (Nat.card P).factorization 3 = 5 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3, factorization_three_j3]
  exact @not_isRankTwoByCyclic_sylow_of_witness P NativeSporadic.J3 _ _ inferInstance e K hK hP hKc T

end CFSG.RankThree.PartTwo.Sec11
