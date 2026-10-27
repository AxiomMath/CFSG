module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2TwoPartArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow 2-subgroups of odd `PSL₂`

The split and nonsplit Huppert torus-reflection interfaces supply the two
possible dihedral 2-subgroups.  The only branch choice is which of
`(q - 1) / 2` and `(q + 1) / 2` is even.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki
open BenderSuzuki.External
open BenderSuzuki.MatrixGroups

universe u

private lemma gcd_sub_one_two_of_odd {q : ℕ} (hq : Odd q) :
    Nat.gcd (q - 1) 2 = 2 := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    (Nat.dvd_gcd h2 (dvd_refl 2))

private lemma odd_card_field {K : Type u} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  rcases hodd with ⟨p, n, hp, hpOdd, hn, hcard⟩
  rw [hcard]
  exact hpOdd.pow

private lemma one_lt_card_field {K : Type u} [Field K] [Finite K] :
    1 < Nat.card K :=
  Finite.one_lt_card

/-- Every odd-prime-power finite field has a dihedral Sylow `2`-subgroup in
its projective special linear group. -/
public theorem psl2_odd_hasDihedralSylowTwo_model
    (K : Type u) [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) :
    HasDihedralSylowTwo (PSL2 K) := by
  rcases hodd with ⟨p, f, hp, hpOdd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hoddK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpOdd, hf, hcard⟩
  have hPSLcard : Nat.card (PSL2 K) =
      Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
    psl2_card_formula K hoddK
  have hqOdd : Odd (Nat.card K) := by
    rw [hcard]
    exact hpOdd.pow
  have hqOne : 1 < Nat.card K := one_lt_card_field
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd hqOdd
  have h2sub : 2 ∣ Nat.card K - 1 := by
    rcases hqOdd with ⟨k, hk⟩
    use k
    omega
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hqOdd with ⟨k, hk⟩
    use k + 1
    omega
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · obtain ⟨U, w, hUc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, _hNorm⟩ :=
      huppert_II_8_3_split_torus_reflection_data
        (F := K) (p := p) (f := f) hcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hsplit.two_dvd
    obtain ⟨D, hm, hdih⟩ :=
      exists_dihedral_two_subgroup_of_cyclic_reflection
        U w hUc hUeven hwU hwsq hwinv
    have hDcard : Nat.card D =
        2 ^ (Nat.card (PSL2 K)).factorization 2 := by
      rcases hdih with ⟨eD⟩
      calc
        Nat.card D = Nat.card (DihedralGroup
            (2 ^ (Nat.card U).factorization 2)) :=
          Nat.card_congr eD.toEquiv
        _ = 2 * 2 ^ (Nat.card U).factorization 2 :=
          DihedralGroup.nat_card
        _ = 2 ^ ((Nat.card U).factorization 2 + 1) := by
          rw [pow_succ, mul_comm]
        _ = 2 ^ (Nat.card (PSL2 K)).factorization 2 := by
          rw [hUcard', hPSLcard,
            psl2_order_two_factorization_split hqOdd hqOne hsplit]
    let S : Sylow 2 (PSL2 K) := Sylow.ofCard D hDcard
    intro T
    refine ⟨(Nat.card U).factorization 2, hm, ?_⟩
    rcases hdih with ⟨eD⟩
    have eS : (S : Type u) ≃* DihedralGroup
        (2 ^ (Nat.card U).factorization 2) := by
      have hSD : (S : Subgroup (PSL2 K)) = D := by simp [S]
      rw [hSD]
      exact eD
    exact ⟨(Sylow.equiv S T).symm.trans eS⟩
  · obtain ⟨S0, w, hSc, hScard, _hwN, hwS, hwsq, hwinv, _hDcard, _hNorm⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data
        (F := K) (p := p) (f := f) hcard
    have hScard' : Nat.card S0 = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hScard
    have hSeven : Even ((Nat.card K + 1) / 2) := by
      rcases hnonsplit with ⟨k, hk⟩
      use k + 1
      omega
    have hSevenDvd : 2 ∣ Nat.card S0 := by
      rw [hScard']
      exact hSeven.two_dvd
    obtain ⟨D, hm, hdih⟩ :=
      exists_dihedral_two_subgroup_of_cyclic_reflection
        S0 w hSc hSevenDvd hwS hwsq hwinv
    have hDcard : Nat.card D =
        2 ^ (Nat.card (PSL2 K)).factorization 2 := by
      rcases hdih with ⟨eD⟩
      calc
        Nat.card D = Nat.card (DihedralGroup
            (2 ^ (Nat.card S0).factorization 2)) :=
          Nat.card_congr eD.toEquiv
        _ = 2 * 2 ^ (Nat.card S0).factorization 2 :=
          DihedralGroup.nat_card
        _ = 2 ^ ((Nat.card S0).factorization 2 + 1) := by
          rw [pow_succ, mul_comm]
        _ = 2 ^ (Nat.card (PSL2 K)).factorization 2 := by
          rw [hScard', hPSLcard,
            psl2_order_two_factorization_nonsplit hqOdd hqOne hnonsplit]
    let S : Sylow 2 (PSL2 K) := Sylow.ofCard D hDcard
    intro T
    refine ⟨(Nat.card S0).factorization 2, hm, ?_⟩
    rcases hdih with ⟨eD⟩
    have eS : (S : Type u) ≃* DihedralGroup
        (2 ^ (Nat.card S0).factorization 2) := by
      have hSD : (S : Subgroup (PSL2 K)) = D := by simp [S]
      rw [hSD]
      exact eD
    exact ⟨(Sylow.equiv S T).symm.trans eS⟩

end CFSG.GorensteinWalter
