module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TwoPartArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2SplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2NonsplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicSylow

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral Sylow 2-subgroups of odd `PGL₂`

According to the parity of `(q - 1) / 2`, the full `2`-part lies in the
normalizer of either the split torus of order `q - 1` or the nonsplit torus
of order `q + 1`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every odd-prime-power finite field has a dihedral Sylow `2`-subgroup in
its projective general linear group. -/
public theorem pgl2_odd_hasDihedralSylowTwo_model
    (K : Type u) [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) :
    HasDihedralSylowTwo (PGL2 K) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  rcases hodd with ⟨p, f, hp, hpOdd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hPGLcard : Nat.card (PGL2 K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    pgl2_card_formula K
  have hqOdd : Odd (Nat.card K) := by
    rw [hcard]
    exact hpOdd.pow
  have hqOne : 1 < Nat.card K := Finite.one_lt_card
  have h2sub : 2 ∣ Nat.card K - 1 := by
    rcases hqOdd with ⟨k, hk⟩
    use k
    omega
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hqOdd with ⟨k, hk⟩
    use k + 1
    omega
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · obtain ⟨U, w, hUc, hUcard, hwU, hwsq, hwinv, _hcross⟩ :=
      pgl2_split_torus_reflection_data K
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard]
      exact h2sub
    obtain ⟨D, hm, hdih⟩ :=
      exists_dihedral_two_subgroup_of_cyclic_reflection
        U w hUc hUeven hwU hwsq hwinv
    have hDcard : Nat.card D =
        2 ^ (Nat.card (PGL2 K)).factorization 2 := by
      rcases hdih with ⟨eD⟩
      calc
        Nat.card D = Nat.card (DihedralGroup
            (2 ^ (Nat.card U).factorization 2)) :=
          Nat.card_congr eD.toEquiv
        _ = 2 * 2 ^ (Nat.card U).factorization 2 :=
          DihedralGroup.nat_card
        _ = 2 ^ ((Nat.card U).factorization 2 + 1) := by
          rw [pow_succ, mul_comm]
        _ = 2 ^ (Nat.card (PGL2 K)).factorization 2 := by
          rw [hUcard, hPGLcard,
            pgl2_order_two_factorization_split hqOdd hqOne hsplit]
    let S : Sylow 2 (PGL2 K) := Sylow.ofCard D hDcard
    intro T
    refine ⟨(Nat.card U).factorization 2, hm, ?_⟩
    rcases hdih with ⟨eD⟩
    have eS : (S : Type u) ≃* DihedralGroup
        (2 ^ (Nat.card U).factorization 2) := by
      have hSD : (S : Subgroup (PGL2 K)) = D := by simp [S]
      rw [hSD]
      exact eD
    exact ⟨(Sylow.equiv S T).symm.trans eS⟩
  · obtain ⟨U, w, hUc, hUcard, hwU, hwsq, hwinv, _hcross⟩ :=
      pgl2_nonsplit_torus_reflection_data (F := K) hcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard]
      exact h2plus
    obtain ⟨D, hm, hdih⟩ :=
      exists_dihedral_two_subgroup_of_cyclic_reflection
        U w hUc hUeven hwU hwsq hwinv
    have hDcard : Nat.card D =
        2 ^ (Nat.card (PGL2 K)).factorization 2 := by
      rcases hdih with ⟨eD⟩
      calc
        Nat.card D = Nat.card (DihedralGroup
            (2 ^ (Nat.card U).factorization 2)) :=
          Nat.card_congr eD.toEquiv
        _ = 2 * 2 ^ (Nat.card U).factorization 2 :=
          DihedralGroup.nat_card
        _ = 2 ^ ((Nat.card U).factorization 2 + 1) := by
          rw [pow_succ, mul_comm]
        _ = 2 ^ (Nat.card (PGL2 K)).factorization 2 := by
          rw [hUcard, hPGLcard,
            pgl2_order_two_factorization_nonsplit hqOdd hqOne hnonsplit]
    let S : Sylow 2 (PGL2 K) := Sylow.ofCard D hDcard
    intro T
    refine ⟨(Nat.card U).factorization 2, hm, ?_⟩
    rcases hdih with ⟨eD⟩
    have eS : (S : Type u) ≃* DihedralGroup
        (2 ^ (Nat.card U).factorization 2) := by
      have hSD : (S : Subgroup (PGL2 K)) = D := by simp [S]
      rw [hSD]
      exact eD
    exact ⟨(Sylow.equiv S T).symm.trans eS⟩

end CFSG.GorensteinWalter
