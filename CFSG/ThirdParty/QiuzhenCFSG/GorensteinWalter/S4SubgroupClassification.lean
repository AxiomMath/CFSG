module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace CFSG
end CFSG
open CFSG

/-!
# Dihedral-Sylow subgroups of `S₄`

The image of a faithful four-point action is a subgroup of `S₄`.  A dihedral
Sylow `2`-subgroup has order at least four, so Lagrange's theorem leaves only
the orders `4`, `8`, `12`, and `24`.  The first two are `2`-groups; the latter
two are the unique index-two subgroup `A₄` and all of `S₄`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

private lemma card_s4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]

private lemma subgroup_card_dvd_s4 (K : Subgroup (Equiv.Perm (Fin 4))) :
    Nat.card (↥K) ∣ 24 := by
  have h := Subgroup.card_dvd_of_le
    (H := K) (K := (⊤ : Subgroup (Equiv.Perm (Fin 4)))) le_top
  rw [Subgroup.card_top, card_s4] at h
  exact h

private lemma subgroup_card_cases {K : Subgroup (Equiv.Perm (Fin 4))}
    (h4 : 4 ∣ Nat.card (↥K)) (hd : Nat.card (↥K) ∣ 24) :
    Nat.card (↥K) = 4 ∨ Nat.card (↥K) = 8 ∨
      Nat.card (↥K) = 12 ∨ Nat.card (↥K) = 24 := by
  have hpos : 0 < Nat.card (↥K) := Nat.card_pos
  have hle : Nat.card (↥K) ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  rcases h4 with ⟨a, ha⟩
  rcases hd with ⟨b, hb⟩
  interval_cases hc : Nat.card (↥K) <;> norm_num at ha hb ⊢ <;> omega

/-- A subgroup of `S₄` with dihedral Sylow `2`-subgroups is a `2`-group,
`A₄`, or all of `S₄`. -/
public theorem subgroup_S4_dihedral_classification
    {K : Subgroup (Equiv.Perm (Fin 4))}
    (hKd : HasDihedralSylowTwo (↥K)) :
    IsPGroup 2 (↥K) ∨ K = alternatingGroup (Fin 4) ∨ K = ⊤ := by
  let S : Sylow 2 (↥K) := Classical.choice Sylow.nonempty
  rcases hKd S with ⟨m, hm, ⟨eS⟩⟩
  have hScard : Nat.card (↥(S : Subgroup (↥K))) = 2 ^ (m + 1) := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
    rw [pow_succ]
    ring
  have hSdvd : Nat.card (↥(S : Subgroup (↥K))) ∣ Nat.card (↥K) := by
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := (S : Subgroup (↥K)))
        (K := (⊤ : Subgroup (↥K))) le_top)
  have h4S : 4 ∣ Nat.card (↥(S : Subgroup (↥K))) := by
    rw [hScard]
    have hmn : 2 ≤ m + 1 := by omega
    have hpow : 2 ^ 2 ∣ 2 ^ (m + 1) := Nat.pow_dvd_pow 2 hmn
    norm_num at hpow ⊢
    exact hpow
  have h4K : 4 ∣ Nat.card (↥K) := Nat.dvd_trans h4S hSdvd
  have hcases := subgroup_card_cases h4K (subgroup_card_dvd_s4 K)
  rcases hcases with hc4 | hc8 | hc12 | hc24
  · left
    exact IsPGroup.of_card (n := 2) (by simpa using hc4)
  · left
    exact IsPGroup.of_card (n := 3) (by
      calc
        Nat.card (↥K) = 8 := hc8
        _ = 2 ^ 3 := by norm_num)
  · right; left
    have hidx : K.index = 2 := by
      have hi := Subgroup.index_mul_card K
      rw [hc12, card_s4] at hi
      omega
    exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  · right; right
    have hidx : K.index = 1 := by
      have hi := Subgroup.index_mul_card K
      rw [hc24, card_s4] at hi
      omega
    exact Subgroup.index_eq_one.mp hidx

end CFSG.GorensteinWalter
