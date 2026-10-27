module

public import CFSG.Permutation.FiveTransitive.TransferFourTransitiveObstruction

public section

namespace CFSG

namespace FiveTransitive.Degree52SeventeenTransferCore

open MulAction Subgroup

private theorem normalizer_centralizes
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (hS : Nat.card S = 17)
    (hN : Nat.card (normalizer (S : Set G)) = 17 ∨
      Nat.card (normalizer (S : Set G)) = 51) :
    normalizer (S : Set G) ≤ centralizer (S : Set G) := by
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  have ha : Nat.card (MulAut S) = 16 := by
    rw [IsCyclic.card_mulAut S,hS,Nat.totient_prime (by decide)]
  have hd16 : Nat.card S.normalizerMonoidHom.range ∣ 16 := by
    rw [← ha]
    exact Subgroup.card_subgroup_dvd_card _
  have hdN := Subgroup.card_range_dvd S.normalizerMonoidHom
  have hdone : Nat.card S.normalizerMonoidHom.range ∣ 1 := by
    rcases hN with hN | hN
    · rw [hN] at hdN
      simpa using Nat.dvd_gcd hd16 hdN
    · rw [hN] at hdN
      simpa using Nat.dvd_gcd hd16 hdN
  have hrange : S.normalizerMonoidHom.range = ⊥ :=
    Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_one hdone)
  intro g hg
  have hmem : S.normalizerMonoidHom ⟨g,hg⟩ ∈ S.normalizerMonoidHom.range := ⟨⟨g,hg⟩,rfl⟩
  rw [hrange,Subgroup.mem_bot] at hmem
  have hk : (⟨g,hg⟩ : normalizer (S : Set G)) ∈ S.normalizerMonoidHom.ker := hmem
  rw [S.normalizerMonoidHom_ker] at hk
  exact hk

theorem excluded_of_normalizer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 17 P) (hS : Nat.card S = 17)
    (hN : Nat.card (normalizer (S : Set P)) = 17 ∨
      Nat.card (normalizer (S : Set P)) = 51) : False := by
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hd := descFactorial_dvd_card_of_isMultiplyPretransitive P X 5 (by omega) h5
  rw [hcard] at hd
  have hle := Nat.le_of_dvd Nat.card_pos hd
  apply TransferFourTransitiveObstruction.false_of_centralizing_sylow P (by omega) h5 hnotAlt S
  · rw [hS]
    norm_num [Nat.descFactorial] at hle
    omega
  · rw [hcard]
    norm_num [Nat.descFactorial]
  · exact normalizer_centralizes (S : Subgroup P) hS hN

end FiveTransitive.Degree52SeventeenTransferCore

end CFSG
