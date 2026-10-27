module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG

namespace FiveTransitive.CyclicElevenCentralizerNine

theorem nine_dvd
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) (hQ : Nat.card Q = 11)
    (hN : 9 ∣ Nat.card (Subgroup.normalizer (Q : Set G))) :
    9 ∣ Nat.card (Subgroup.centralizer (Q : Set G)) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : IsCyclic Q := isCyclic_of_prime_card hQ
  have hAut : Nat.card (MulAut Q) = 10 := by
    rw [IsCyclic.card_mulAut Q,hQ,Nat.totient_prime (by decide)]
  let f := Q.normalizerMonoidHom
  have hd : Nat.card f.range ∣ 10 := hAut ▸ f.range.card_subgroup_dvd_card
  have hc : Nat.Coprime 9 (Nat.card f.range) := (show Nat.Coprime 9 10 by decide).of_dvd_right hd
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  rw [← hm] at hN
  have hk : 9 ∣ Nat.card f.ker := hc.dvd_of_dvd_mul_right hN
  have he : Nat.card f.ker = Nat.card (Subgroup.centralizer (Q : Set G)) := by
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (Q : Set G))).toEquiv
  rwa [he] at hk

end FiveTransitive.CyclicElevenCentralizerNine

end CFSG
