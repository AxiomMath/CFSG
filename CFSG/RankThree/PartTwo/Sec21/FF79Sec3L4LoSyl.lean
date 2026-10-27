module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem sylow3_cyclic_of_order9 {L : Type} [Group L] [Finite L] (g : L) (hg : orderOf g = 9)
    (h27 : ¬ 27 ∣ Nat.card L) (S : Subgroup L) (hS : IsSylowOf 3 S ⊤) :
    IsCyclic S ∧ Nat.card S = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hcop⟩ := hS
  rw [Subgroup.relIndex_top_right] at hcop
  have hndvd : ¬ 3 ∣ S.index := fun hd => by
    have := Nat.Coprime.eq_one_of_dvd hcop hd
    omega
  let P : Sylow 3 L := hp.toSylow hndvd
  have hPS : (P : Subgroup L) = S := rfl
  have hcard : Nat.card S = 3 ^ (Nat.card L).factorization 3 := by
    rw [← hPS]; exact P.card_eq_multiplicity
  have h9 : 9 ∣ Nat.card L := hg ▸ orderOf_dvd_natCard g
  have hfac : (Nat.card L).factorization 3 = 2 := by
    have hpos : Nat.card L ≠ 0 := Nat.card_pos.ne'
    have hge : 2 ≤ (Nat.card L).factorization 3 := by
      have : 3 ^ 2 ∣ Nat.card L := by simpa using h9
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 this
    by_contra hne
    have : 3 ^ 3 ∣ Nat.card L :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 (by omega)
    exact h27 (by simpa using this)
  rw [hfac] at hcard
  refine ⟨?_, by simpa using hcard⟩
  have hpg : IsPGroup 3 (Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hg]; norm_num
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup L) = 9 := by
    have := Q.card_eq_multiplicity
    rw [hfac] at this; simpa using this
  have hzc : Nat.card (Subgroup.zpowers g) = 9 := by rw [Nat.card_zpowers, hg]
  have hQeq : Subgroup.zpowers g = (Q : Subgroup L) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard, hzc])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq L Q P
  have hSeq : (P : Subgroup L) = (Subgroup.zpowers g).map (MulAut.conj c).toMonoidHom := by
    rw [hQeq]
    have : ((c • Q : Sylow 3 L) : Subgroup L) =
        (Q : Subgroup L).map (MulAut.conj c).toMonoidHom := by
      rfl
    rw [← this, hc]
  rw [hPS] at hSeq
  rw [hSeq]
  have : IsCyclic (Subgroup.zpowers g) := inferInstance
  exact isCyclic_of_surjective
    (((Subgroup.zpowers g).equivMapOfInjective _ (MulAut.conj c).injective).toMonoidHom.comp
      (MonoidHom.id _)) (MulEquiv.surjective _) 

end CFSG.RankThree.PartTwo.Sec21.FF79
