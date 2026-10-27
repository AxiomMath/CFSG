module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Equiv

namespace Item211Res3Proof

theorem not_three_dvd_card_of_isPGroup_two {M : Type*} [Group M] [Finite M] {T : Subgroup M}
    (hT : IsPGroup 2 T) : ¬ 3 ∣ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  rw [hk]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem map_conj_le_normalizer {M : Type*} [Group M] {T D : Subgroup M} (g : M)
    (hDT : D ≤ Subgroup.normalizer (T : Set M)) :
    D.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup M) : Set M) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨d * t * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨t, ht, hx⟩
    refine ⟨d⁻¹ * t * d, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hDT (D.inv_mem hd)) t).mp ht
      rwa [inv_inv] at h1
    · rw [map_mul, map_mul, map_inv, hx]
      group

end Item211Res3Proof

open Item211Res3Proof

theorem ks211TwoLocalS7 : KS211TwoLocalS7 := by
  intro T D hT _ hD9 hDT
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine hD9
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hcard : Nat.card T' = Nat.card T := KFacts.K412.card_map_conj T g
  have hT'2 : IsPGroup 2 T' := hT.map _
  have h3 : ¬ 3 ∣ Nat.card T' := not_three_dvd_card_of_isPGroup_two hT'2
  have hN : KFacts.KP2.eNine ≤ Subgroup.normalizer (T' : Set (Perm (Fin 7))) := by
    rw [← hg]
    exact map_conj_le_normalizer g hDT
  rw [← hcard]
  rcases KFacts.KP2.le_vOne_or_le_vTwo h3 (hN KFacts.KP2.cOne_mem_eNine)
      (hN KFacts.KP2.cTwo_mem_eNine) with h | h
  · calc Nat.card T' ≤ Nat.card KFacts.KP2.vOne := Subgroup.card_le_of_le h
      _ = 4 := KFacts.KP2.card_vOne
  · calc Nat.card T' ≤ Nat.card KFacts.KP2.vTwo := Subgroup.card_le_of_le h
      _ = 4 := KFacts.KP2.card_vTwo

end CFSG.RankThree.PartTwo.Sec21
