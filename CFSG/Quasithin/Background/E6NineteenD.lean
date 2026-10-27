module

public import CFSG.Quasithin.Background.E6NineteenC
public import CFSG.Quasithin.Background.GoldschmidtTDE68L2pPsl

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem center_eq_bot_of_psl2_model {X : Type} [Group X] [Finite X] {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel X .PSL 2 p f) : Subgroup.center X = ⊥ := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p f hmodel).2
  obtain ⟨K, _, _, _, e, hcard, -, h5⟩ := K1.psl2_model_data hp2 hmodel
  obtain ⟨⟨hp, hf, -, -, -⟩, -⟩ := hmodel
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set q := Fintype.card K with hq
  have hKq : Nat.card K = q := Nat.card_eq_fintype_card
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hodd, hf, by rw [hKq, hcard]⟩
  have hcardX : Nat.card X = q * (q ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.Suzuki.card_psl2_of_card K hK hKq]
  have hqodd : Odd q := by rw [hcard]; exact hodd.pow
  have hnp : ¬ (Nat.card X).Prime := by
    rw [hcardX]
    obtain ⟨k, hk⟩ := hqodd
    have h2 : 2 ∣ q ^ 2 - 1 := by
      rw [hk]
      exact ⟨2 * k ^ 2 + 2 * k, by ring_nf; omega⟩
    rw [Nat.mul_div_assoc _ h2]
    apply Nat.not_prime_mul
    · omega
    · have h1 : 25 ≤ q ^ 2 := by nlinarith
      omega
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative X :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hnp (Group.is_simple_iff_prime_card.mp hs)

theorem isPGroup_centralizer_psl2 {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hFM : IsFermatOrMersenne p) (h7 : 7 ≤ p) (hK : Nat.card K = p) {s : PSL(2, K)}
    (hs : orderOf s = 2) : IsPGroup 2 ↥(Subgroup.centralizer ({s} : Set PSL(2, K))) := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K (p := p) (f := 1)
    (by rw [hK, pow_one]) hodd one_pos hs
  rw [pow_one] at h1 h3
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(Subgroup.centralizer ({s} : Set PSL(2, K))) = 2 ^ m := by
    rcases Nat.lt_or_ge 7 p with hlt | hle
    · rcases Unc25K1.fermat_or_mersenne_pow hFM hlt with ⟨h8, m, hm⟩ | ⟨h8, m, hm⟩
      · exact ⟨m, by rw [(h1 (by omega)).1]; omega⟩
      · exact ⟨m, by rw [(h3 (by omega)).1]; omega⟩
    · obtain rfl : p = 7 := by omega
      exact ⟨3, by rw [(h3 (by norm_num)).1]; norm_num⟩
  exact IsPGroup.of_card hm

theorem oddInvertFree_psl2p
    (hE : EvenLieAutInner) (hC : LieInvolCentCharTwo) :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ), IsFermatOrMersennePrime p →
      StatedClassicalModel X .PSL 2 p 1 → OddInvertFree X := by
  intro X _ _ p hFM hmodel
  have hp : p.Prime := hFM.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hprime, -, -, h22, h23⟩ := hmodel.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h22 rfl
  have hZ := center_eq_bot_of_psl2_model hp2 hmodel
  by_cases h7 : 7 ≤ p
  · have hfix := (L2p.psl2_facts hFM h7 hmodel).1
    refine oddInvertFree_of_charTwo hZ (Inn.InvolFixInner.of_forall fun Q hQ β hβ => hfix Q hQ β hβ)
      fun t ht1 htt => ?_
    have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
    obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data hp2 hmodel
    have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
    refine CFSG.ComponentClassification.RankTwoChar2C0.isCharacteristicP_centralizer_of_mulEquiv
      e (fun s hs => ?_) t hto
    exact isCharacteristicP_of_isPGroup
      ((isPGroup_centralizer_psl2 hFM h7 hK hs).of_equiv Subgroup.topEquiv.symm)
  ·
    have h5 : p = 5 := by
      have h2 := hp.two_le
      have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have hp6 : p ≠ 6 := by
        rintro rfl
        norm_num at hp
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact h23 rfl
      omega
    subst h5
    have h4 : StatedClassicalModel X .PSL 2 2 2 :=
      Ch1.statedClassicalModel_psl_two_four_of_alternating_five X
        (Setup.Family.alternating_five_of_model_five hmodel)
    exact oddInvertFree_of_lie hE hC (Or.inl (Or.inl ⟨2, Or.inl ⟨le_rfl, h4⟩⟩)) hZ

end E6

end CFSG.Quasithin
