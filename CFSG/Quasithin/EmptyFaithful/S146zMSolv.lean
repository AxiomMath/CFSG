module

public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146zMFit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section HTM

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Setting146.isHTM_of_le_mcOf (S : Setting146 G T M) (hH : IsHTM T M H) {Hp : Subgroup G}
    (hHHp : H ≤ Hp) (hHpM : Hp ≤ mcOf T) : IsHTM T M Hp := by
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Subgroup.closure_le _).mpr fun z hz => hz.1.1
  have hZHp : quasithinOmegaOneCenter T ≤ Hp := hZT.trans (hH.1.1.trans hHHp)
  have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    IsPGroup.of_card (n := 1) (by rw [S.card_Z]; norm_num)
  have hZ : quasithinOmegaOneCenter T ≤ pCoreOf 2 Hp :=
    le_pCoreOf_of_le_normalizer 2 hZHp (hHpM.trans S.normalizer_Z.ge) hZp
  refine ⟨⟨hH.1.1.trans hHHp, fun hbot => ?_⟩, fun h => hH.2 (hHHp.trans h)⟩
  have h1 : quasithinOmegaOneCenter T = ⊥ := eq_bot_iff.mpr (hbot ▸ hZ)
  have h2 : Nat.card (quasithinOmegaOneCenter T) = 1 := by rw [h1]; exact Subgroup.card_bot
  rw [S.card_Z] at h2
  exact absurd h2 (by norm_num)

end HTM

theorem input14614Solv_proved : Input14614Solv := by
  intro G _ _ T M S H PQ p hred hmax Hp hHHp hHpM hsolv
  classical
  have hHp : IsHTM T M Hp := S.isHTM_of_le_mcOf hred.isHTM hHHp hHpM
  have hSQ : CFSG.IsStronglyQuasithin ↥Hp :=
    isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank S.hyp.qtke.2.2 hHp.1.2
  have hrk := CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQ
  have hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Hp) ≤ 2 := hrk 3 Nat.prime_three (by norm_num)
  have hr5 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Hp) ≤ 2 := hrk 5 (by norm_num) (by norm_num)
  let φ : ↥Hp →* OTwoQuot Hp := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Hp)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hsolvD : Group.IsSolvable (OTwoQuot Hp) := Group.isSolvable_of_surjective hφ
  have hO2 : CFSG.Open.pCore 2 (OTwoQuot Hp) = ⊥ := by
    have := pCore_two_quot_eq_bot Hp
    assumption
  have hmaxD : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pCore q (OTwoQuot Hp) ≠ ⊥ → q ≤ p :=
    fun q hq hq2 hne => hmax Hp hHp q hq hq2 (by assumption)
  have hdiv : ∀ r : ℕ, r.Prime → r ∣ Nat.card Hp → r = 2 ∨ r ∣ Nat.card (OTwoQuot Hp) := by
    intro r hr hdvd
    have hcard : Nat.card ↥Hp = Nat.card (CFSG.Open.pCore 2 ↥Hp) * Nat.card (OTwoQuot Hp) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Hp)]
      ring
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥Hp)).exists_card_eq
    rw [hcard, hk] at hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    · exact Or.inr h
  refine ⟨fun hp3 r hr hdvd => ?_, fun hp5 r hr hdvd => ?_⟩
  · rcases hdiv r hr hdvd with h | h
    · exact Or.inl h
    · rcases prime_mem_allowed_of_solvable_quotient φ hφ hsolvD hO2 hr3 hr5 (Or.inl hp3) hmaxD hr
        h with h' | h' | ⟨h', -⟩
      · exact Or.inl h'
      · exact Or.inr h'
      · omega
  · rcases hdiv r hr hdvd with h | h
    · exact Or.inl h
    · rcases prime_mem_allowed_of_solvable_quotient φ hφ hsolvD hO2 hr3 hr5 (Or.inr hp5) hmaxD hr
        h with h' | h' | ⟨-, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')

end CFSG.Quasithin
