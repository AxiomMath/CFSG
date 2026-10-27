module

public import CFSG.Quasithin.EmptyFaithful.S146zYZSz
public import CFSG.Quasithin.EmptyFaithful.S146zYCfg

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem facts134Five_sz :
    ∀ n : ℕ, NoE25Config fun (X : Type) [Group X] => SuzukiModel X 2 n := by
  intro n A _ _ L P T hL hcfg
  have hU := E25Config.isSylowTwoOf_inf hcfg
  have hcard := E25Config.card_sup_inf hcfg
  have hT2 : IsPGroup 2 (T ⊓ L : Subgroup A) := hcfg.sylow.2.1.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT2
  obtain ⟨y, hyP, hy1⟩ : ∃ y ∈ P, y ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 := hcfg.card
    rw [(Subgroup.eq_bot_iff_forall P).2 hall, Subgroup.card_bot] at h1
    omega
  have hy5 : orderOf y = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hcfg.exp y hyP) hy1
  refine sz_no_five A L (P ⊔ (T ⊓ L)) (T ⊓ L) n y hL le_sup_right (E25Config.sup_inf_le hcfg) hU
    ?_ (Subgroup.mem_sup_left hyP) hy5
  intro q hq hqd
  rw [hcard, hk] at hqd
  rcases (Nat.Prime.dvd_mul hq).1 hqd with h | h
  · have h25 : q ∣ 5 ^ 2 := by norm_num; exact h
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (hq.dvd_of_dvd_pow h25))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

end CFSG.Quasithin.S146zY
