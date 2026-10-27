module

public import CFSG.Quasithin.H13.NQTermThompsonFactorization
public import CFSG.RankThree.PGroups.SolvableTrivialComplementCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open

theorem zpowers_eq_of_normal {H : Type} [Group H] [Finite H] {x : H} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hx : orderOf x = p) (hcard : Nat.card H = p * 2 ^ k) {K : Subgroup H}
    (hKn : K.Normal) (hK : Nat.card K = p) : Subgroup.zpowers x = K := by
  have hidx : K.index = 2 ^ k := by
    have e := Subgroup.card_mul_index K
    rw [hK, hcard] at e
    exact Nat.eq_of_mul_eq_mul_left hp.pos e
  have hxK : x ∈ K := by
    have hq : (QuotientGroup.mk x : H ⧸ K) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h1 : orderOf (QuotientGroup.mk x : H ⧸ K) ∣ p := orderOf_dvd_of_pow_eq_one hq
    have h2 : orderOf (QuotientGroup.mk x : H ⧸ K) ∣ 2 ^ k := hidx ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h3 : orderOf (QuotientGroup.mk x : H ⧸ K) ∣ Nat.gcd p (2 ^ k) := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxK) ?_
  rw [hK, Nat.card_zpowers, hx]

theorem pPrimeCore_two_eq_bot {H : Type} [Group H] [Finite H] {x : H} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hx : orderOf x = p) (hcard : Nat.card H = p * 2 ^ k)
    (hnn : ¬ (Subgroup.zpowers x).Normal) : CFSG.pPrimeCore 2 H = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  have hdvd : Nat.card K ∣ p * 2 ^ k := hcard ▸ Subgroup.card_subgroup_dvd_card K
  have hKp : Nat.card K ∣ p := (Nat.Coprime.pow_right k hcop.symm).dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime hp).mp hKp with h1 | h1
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (by rw [zpowers_eq_of_normal hp hp2 hx hcard hK h1]; exact hK) hnn

theorem sylow_normal_of_no_char_normal {H : Type} [Group H] [Finite H] {P : Subgroup H} {x : H}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hP : IsPGroup 2 P) (hx : orderOf x = p) (hcard : Nat.card H = p * Nat.card P)
    (hno : ∀ K : Subgroup H, K ≤ P → (K.subgroupOf P).Characteristic → K.Normal → K = ⊥) :
    (Subgroup.zpowers x).Normal := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hcardH : Nat.card H = p * 2 ^ k := by rw [hcard, hk]
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  by_cases hPbot : P = ⊥
  · have h : Nat.card (Subgroup.zpowers x) = Nat.card H := by
      rw [hxcard, hcard, hPbot, Subgroup.card_bot, mul_one]
    rw [Subgroup.eq_top_of_card_eq _ h]
    infer_instance
  by_contra hnn
  have : Fintype H := Fintype.ofFinite H
  have hsolv : Group.IsSolvable H :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := p) (q := 2)
      (a := 1) (b := k) hp Nat.prime_two hp2
      (by rw [← Nat.card_eq_fintype_card, hcardH, pow_one])
  have hchar : CFSG.IsCharacteristicP 2 H :=
    CFSG.RankThree.PGroups.solvable_trivial_complement_core Nat.prime_two
      (pPrimeCore_two_eq_bot hp hp2 hx hcardH hnn)
  have hF : CFSG.generalizedFitting H = CFSG.pCore 2 H :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H 2).mp hchar
  have h3 : ¬ 3 ∣ Nat.card H := by
    rw [hcardH]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hidx2 : P.index = p := by
    have e := Subgroup.index_mul_card P
    rw [hk, hcardH] at e
    exact Nat.eq_of_mul_eq_mul_right (by positivity) e
  have hidx : ¬ 2 ∣ P.index := by
    rw [hidx2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  let T : Sylow 2 H := hP.toSylow hidx
  obtain ⟨-, -, -, -, -, -, hfac, -⟩ :=
    CFSG.Quasithin.H13.NQTerm.solvable_characteristic_two_three_free_thompson_factorization hF h3
      T (Z := quasithinOmegaOneCenter P)
      (U := Subgroup.normalClosure ((quasithinOmegaOneCenter P : Subgroup H) : Set H))
      (J := (elemThompson P 2).map P.subtype) rfl rfl rfl
  have hJeq : (elemThompson P 2).map P.subtype = thompsonJ P :=
    elemThompson_map_subtype_eq_thompsonJ P
  have hJP : (elemThompson P 2).map P.subtype ≤ P := Subgroup.map_subtype_le _
  have hJchar : (((elemThompson P 2).map P.subtype).subgroupOf P).Characteristic := by
    rw [hJeq]
    exact CFSG.QuasithinUnique.Setup.characteristic_thompsonJ P
  have hJne : (elemThompson P 2).map P.subtype ≠ ⊥ := by
    rw [hJeq]
    exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hP hPbot
  have hJnn : ¬ ((elemThompson P 2).map P.subtype).Normal := fun hn => hJne (hno _ hJP hJchar hn)
  have hPN : P ≤ Subgroup.normalizer (((elemThompson P 2).map P.subtype : Subgroup H) : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJP).mp (by have := hJchar; infer_instance)
  have hNP : Subgroup.normalizer (((elemThompson P 2).map P.subtype : Subgroup H) : Set H) = P := by
    have hdvd := Subgroup.index_dvd_of_le hPN
    rw [hidx2] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h1)) hJnn
    · have e := Subgroup.card_mul_index
        (Subgroup.normalizer (((elemThompson P 2).map P.subtype : Subgroup H) : Set H))
      rw [h1, hcardH, mul_comm] at e
      have hc := Nat.eq_of_mul_eq_mul_left hp.pos e
      exact (Subgroup.eq_of_le_of_card_ge hPN (by rw [hc, hk])).symm
  rw [hNP] at hfac
  have hZC : quasithinOmegaOneCenter P ≤ Subgroup.centralizer (P : Set H) :=
    (Subgroup.closure_le _).2 fun _ hz => hz.1.2
  have hPC : P ≤ Subgroup.centralizer (quasithinOmegaOneCenter P : Set H) :=
    Subgroup.le_centralizer_iff.mpr hZC
  have hC : Subgroup.centralizer (quasithinOmegaOneCenter P : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp (hfac ▸ Set.mem_univ g)
    exact mul_mem (hPC ha) hc
  have hZn : (quasithinOmegaOneCenter P).Normal := by
    refine ⟨fun z hz g => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp (hC ▸ Subgroup.mem_top g) z hz
    rwa [← h, mul_inv_cancel_right]
  exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP hPbot
    (hno _ (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le P)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf P) hZn)

end CFSG.Quasithin.Fan86
