module

public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Ord
public import CFSG.Quasithin.EmptyFaithful.T1515M11

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem card_statedProj_statedSL_three_mul_gcd (K : Type) [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
  CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2.card_psl3_mul K

theorem card_statedProj_statedSU_three_mul_gcd {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
  CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK

theorem forall_of_forall_lt1515e {N B : ℕ} (hN : 0 < N) (hB : N < B ^ 3) {P : ℕ → Prop}
    (h : ∀ q < B, 2 ≤ q → q ^ 3 ∣ N → P q) : ∀ q, 2 ≤ q → q ^ 3 ∣ N → P q := by
  intro q hq hd
  refine h q ?_ hq hd
  by_contra hqB
  have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hqB) 3
  have h2 := Nat.le_of_dvd hN hd
  omega

structure L3Free1515e (N q₀ : ℕ) : Prop where
  sl : ∀ q, 2 ≤ q → q % 3 = 1 → q ≠ q₀ → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))
  su : ∀ q, 2 ≤ q → q % 3 = 2 → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))

theorem L3Free1515e.of_check {N q₀ B : ℕ} (hN : 0 < N) (hB : N < B ^ 3)
    (hsl : ∀ q < B, (2 ≤ q ∧ q % 3 = 1 ∧ q ≠ q₀ ∧ q ^ 3 ∣ N) →
      N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hsu : ∀ q < B, (2 ≤ q ∧ q % 3 = 2 ∧ q ^ 3 ∣ N) →
      N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    L3Free1515e N q₀ :=
  ⟨fun q hq h3 h0 => forall_of_forall_lt1515e (P := fun q => q % 3 = 1 → q ≠ q₀ → _) hN hB
      (fun q hqB hq2 hd h3 h0 => hsl q hqB ⟨hq2, h3, h0, hd⟩) q hq |> fun f hd => f hd h3 h0,
   fun q hq h3 => forall_of_forall_lt1515e (P := fun q => q % 3 = 2 → _) hN hB
      (fun q hqB hq2 hd h3 => hsu q hqB ⟨hq2, h3, hd⟩) q hq |> fun f hd => f hd h3⟩

theorem A318Exclusion.of_card_exc {X : Type} [Group X] [Finite X] {N q₀ : ℕ}
    (hs : IsSimpleGroup X) (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) (hN : Nat.card X = N)
    (hL : L3Free1515e N q₀)
    (hexc : ∀ (Y : Type) [Group Y] (p k : ℕ), p.Prime → 1 ≤ k → IsPSL 3 p k Y → p ^ k = q₀ →
      Nonempty (Y ≃* X) → False) :
    A318Exclusion X := by
  refine ⟨hs, hr, ?_⟩
  intro Y _ s p k hp hk hY hmod f hf
  have hYs : IsSimpleGroup Y := by
    cases s
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 p k hY).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 p k hY).2
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hb | ht
    · exact hb
    · exfalso
      have hsub : Subsingleton X := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a', rfl⟩ := hf a
        obtain ⟨b', rfl⟩ := hf b
        have h1 : f a' = 1 := MonoidHom.mem_ker.mp (ht ▸ Subgroup.mem_top a')
        have h2 : f b' = 1 := MonoidHom.mem_ker.mp (ht ▸ Subgroup.mem_top b')
        rw [h1, h2]
      exact (not_subsingleton X) hsub
  have hcard : Nat.card Y = N := by
    rw [← hN]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩)
  have hY0 := hY
  cases s
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have hc := card_statedProj_statedSU_three_mul_gcd hp hk hK
    rw [← Nat.card_congr e.toEquiv, hcard] at hc
    have hq2 : 2 ≤ p ^ k := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
    have hcop : Nat.Coprime ((p ^ k) ^ 3) (Nat.gcd 3 (p ^ k + 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    have hm : (p ^ k) % 3 = 2 := by
      have h := hmod
      simp only [Bool.false_eq_true, ↓reduceIte, Int.ModEq] at h
      omega
    exact hL.su _ hq2 hm (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)) hc
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have hc := card_statedProj_statedSL_three_mul_gcd K
    rw [← Nat.card_congr e.toEquiv, hcard, hK] at hc
    have hq2 : 2 ≤ p ^ k := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
    have hcop : Nat.Coprime ((p ^ k) ^ 3) (Nat.gcd 3 (p ^ k - 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      have h1 : Nat.Coprime (p ^ k - 1) (p ^ k - 1 + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.sub_add_cancel (by omega)] at h1
      exact h1.symm
    have hm : (p ^ k) % 3 = 1 := by
      have h := hmod
      simp only [↓reduceIte, Int.ModEq] at h
      omega
    refine hL.sl _ hq2 hm ?_ (hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)) hc
    intro h0
    exact hexc Y p k hp hk hY0 h0 ⟨MulEquiv.ofBijective f ⟨hinj, hf⟩⟩

theorem A318Exclusion.of_card {X : Type} [Group X] [Finite X] {N : ℕ} (hs : IsSimpleGroup X)
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) (hN : Nat.card X = N) (hL : L3Free1515e N 0) :
    A318Exclusion X :=
  A318Exclusion.of_card_exc hs hr hN hL fun Y _ p k hp hk _ h0 _ => by
    have : 2 ≤ p ^ k := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
    omega

section Checks

theorem l3Free_2520 : L3Free1515e 2520 0 :=
  L3Free1515e.of_check (B := 14) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_360 : L3Free1515e 360 0 :=
  L3Free1515e.of_check (B := 8) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_6048 : L3Free1515e 6048 0 :=
  L3Free1515e.of_check (B := 19) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_9999360 : L3Free1515e 9999360 0 :=
  L3Free1515e.of_check (B := 216) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_17971200 : L3Free1515e 17971200 0 :=
  L3Free1515e.of_check (B := 262) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_211341312 : L3Free1515e 211341312 0 :=
  L3Free1515e.of_check (B := 596) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_604800 : L3Free1515e 604800 0 :=
  L3Free1515e.of_check (B := 85) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_4030387200 : L3Free1515e 4030387200 0 :=
  L3Free1515e.of_check (B := 1592) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_95040 : L3Free1515e 95040 0 :=
  L3Free1515e.of_check (B := 46) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_443520 : L3Free1515e 443520 0 :=
  L3Free1515e.of_check (B := 77) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_10200960 : L3Free1515e 10200960 0 :=
  L3Free1515e.of_check (B := 217) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_244823040 : L3Free1515e 244823040 0 :=
  L3Free1515e.of_check (B := 626) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem l3Free_7920 : L3Free1515e 7920 0 :=
  L3Free1515e.of_check (B := 20) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem l3Free_20160 : L3Free1515e 20160 4 :=
  L3Free1515e.of_check (B := 28) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end Checks

section Clauses

theorem card_alt_fin1515e (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem a318Exclusion_alt7 : A318Exclusion (alternatingGroup (Fin 7)) :=
  A318Exclusion.of_card (N := 2520)
    (alternatingGroup.isSimpleGroup (by simp))
    (CFSG.Quasithin.A3Facts.two_le_pRank_alternating (by norm_num))
    (by rw [card_alt_fin1515e 7 (by norm_num)]; decide) l3Free_2520

theorem a318Exclusion_alt6 : A318Exclusion (alternatingGroup (Fin 6)) :=
  A318Exclusion.of_card (N := 360)
    (alternatingGroup.isSimpleGroup (by simp))
    (CFSG.Quasithin.A3Facts.two_le_pRank_alternating (by norm_num))
    (by rw [card_alt_fin1515e 6 (by norm_num)]; decide) l3Free_360

theorem two_le_pRank_of_isPSL1515e {n p e : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (h : IsPSL n p e X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKf, hK, ⟨e'⟩⟩ := h
  have := CFSG.Quasithin.A3Facts.psl_two_le_pRank_three (K := K) hn
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']

theorem a318Exclusion_psl52 {X : Type} [Group X] [Finite X] (h : IsPSL 5 2 1 X) :
    A318Exclusion X :=
  A318Exclusion.of_card (N := 9999360)
    (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
    (two_le_pRank_of_isPSL1515e (by norm_num) h)
    (by rw [card_of_isPSL_two1522 5 h]; simp [Fin.prod_univ_five]) l3Free_9999360

@[expose] def L34NotL42Fact1515e : Prop :=
  ∀ (X : Type) [Group X], IsPSL 3 2 2 X → ¬ IsPSL 4 2 1 X

theorem isPSL_of_mulEquiv1515e {n p e : ℕ} {X Y : Type} [Group X] [Group Y] (f : Y ≃* X)
    (h : IsPSL n p e X) : IsPSL n p e Y := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨f.trans e'⟩⟩

theorem a318Exclusion_psl42 (h34 : L34NotL42Fact1515e) {X : Type} [Group X] [Finite X]
    (h : IsPSL 4 2 1 X) : A318Exclusion X :=
  A318Exclusion.of_card_exc (N := 20160) (q₀ := 4)
    (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    (two_le_pRank_of_isPSL1515e (by norm_num) h)
    (by rw [card_of_isPSL_two1522 4 h]; simp [Fin.prod_univ_four]) l3Free_20160
    (fun Y _ p k hp hk hY h4 ⟨f⟩ => by
      have hpd : p ∣ 2 ^ 2 := by
        have : p ∣ p ^ k := dvd_pow_self p (by omega)
        rw [h4] at this
        simpa using this
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
      subst hp2
      have hk2 : k = 2 := Nat.pow_right_injective (le_refl 2) (by simpa using h4)
      subst hk2
      exact h34 Y hY (isPSL_of_mulEquiv1515e f h))

end Clauses

end CFSG.Quasithin
