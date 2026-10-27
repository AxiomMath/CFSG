module

import CFSG.Goldschmidt.Steps.G310TransQuot
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.M591D

open Subgroup CFSG.Open
open scoped commutatorElement

@[expose] def OddInvCent {X : Type*} [Group X] (N D : Subgroup X) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup X, Q ≤ N → IsPGroup q Q →
    D ≤ normalizer (Q : Set X) → Q ≤ centralizer (D : Set X)

@[expose] def LemmaCBelow (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ N D : Subgroup X, Nat.card N < n →
    D ≤ normalizer (N : Set X) → Nat.card D = 3 → Nat.Coprime 3 (Nat.card N) → OddInvCent N D →
      ∃ k : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ k

theorem OddInvCent.mono {X : Type*} [Group X] {N N₁ D : Subgroup X} (h : OddInvCent N D) (hle : N₁ ≤ N) :
    OddInvCent N₁ D :=
  fun q hq hq2 Q hQ hQp hDQ => h q hq hq2 Q (hQ.trans hle) hQp hDQ

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {W : Subgroup X} {k : X}
    (h : ∀ w ∈ W, k * w * k⁻¹ ∈ W) : k ∈ normalizer (W : Set X) := by
  have hle : W.map (MulAut.conj k).toMonoidHom ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using h w hw
  have heq : W.map (MulAut.conj k).toMonoidHom = W :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  have : w = x := by
    have h2 : k * w * k⁻¹ = k * x * k⁻¹ := by simpa [MulAut.conj_apply] using hwx
    simpa using h2
  exact this ▸ hw

theorem exists_inv_sylow {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) {D M : Subgroup X}
    (hD3 : Nat.card D = 3) (hM : Nat.Coprime 3 (Nat.card M)) (hDM : D ≤ normalizer (M : Set X)) :
    ∃ S : Subgroup X, fusionIsSylowIn q S M ∧ D ≤ normalizer (S : Set X) := by
  obtain ⟨S, hS, -, hDS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three hq
    (IsPGroup.of_card (n := 1) (by rw [hD3, pow_one]))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hM) hDM bot_le IsPGroup.of_bot
    (by rw [normalizer_eq_top_iff.2 inferInstance]; exact le_top)
  exact ⟨S, hS, hDS⟩

theorem card_of_fusionIsSylowIn {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {S M : Subgroup X}
    (h : fusionIsSylowIn p S M) : Nat.card S = p ^ (Nat.card M).factorization p := by
  obtain ⟨P, rfl⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn h
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  exact P.card_eq_multiplicity

theorem lemmaC_of_restrict {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {N D : Subgroup X}
    (hDN : D ≤ normalizer (N : Set X)) (hD3 : Nat.card D = 3) (hcop : Nat.Coprime 3 (Nat.card N))
    (hb : OddInvCent N D)
    (H : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → ∀ N' D' : Subgroup Y, N' ⊔ D' = ⊤ →
      Nat.card N' = Nat.card N → D' ≤ normalizer (N' : Set Y) → Nat.card D' = 3 →
        Nat.Coprime 3 (Nat.card N') → OddInvCent N' D' → ∃ k : ℕ, Nat.card ↥⁅N', D'⁆ = 2 ^ k) :
    ∃ k : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ k := by
  set A : Subgroup X := N ⊔ D with hA
  have hNA : N ≤ A := le_sup_left
  have hDA : D ≤ A := le_sup_right
  set N' : Subgroup A := N.subgroupOf A with hN'
  set D' : Subgroup A := D.subgroupOf A with hD'
  have hcardN : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv
  have hcardD : Nat.card D' = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv
  have hsup : N' ⊔ D' = ⊤ := by
    rw [hN', hD', ← subgroupOf_sup hNA hDA]
    exact subgroupOf_self A
  have hAN : A ≤ normalizer (N : Set X) := sup_le le_normalizer hDN
  have hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNA).2 hAN
  have hD'N' : D' ≤ normalizer (N' : Set A) := by
    rw [normalizer_eq_top_iff.2 hN'n]
    exact le_top
  have hb' : OddInvCent N' D' := by
    intro q hq hq2 Q hQN hQ hDQ
    have hQXN : Q.map A.subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact hQN hx
    have hDQX : D ≤ normalizer ((Q.map A.subtype : Subgroup X) : Set X) := by
      intro d hd
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨x, hx, rfl⟩
      have hd' : (⟨d, hDA hd⟩ : A) ∈ D' := hd
      exact ⟨_, (mem_normalizer_iff.1 (hDQ hd') x).1 hx, rfl⟩
    have hC := hb q hq hq2 _ hQXN (hQ.map _) hDQX
    intro x hx
    rw [mem_centralizer_iff]
    intro d hd
    exact Subtype.ext (mem_centralizer_iff.1 (hC ⟨x, hx, rfl⟩) d hd)
  obtain ⟨k, hk⟩ := H A (hX.subgroup A) N' D' hsup hcardN hD'N' (hcardD.trans hD3) (hcardN ▸ hcop) hb'
  refine ⟨k, ?_⟩
  have hmap : ⁅N', D'⁆.map A.subtype = ⁅N, D⁆ := by
    rw [map_commutator, hN', hD', map_subgroupOf_eq_of_le hNA, map_subgroupOf_eq_of_le hDA]
  rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective, hk]

theorem card_eq_two_pow_mul {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {N D W : Subgroup X}
    (hNn : N.Normal) (hD3 : Nat.card D = 3) (hcop : Nat.Coprime 3 (Nat.card N)) (hb : OddInvCent N D)
    (hcomm : ⁅N, D⁆ = N) [W.Normal] (hWN : W ≤ N) (hW1 : W ≠ ⊥) (IH : LemmaCBelow (Nat.card N)) :
    ∃ k : ℕ, Nat.card N = 2 ^ k * Nat.card W := by
  set π := QuotientGroup.mk' W with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective W
  set N' : Subgroup (X ⧸ W) := N.map π with hN'
  set D' : Subgroup (X ⧸ W) := D.map π with hD'
  have hcardN : Nat.card N = Nat.card N' * Nat.card W := by
    have h1 : W.relIndex N = Nat.card N' := by
      have := Subgroup.relIndex_ker N π
      rwa [QuotientGroup.ker_mk'] at this
    have h2 : Nat.card (W.subgroupOf N) * W.relIndex N = Nat.card N := card_mul_index (W.subgroupOf N)
    rw [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv, h1] at h2
    rw [← h2, mul_comm]
  have hW1' : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).2 hW1
  have hlt : Nat.card N' < Nat.card N := by
    rw [hcardN]
    have : 0 < Nat.card N' := Nat.card_pos
    nlinarith
  have hN'n : N'.Normal := hNn.map π hπs
  have hD'N' : D' ≤ normalizer (N' : Set (X ⧸ W)) := by
    rw [normalizer_eq_top_iff.2 hN'n]
    exact le_top
  have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (h.trans (card_dvd_of_le hWN))
  have hD'3 : Nat.card D' = 3 := by
    have hdvd : Nat.card D' ∣ 3 := hD3 ▸ Subgroup.card_map_dvd D π
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hDW : D ≤ W := by
        intro d hd
        have : π d ∈ D' := mem_map_of_mem π hd
        rw [Subgroup.card_eq_one.1 h1, mem_bot] at this
        exact (QuotientGroup.eq_one_iff d).1 this
      exact hW3 (hD3 ▸ card_dvd_of_le hDW)
    · exact h1
  have hcop' : Nat.Coprime 3 (Nat.card N') := Nat.Coprime.coprime_dvd_right (card_map_dvd N π) hcop
  have hb' : OddInvCent N' D' := by
    intro q hq hq2 Q' hQ'N' hQ' hD'Q'
    haveI : Fact q.Prime := ⟨hq⟩
    set P : Subgroup X := Q'.comap π with hP
    have hPN : P ≤ N := by
      intro x hx
      obtain ⟨n, hn, hnx⟩ := hQ'N' hx
      have hnx' : n⁻¹ * x ∈ W := QuotientGroup.eq.1 hnx
      have := N.mul_mem hn (hWN hnx')
      simpa using this
    have hDP : D ≤ normalizer (P : Set X) := by
      intro d hd
      apply mem_normalizer_of_conj_mem
      intro x hx
      show π (d * x * d⁻¹) ∈ Q'
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 (hD'Q' (mem_map_of_mem π hd)) (π x)).1 hx
    obtain ⟨S, hS, hDS⟩ :=
      exists_inv_sylow hq hD3 (Nat.Coprime.coprime_dvd_right (card_dvd_of_le hPN) hcop) hDP
    have hSC : S ≤ centralizer (D : Set X) := hb q hq hq2 S (hS.1.trans hPN) hS.2.1 hDS
    have hPmap : P.map π = Q' := map_comap_eq_self_of_surjective hπs Q'
    have hSmap : S.map π = Q' := by
      rw [CFSG.Goldschmidt.G310.map_eq_of_fusionIsSylowIn π hS (hPmap ▸ hQ'), hPmap]
    rw [← hSmap]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hSC hs) d hd]
  obtain ⟨k, hk⟩ := IH (X ⧸ W) (hX.quotient W) N' D' hlt hD'N' hD'3 hcop' hb'
  have h3 : ⁅N', D'⁆ = N' := by rw [hN', hD', ← map_commutator, hcomm]
  rw [h3] at hk
  exact ⟨k, by rw [hcardN, hk]⟩

theorem factorization_two_pow_mul {k r q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (2 ^ k * q ^ r).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hq.ne_zero), Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
    Nat.prime_two.factorization, hq.factorization]
  simp [Finsupp.single_apply, hq2]

theorem abelian_case {X : Type*} [Group X] [Finite X] {N D W : Subgroup X}
    (hDN : D ≤ normalizer (N : Set X)) (hD3 : Nat.card D = 3) (hcop : Nat.Coprime 3 (Nat.card N))
    (hb : OddInvCent N D) [hWn : W.Normal] (hWN : W ≤ N) {q r k : ℕ} (hq : q.Prime)
    (hWcard : Nat.card W = q ^ r) (hNcard : Nat.card N = 2 ^ k * Nat.card W) :
    ∃ j : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ j := by
  have hNDN : ⁅N, D⁆ ≤ N := le_normalizer_iff_commutator_le_left.1 hDN
  by_cases hq2 : q = 2
  · subst hq2
    have hdvd : Nat.card ↥⁅N, D⁆ ∣ 2 ^ (k + r) := by
      rw [pow_add, ← hWcard, ← hNcard]
      exact card_dvd_of_le hNDN
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hDW : D ≤ normalizer (W : Set X) := by
      rw [normalizer_eq_top_iff.2 hWn]
      exact le_top
    have hWD : W ≤ centralizer (D : Set X) := hb q hq hq2 W hWN (IsPGroup.of_card hWcard) hDW
    obtain ⟨T, hT, hDT⟩ := exists_inv_sylow Nat.prime_two hD3 hcop hDN
    have hTcard : Nat.card T = 2 ^ k := by
      rw [card_of_fusionIsSylowIn hT, hNcard, hWcard, factorization_two_pow_mul hq hq2]
    have hdecomp : ∀ n ∈ N, ∃ t ∈ T, ∃ w ∈ W, n = t * w := by
      have hc : (T.subgroupOf N).IsComplement' (W.subgroupOf N) := by
        have e1 : Nat.card (T.subgroupOf N) = 2 ^ k :=
          (Nat.card_congr (subgroupOfEquivOfLe hT.1).toEquiv).trans hTcard
        have e2 : Nat.card (W.subgroupOf N) = q ^ r :=
          (Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv).trans hWcard
        apply isComplement'_of_coprime
        · rw [e1, e2, ← hWcard, ← hNcard]
        · rw [e1, e2]
          exact Nat.Coprime.pow k r ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
      intro n hn
      obtain ⟨⟨⟨t, ht⟩, ⟨w, hw⟩⟩, h⟩ := hc.2 ⟨n, hn⟩
      exact ⟨t, ht, w, hw, (congrArg Subtype.val h).symm⟩
    have hle : ⁅N, D⁆ ≤ T := by
      rw [commutator_le]
      intro n hn d hd
      obtain ⟨t, ht, w, hw, rfl⟩ := hdecomp n hn
      have hwd : d * w = w * d := mem_centralizer_iff.1 (hWD hw) d hd
      have hcalc : ⁅t * w, d⁆ = t * (d * t⁻¹ * d⁻¹) := by
        rw [commutatorElement_def]
        calc t * w * d * (t * w)⁻¹ * d⁻¹ = t * (w * d) * w⁻¹ * t⁻¹ * d⁻¹ := by group
          _ = t * (d * w) * w⁻¹ * t⁻¹ * d⁻¹ := by rw [hwd]
          _ = t * (d * t⁻¹ * d⁻¹) := by group
      rw [hcalc]
      exact T.mul_mem ht ((mem_normalizer_iff.1 (hDT hd) t⁻¹).1 (T.inv_mem ht))
    have hdvd : Nat.card ↥⁅N, D⁆ ∣ 2 ^ k := hTcard ▸ card_dvd_of_le hle
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.M591D
