module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

theorem le_center_or_comm {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q)
    [hN : N.Normal] : N ≤ Subgroup.center Q ∨ ∀ a b : Q ⧸ N, a * b = b * a := by
  have := hQ.2.1
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hNm.eq_bot_or_eq_top with h | h
  · left
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center Q) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) := Subgroup.mem_map_of_mem _ hn
    rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · right
    have key : ∀ q : Q, ∃ z ∈ Subgroup.center Q,
        (QuotientGroup.mk q : Q ⧸ N) = QuotientGroup.mk z := by
      intro q
      have hq : QuotientGroup.mk' (Subgroup.center Q) q ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hq
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnq
      refine ⟨n⁻¹ * q, hnq, ?_⟩
      rw [QuotientGroup.eq]
      have e : q⁻¹ * (n⁻¹ * q) = q⁻¹ * n⁻¹ * q⁻¹⁻¹ := by group
      rw [e]
      exact hN.conj_mem _ (N.inv_mem hn) _
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    obtain ⟨z₁, hz₁, e₁⟩ := key a
    obtain ⟨z₂, hz₂, e₂⟩ := key b
    rw [e₁, e₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hz₁ z₂]

theorem eq_bot_of_odd_normal {Q R : Type*} [Group Q] [Finite Q] [Group R]
    (hs : IsSimpleGroup (Q ⧸ CFSG.pCore 2 Q)) {D : Subgroup Q} [hDn : D.Normal]
    (hD : Odd (Nat.card D)) (χ : Q →* R) (hχ : Function.Surjective χ) (hDχ : D ≤ χ.ker)
    (hR : ¬ IsPGroup 2 R) : D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hs
  have hDm : (D.map (QuotientGroup.mk' (CFSG.pCore 2 Q))).Normal :=
    hDn.map _ (QuotientGroup.mk'_surjective _)
  rcases hDm.eq_bot_or_eq_top with h | h
  · have hDle : D ≤ CFSG.pCore 2 Q := by
      intro d hd
      have : QuotientGroup.mk' (CFSG.pCore 2 Q) d ∈
          D.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) := Subgroup.mem_map_of_mem _ hd
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hDp : IsPGroup 2 D := CFSG.pCore_isPGroup.to_le hDle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hDp
    rw [hn] at hD
    cases n with
    | zero => rwa [pow_zero, Subgroup.card_eq_one] at hn
    | succ k =>
      exact absurd hD (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  · exfalso
    apply hR
    intro r
    obtain ⟨q, rfl⟩ := hχ r
    have hq : QuotientGroup.mk' (CFSG.pCore 2 Q) q ∈
        D.map (QuotientGroup.mk' (CFSG.pCore 2 Q)) := h ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdq⟩ := Subgroup.mem_map.mp hq
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdq
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨_, hdq⟩ : ↥(CFSG.pCore 2 Q))
    refine ⟨k, ?_⟩
    have h1 : χ q = χ (d⁻¹ * q) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp (hDχ hd), inv_one, one_mul]
    have h2 : (d⁻¹ * q) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1, ← map_pow, h2, map_one]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
