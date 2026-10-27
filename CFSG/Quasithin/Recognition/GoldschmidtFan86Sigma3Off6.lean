module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off5
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off4

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.exists_offender (h : Hyp3 H S x) :
    ∃ A, IsMaxElemAbelian S A ∧ ¬ A ≤ oQ H := by
  by_contra hcon
  push Not at hcon
  exact h.not_J_le_Q (iSup₂_le fun A hA => hcon A hA)

theorem Hyp3.offender (h : Hyp3 H S x) :
    Nat.card (nQ H x) = 4 ∧
      ∃ a ∈ thompsonJ S, a ∈ S ∧ a ∉ oQ H ∧ ∃ n ∈ nQ H x, a * n * a⁻¹ ≠ n := by
  obtain ⟨A, hA, hAQ⟩ := h.exists_offender
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.1 hAQ
  have haS : a ∈ S := hA.1 haA
  have haJ : a ∈ thompsonJ S := le_iSup₂ (f := fun A (_ : IsMaxElemAbelian S A) => A) A hA haA
  have hx3 := mul_mul_eq_one_of_orderOf h.ord
  have hNn : (nQ H x).Normal := h.sig.nQ_normal h.ord
  have hxN : ∀ n ∈ nQ H x, x * n * x⁻¹ ∈ nQ H x := fun n hn => hNn.conj_mem n hn x
  have hxinv : ∀ n ∈ nQ H x, x⁻¹ * n * x ∈ nQ H x := fun n hn => by
    simpa using hNn.conj_mem n hn x⁻¹
  have hfix : ∀ n ∈ nQ H x, x * n * x⁻¹ = n → n = 1 := fun n hn => nQ_fix hx3 hn
  have hNS : nQ H x ≤ S := (nQ_le x).trans (oneCenter_le.trans h.sig.Q_le_S)
  have hQN : ∀ q ∈ oQ H, ∀ n ∈ nQ H x, q * n = n * q := fun q hq n hn =>
    ((mem_oneCenter.1 (nQ_le x hn)).2.2 q hq).symm
  obtain ⟨q, hq, haxq⟩ := h.sig.inv_mod h.ord haS haQ
  have hb1 := offender_bound (nQ_elem x) hNS hA hQN h.sig.index_Q
  have hb2 : Nat.card ↥(nQ H x ⊓ Subgroup.centralizer (A : Set H)) ≤
      Nat.card ↥(nQ H x ⊓ Subgroup.centralizer {a}) :=
    Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.2 haA)))
  have hb3 := card_sq_le hx3 hxN hxinv hfix (hQN q hq) haxq
  have hCpos : 0 < Nat.card ↥(nQ H x ⊓ Subgroup.centralizer {a}) := Nat.card_pos
  have hC2 : Nat.card ↥(nQ H x ⊓ Subgroup.centralizer {a}) ≤ 2 := by
    nlinarith
  have hN4 : Nat.card (nQ H x) ≤ 4 := by omega
  have hN1 : Nat.card (nQ H x) ≠ 1 := fun h1 => h.nQ_ne_bot (Subgroup.card_eq_one.1 h1)
  have hNp : IsPGroup 2 (nQ H x) := fun g => ⟨1, Subtype.ext (by simpa using (nQ_elem x).2 g g.2)⟩
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hN4' : Nat.card (nQ H x) = 4 := by
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    · rw [pow_zero] at hk
      exact absurd hk hN1
    · exfalso
      rw [pow_one] at hk
      obtain ⟨n, hn1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(nQ H x))).1 hk
      have hxn : x * (n : H) * x⁻¹ = (n : H) := by
        have h2 : (⟨x * (n : H) * x⁻¹, hxN _ n.2⟩ : ↥(nQ H x)) = n := by
          apply huniq
          intro h3
          apply hn1
          apply Subtype.ext
          have h4 : x * (n : H) * x⁻¹ = 1 := congrArg Subtype.val h3
          have := congrArg (fun w => x⁻¹ * w * x) h4
          calc (n : H) = x⁻¹ * (x * (n : H) * x⁻¹) * x := by group
            _ = 1 := by rw [h4]; group
        exact congrArg Subtype.val h2
      exact hn1 (Subtype.ext (hfix _ n.2 hxn))
    · rw [hk]; norm_num
  refine ⟨hN4', a, haJ, haS, haQ, ?_⟩
  by_contra hall
  push Not at hall
  have hle : nQ H x ≤ Subgroup.centralizer {a} := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hall n hn
      calc n * a = (a * n * a⁻¹) * a := by rw [this]
        _ = a * n := by group)
  rw [inf_eq_left.2 hle, hN4'] at hC2
  omega

end CFSG.Quasithin.Fan86.Sigma3
