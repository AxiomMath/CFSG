module

public import CFSG.Quasithin.Background.SmithC27Setup
public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.C2PushBlocks

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.C2Push

variable {G : Type} [Group G]

private theorem conjClosure_eq_self' {K R : Subgroup G}
    (h : R ≤ Subgroup.normalizer (K : Set G)) : conjClosure K R = K :=
  le_antisymm (conjClosure_le fun _ hs x hx => (Subgroup.mem_normalizer_iff.mp (h hs) x).mp hx)
    (le_conjClosure K R)

private theorem conjByElt_eq_self {K : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) : conjByElt r K = K := by
  ext x
  rw [mem_conjByElt]
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr) x)
  simp only [inv_inv] at h
  rw [← h]

private theorem card_quot_eq_of_surj {K : Subgroup G} {Q : Type*} [Group Q] (φ : ↥K →* Q)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card Q :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).toEquiv

variable [Finite G]

theorem Hyp27.conjClosure_sup_eq {H R M K : Subgroup G} (h : Hyp27 H R M K) :
    conjClosure K R ⊔ R = K ⊔ R := by
  rw [conjClosure_eq_self' h.norm]

theorem chi0_of_sylow (hC129 : ASC129Statement G) {H R M K : Subgroup G} (h : Hyp27 H R M K)
    (hS : IsSylowTwoOf R (K ⊔ R)) :
    IsChi0Block (K ⊔ R) K ∧ IsBorelOfBlock K (K ⊓ (M ⊓ (K ⊔ R))) ∧ ⁅K, thompsonJ R⁆ = K := by
  have h23 := h.hypC23_sup
  obtain ⟨r, Lb, -, hLb, hprod⟩ :=
    hC129 (K ⊔ R) R (M ⊓ (K ⊔ R)) h23.sqtk h.charTwo_sup hS h23.cgs h23.le
  have hY := h.conjClosure_sup_eq
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · obtain ⟨i, hi⟩ := hq
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      ((hLb i).1.1.1.2.2.2.1).resolve_right hi
    have hB : IsBlock2 (conjClosure K R ⊔ R) (Lb i) := by
      rw [hY]
      exact (hLb i).1.1
    obtain ⟨t, ht, hBt⟩ :=
      exists_eq_conjByElt_of_isBlock2 h.hyp.radical h.comp h.quasi hB hBq
    have hBK : Lb i = K := hBt.trans (conjByElt_eq_self (h.norm ht))
    have hi' := hLb i
    rw [hBK] at hi'
    exact hi'
  · exfalso
    push Not at hq
    apply h.not_le
    have hsyl : IsSylowTwoOf R (conjClosure K R ⊔ R) := by
      rw [hY]
      exact hS
    refine le_of_isBlock2_card_three h.comp h.quasi h.hyp.radical.1 hsyl
      h.R_le_M Lb (fun i => ⟨?_, hq i⟩) ?_
    · rw [hY]
      exact (hLb i).1.1
    · intro x hx
      rw [hY] at hx ⊢
      obtain ⟨m, hm, y, hy, hxy⟩ := hprod x hx
      exact ⟨m, ⟨hm.2, hm.1⟩, y, hy, hxy⟩

theorem not_sylow_of_not_chi0 (hC129 : ASC129Statement G) {H R M K : Subgroup G}
    (h : Hyp27 H R M K) (hK : ¬ IsChi0Block (K ⊔ R) K) : ¬ IsSylowTwoOf R (K ⊔ R) :=
  fun hS => hK (chi0_of_sylow hC129 h hS).1

private theorem two_pow_mul_ne (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 2520 := by
  intro h
  have hdvd : 2 ^ n ∣ 2 ^ 3 * 315 := ⟨_, h.symm⟩
  have hn : n ≤ 3 := by
    have hcop : Nat.Coprime (2 ^ n) 315 := Nat.Coprime.pow_left _ (by norm_num)
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1
      (hcop.dvd_of_dvd_mul_right hdvd)
    exact this
  interval_cases n <;> norm_num at h

omit [Finite G] in
theorem not_isChi0Block_of_card {X K : Subgroup G}
    (hK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520) : ¬ IsChi0Block X K := by
  rintro ⟨-, ⟨n, -, F, _, _, hF, α, hα, hker, -⟩ | h3 | ⟨α, hα, hker, -⟩⟩
  · rw [card_quot_eq_of_surj α hα hker, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_eq_fintype_card, hF] at hK
    exact two_pow_mul_ne n hK
  · rw [C2Six.natCard_pCore_quotient_of_isAltType_three h3] at hK
    norm_num at hK
  · rw [card_quot_eq_of_surj α hα hker, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at hK
    norm_num [Nat.factorial] at hK

theorem lin2_or_alt5_of_isChi0Block {X K : Subgroup G} (hK : IsChi0Block X K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    (∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 5 := by
  rcases hK.2 with h1 | h3 | h5
  · exact Or.inl h1
  · exfalso
    have hc := C2Six.natCard_pCore_quotient_of_isAltType_three h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic (↥K ⧸ CFSG.pCore 2 ↥K) := isCyclic_of_prime_card hc
    have hnt : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
    have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ CFSG.pCore 2 ↥K) inferInstance
  · exact Or.inr h5

theorem isChiBlock2_of_sylow (hC129 : ASC129Statement G) {H R M K : Subgroup G}
    (h : Hyp27 H R M K) (hS : IsSylowTwoOf R (K ⊔ R)) : IsChiBlock2 H K := by
  have hc := (chi0_of_sylow hC129 h hS).1
  have hKH : K ≤ H := le_of_mem_cComp h.comp
  refine ⟨⟨hc.1.1, hKH, (isSubnormal_iff_subgroupOf hKH).mp (subnormal_of_mem_cComp h.comp)⟩, ?_⟩
  rcases lin2_or_alt5_of_isChi0Block hc h.quasi with h1 | h5
  · exact Or.inl h1
  · exact Or.inr ⟨5, by decide, h5⟩

end CFSG.Quasithin.SmithC27
