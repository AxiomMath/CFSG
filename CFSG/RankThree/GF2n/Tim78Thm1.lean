module

public import CFSG.RankThree.GF2n.Tim78S33
public import CFSG.RankThree.GF2n.Tim78S3Setting

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneSub_omegaTwoSub_ne {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB2 : IsPGroup 2 B) (hne : PartTwo.omegaOneSub B ≠ B) :
    PartTwo.omegaOneSub (omegaTwoSub B) ≠ omegaTwoSub B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxV⟩ : ∃ x ∈ B, x ∉ PartTwo.omegaOneSub B := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (le_antisymm (PartTwo.omegaOneSub_le B) hcon)
  have hxx : x * x ≠ 1 := fun h => hxV ((mem_omegaOneSub_iff hBc).mpr ⟨hx, h⟩)
  obtain ⟨n, hn⟩ := hB2 ⟨x, hx⟩
  have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn')
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hxx
    rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hk]
    have : 2 ^ k ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
    simpa using this
  set y := x ^ 2 ^ (k - 2) with hy
  have hy4 : y ^ 4 = 1 := by
    rw [hy, ← pow_mul, show 2 ^ (k - 2) * 4 = 2 ^ k by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hk2], ← hk]
    exact pow_orderOf_eq_one x
  have hy2 : y * y ≠ 1 := by
    intro h
    have h1 : x ^ 2 ^ (k - 1) = 1 := by
      rw [show 2 ^ (k - 1) = 2 ^ (k - 2) * 2 by
        rw [← pow_succ, show k - 2 + 1 = k - 1 by omega], pow_mul, ← hy, sq]
      exact h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hk] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  intro h
  have hyU : y ∈ omegaTwoSub B := (mem_omegaTwoSub_iff hBc).mpr ⟨B.pow_mem hx _, hy4⟩
  rw [← h] at hyU
  exact hy2 ((mem_omegaOneSub_iff (comm_omegaTwoSub hBc)).mp hyU).2

theorem tim78_theorem1_of_eight_le (hGold : GoldschmidtInput) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {M B : Subgroup G} (H : HypH M B)
    (h8 : 8 ≤ Nat.card ↥(PartTwo.omegaOneSub B)) : Assembly.IsElemAbelian 2 B := by
  by_contra hnot
  have hne : PartTwo.omegaOneSub B ≠ B := by
    intro h
    apply hnot
    refine ⟨⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    rw [← h] at hx
    rw [sq]
    exact ((mem_omegaOneSub_iff H.comm).mp hx).2
  have hUV : PartTwo.omegaOneSub (omegaTwoSub B) = PartTwo.omegaOneSub B :=
    omegaOneSub_omegaTwoSub H.comm
  have S : S3Hyp M (omegaTwoSub B) :=
    { max := H.max
      fstar := H.fstar
      le := le_trans (omegaTwoSub_le B) H.le
      normal := H.le_normalizer_omegaTwo
      comm := comm_omegaTwoSub H.comm
      two := H.two.to_le (omegaTwoSub_le B)
      ti := isTI_omegaTwoSub H.comm H.ti
      exp := fun x hx => pow_four_of_mem_omegaTwoSub H.comm hx
      ne := omegaOneSub_omegaTwoSub_ne H.comm H.two hne
      card4 := by rw [hUV]; omega }
  have hS : SigmaComm (PartTwo.omegaOneSub (omegaTwoSub B)) :=
    sigmaComm_of_elem fun R hR =>
      tim78_3_1_of_eight_le hCen hU S.comm S.two S.ti S.exp S.ne (by rw [hUV]; exact h8) hR
  exact S.false_of_sigmaComm hGold hCen hU H.o2 hS

end CFSG.RankThree.GF2n.Tim78
