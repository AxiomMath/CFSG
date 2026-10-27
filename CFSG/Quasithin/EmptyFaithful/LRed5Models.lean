module

public import CFSG.Quasithin.EmptyFaithful.LRed4IrrB
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinear
public import CFSG.Quasithin.Background.FFC4Ext
public import CFSG.Quasithin.Background.FFC5T8

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace LRed5

section Orders

theorem sl2_ne {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : N = 168 ∨ N = 360) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ N := by
  rcases LRed4.sl2_card_cases hn with h | h | h | h <;> omega

theorem sl3_cases {n : ℕ} (hn : 1 ≤ n) :
    n = 1 ∨ 60480 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    omega
  · right
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 4 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 4 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
    calc 60480 = 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) := by norm_num
      _ ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h1 1))

theorem sp4_ge {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    720 ≤ Nat.card ↥(StatedSp 2 F) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : 2 ^ 4 ≤ (2 ^ n) ^ (2 ^ 2) := by
    have := Nat.pow_le_pow_left hq (2 ^ 2)
    simpa using this
  have h2 : 2 ^ 2 ≤ (2 ^ n) ^ (2 * 1) := by
    have := Nat.pow_le_pow_left hq (2 * 1)
    simpa using this
  have h3 : 2 ^ 4 ≤ (2 ^ n) ^ (2 * 2) := by
    have := Nat.pow_le_pow_left hq (2 * 2)
    simpa using this
  calc 720 = 2 ^ 4 * ((2 ^ 2 - 1) * (2 ^ 4 - 1)) := by norm_num
    _ ≤ (2 ^ n) ^ (2 ^ 2) * (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))

theorem g2_ge {n : ℕ} (hn : 1 ≤ n) :
    12096 ≤ (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : 2 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 2 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
  calc 12096 = 2 ^ 6 * ((2 ^ 6 - 1) * (2 ^ 2 - 1)) := by norm_num
    _ ≤ (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le_sub_right h1 1) (Nat.sub_le_sub_right h2 1))

end Orders

section B42

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem b42_cases
    (hc : Nat.card ↥L = 168 ∨ Nat.card ↥L = 360)
    (h : B42ModulePair L U Z) :
    (Nat.card ↥L = 168 ∧ ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥L,
        (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L U Z π) ∨
      (Nat.card ↥L = 360 ∧ ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥L,
        (FFModel.altDn 6).RealizesVia L U Z π) := by
  rcases h with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ |
    ⟨n, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨α, π, hπ⟩ |
    ⟨K, _, _, Γ₀, -, -, hhat, -, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hK] at h1
    exact sl2_ne (EmptyFaithfulMultiple.FFL.one_le_of_card hK) hc h1.symm
  ·
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hK] at h1
    rcases sl3_cases (EmptyFaithfulMultiple.FFL.one_le_of_card hK) with hm | hm
    · left
      subst hm
      refine ⟨?_, _, FFC.realizesVia_zmod (by rw [hK]; norm_num) hπ⟩
      rw [h1]
      norm_num
    · exfalso
      rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    have h2 := sp4_ge hK (EmptyFaithfulMultiple.FFL.one_le_of_card hK)
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have := FFC.charP_two_of_card_pow hK
    have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 K) :=
      (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hK, hK] at hcard
    have h2 := g2_ge (EmptyFaithfulMultiple.FFL.one_le_of_card hK)
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have := EmptyFaithfulMultiple.FFL.charP_two_of_card hK
    have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K :=
      Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia
      (EmptyFaithfulMultiple.FFL.zornQ_faithful hle) hπ
    change Nat.card ↥L = Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ at h1
    rw [EmptyFaithfulMultiple.FFL.card_commutator_quasithinG2 (by simpa using hK)] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful le_rfl) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 5)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    rcases hc with hc | hc <;> omega
  ·
    right
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    exact ⟨h1, π, hπ⟩
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.altDn_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (G64.a7Four_faithful α) hπ
    change Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin 7)) at h1
    rw [EmptyFaithfulMultiple.FFL.card_alt (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d hπ
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d (FFC.realizesVia_zmod (by simpa using hK) hπ)
    rw [card_statedSL_four_zmod1527d] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d (FFC.realizesVia_zmod (by simpa using hK) hπ)
    rw [card_statedSL_five_zmod1527d] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (FFC.extSq_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 4 (ZMod 2)) at h1
    rw [card_statedSL_four_zmod1527d] at h1
    rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := EmptyFaithfulMultiple.FFL.card_eq_of_realizesVia (FFC.extSq_faithful (by norm_num)) hπ
    change Nat.card ↥L = Nat.card ↥(StatedSL 5 (ZMod 2)) at h1
    rw [card_statedSL_five_zmod1527d] at h1
    rcases hc with hc | hc <;> omega

end B42

section B51

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem b51_cases
    (hc : Nat.card ↥L = 168 ∨ Nat.card ↥L = 360)
    (h : B51Part1 G L) :
    (Nat.card ↥L = 168 ∧
      ((∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥L,
          (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L (commV L) (fixV L ⊓ commV L) π) ∨
        DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 2)) ∨
      (Nat.card ↥L = 360 ∧ ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥L,
        (FFModel.altDn 6).RealizesVia L (commV L) (fixV L ⊓ commV L) π) := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨-, hB, -⟩ | ⟨-, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ |
    ⟨n, -, hn, π, U₁, U₂, ⟨hU, hU0⟩, h₁, h₂⟩ | ⟨-, n, hn, k, hk1, -, I, π, -, hind, hsup, hreal⟩
  · rcases b42_cases hc hB with ⟨h168, π, hπ⟩ | ⟨h360, π, hπ⟩
    · exact Or.inl ⟨h168, Or.inl ⟨π, hπ⟩⟩
    · exact Or.inr ⟨h360, π, hπ⟩
  ·
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at h1
    rcases sl3_cases (EmptyFaithfulMultiple.FFL.one_le_of_card hK) with hm | hm
    · subst hm
      refine Or.inl ⟨by rw [h1]; norm_num, Or.inr ?_⟩
      refine FFC.DirectSumOfCopies.zmod (K := K) (by rw [hK]; norm_num) ?_
      refine ⟨I, π, fun _ => bot_le, fun i => ?_, ?_, hreal⟩
      · rw [bot_sup_eq]
        exact disjoint_iff.mp (hind i)
      · rw [bot_sup_eq]
        exact hsup
    · exfalso
      rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d h₁
    rcases hn with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at h1
      rcases hc with hc | hc <;> omega
    · rw [card_statedSL_five_zmod1527d] at h1
      rcases hc with hc | hc <;> omega
  ·
    exfalso
    have h1 := card_eq_of_nat_realizes1527d (hreal ⟨0, hk1⟩)
    rcases hn with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at h1
      rcases hc with hc | hc <;> omega
    · rw [card_statedSL_five_zmod1527d] at h1
      rcases hc with hc | hc <;> omega

end B51

end LRed5

end CFSG.Quasithin
