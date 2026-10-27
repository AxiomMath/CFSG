module

public import CFSG.Quasithin.H13.L32A755h
public import CFSG.Quasithin.H13.L32A753g

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

structure G2Facts : Prop where
  card_derived : Nat.card ↥(g2Derived (ZMod 2)) = 6048
  inner_iff : ∀ i < 64, (sEltG i ∈ g2Derived (ZMod 2) ↔ i ∈ innerS)

theorem g2Facts :
    G2Facts := by
  refine ⟨?_, fun i hi => mem_g2Derived_iff hi⟩
  have h1 := (g2Derived (ZMod 2)).card_mul_index
  rw [B45U33.index_g2Derived, card_g2Two] at h1
  omega

theorem mul_self_Q (q : ModQ) : q * q = 1 := by
  obtain ⟨a, rfl⟩ := codeQ_surjective q
  rw [← codeQ_xor, o0Xor_self, codeQ_zero]

@[expose] noncomputable def commHom (g : ↥(quasithinG2 (ZMod 2))) : ModQ →* ModQ where
  toFun q := g2QAct (ZMod 2) g q * q⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv_rev]
    have : ∀ x y : ModQ, x * y = y * x := fun x y => mul_comm x y
    rw [this b⁻¹ a⁻¹]
    simp only [mul_assoc]
    rw [mul_left_comm (g2QAct (ZMod 2) g b) a⁻¹]

theorem eq_one_of_transv {g : ↥(quasithinG2 (ZMod 2))} {c : ModQ}
    (h : ∀ q : ModQ, g2QAct (ZMod 2) g q * q⁻¹ = 1 ∨ g2QAct (ZMod 2) g q * q⁻¹ = c) : g = 1 := by
  set φ := g2QAct (ZMod 2) g with hφ
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  by_contra hg1
  have hφ1 : φ ≠ 1 := fun h' => hg1 (g2QAct_injective (h'.trans (map_one _).symm))
  have hinv : ∀ q : ModQ, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (mul_self_Q q)
  have hc : φ c = c := by
    rcases h c with h1 | h1
    · exact mul_inv_eq_one.1 h1
    · have e : φ c = c * c := by
        calc φ c = (φ c * c⁻¹) * c := by group
          _ = c * c := by rw [h1]
      rw [mul_self_Q] at e
      have : c = 1 := φ.injective (e.trans (map_one φ).symm)
      rw [this, map_one]
  have hφ2 : φ ^ 2 = 1 := by
    refine MulEquiv.ext fun q => ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rcases h q with h1 | h1
    · rw [mul_inv_eq_one.1 h1, mul_inv_eq_one.1 h1]
    · have e : φ q = c * q := by
        calc φ q = (φ q * q⁻¹) * q := by group
          _ = c * q := by rw [h1]
      rw [e, map_mul, hc, e, ← mul_assoc, mul_self_Q, one_mul]
  set B : Subgroup (MulAut ModQ) := Subgroup.zpowers φ with hB
  have hcardB : Nat.card B = 2 := by
    rw [hB, Nat.card_zpowers]
    exact orderOf_eq_prime hφ2 hφ1
  have hBX : B ≤ (g2QAct (ZMod 2)).range := by
    rw [hB, Subgroup.zpowers_le]
    exact ⟨g, rfl⟩
  have hB1 : B ≠ ⊥ := fun h' => by
    rw [h', Subgroup.card_bot] at hcardB
    omega
  have hBe : IsElemAbelian2 B := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφ2, one_zpow]
  have hker : ∀ q, q ∈ (commHom g).ker → q ∈ fixV B := by
    intro q hq
    have h1 : φ q = q := mul_inv_eq_one.1 hq
    exact M753.mem_fixV_zpowers_of h1
  have hrange : Nat.card (commHom g).range ≤ 2 := by
    have hle : (commHom g).range ≤ Subgroup.zpowers c := by
      rintro _ ⟨q, rfl⟩
      rcases h q with h1 | h1
      · change φ q * q⁻¹ ∈ _
        rw [h1]
        exact Subgroup.one_mem _
      · change φ q * q⁻¹ ∈ _
        rw [h1]
        exact Subgroup.mem_zpowers c
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two, mul_self_Q])
  have hfix : 32 ≤ Nat.card (fixV B) := by
    have h1 := (commHom g).ker.card_mul_index
    rw [Subgroup.index_ker, card_ModQ] at h1
    have h2 : Nat.card (commHom g).ker ≤ Nat.card (fixV B) :=
      Subgroup.card_le_of_le fun q hq => hker q hq
    have hpos : 0 < Nat.card (commHom g).range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card (commHom g).ker * Nat.card (commHom g).range ≤ 31 * 2 :=
      Nat.mul_le_mul (by omega) hrange
    omega
  obtain ⟨h8, -⟩ := B42U33.offender_exact hBX hB1 hBe (by rw [card_ModQ, hcardB]; omega)
  omega

@[expose] def trW : List (List ℕ) := [[2, 2, 1, 1, 2, 2], [2, 2, 1, 2, 1, 2, 1, 2],
  [1, 2, 2, 1, 1, 2, 2], [], [2, 2, 1, 2], [1, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2], [1, 1, 2, 2],
  [2, 1, 1, 2, 2], [1, 1, 2, 2, 1, 1, 2], [1, 2, 1, 2], [1, 1, 2], [2, 1, 2, 2],
  [1, 1, 2, 2, 1, 2, 2], [1, 2, 1, 1, 2], [2, 2], [2, 2, 1, 1, 2], [1, 1, 2, 1, 2],
  [1, 2, 1, 1, 2, 2], [2], [2, 2, 1, 2, 2], [1, 1, 2, 1, 1, 2], [1, 2, 1, 2, 2], [1, 2, 2],
  [2, 1, 2], [1, 1, 2, 1, 1, 2, 2], [1, 2, 2, 1, 1, 2], [1, 2], [2, 1, 1, 2], [1, 1, 2, 1, 2, 2],
  [1, 2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 1, 2], [1, 1, 2, 1, 2, 1, 2], [1, 2, 1, 2, 1, 2],
  [2, 1, 2, 1, 2], [2, 2, 1, 1, 2, 1, 1, 2], [1, 2, 1, 1, 2, 1, 2], [2, 1, 1, 2, 1, 2],
  [2, 1, 2, 2, 1, 1, 2], [2, 2, 1, 2, 1, 2], [1, 2, 1, 2, 1, 2, 2], [2, 1, 2, 2, 1, 1, 2, 2],
  [2, 1, 1, 2, 2, 1, 1, 2], [2, 2, 1, 2, 2, 1, 2, 2], [1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 1, 1, 2, 2],
  [2, 1, 1, 2, 1, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2], [1, 2, 1, 2, 2, 1, 1, 2, 2],
  [2, 1, 1, 2, 1, 1, 2], [2, 1, 2, 2, 1, 2, 2], [2, 2, 1, 1, 2, 1, 2], [1, 2, 1, 2, 1, 1, 2, 2],
  [2, 1, 1, 2, 2, 1, 2], [2, 1, 2, 1, 1, 2], [2, 2, 1, 2, 1, 1, 2], [2, 2, 1, 2, 2, 1, 2],
  [2, 1, 2, 1, 2, 2], [2, 1, 1, 2, 1, 2, 2], [2, 2, 1, 2, 2, 1, 1, 2], [1, 2, 1, 1, 2, 2, 1, 2],
  [2, 1, 2, 2, 1, 2], [2, 1, 1, 2, 2, 1, 2, 2]]

theorem trW_spec : ∀ c ∈ ptsQ, (∀ t ∈ trW.getD (c / 2 - 1) [], t = 1 ∨ t = 2) ∧
    applyG (trW.getD (c / 2 - 1) []) 8 ∈ o0Codes ∧ nq (applyG (trW.getD (c / 2 - 1) []) 8) = c := by
  decide +kernel

theorem g2QAct_wordGG {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) {c : ℕ} (hc : c ∈ o0Codes) :
    g2QAct (ZMod 2) (wordGG w) (ptQ c) = ptQ (applyG w c) := by
  rw [g2QAct_ptQ _ hc]
  congr 1
  exact o0Act_wordGG hw ⟨c, hc⟩

theorem exists_g2Derived_pt {c : ℕ} (hc : c ∈ ptsQ) :
    ∃ g ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) g (ptQ 8) = ptQ c := by
  obtain ⟨hw, hmem, hnq⟩ := trW_spec c hc
  have h8 : (8 : ℕ) ∈ o0Codes := by decide
  refine ⟨wordGG (trW.getD (c / 2 - 1) []), wordGG_mem_derived _, ?_⟩
  rw [g2QAct_wordGG hw h8, ← ptQ_nq hmem, hnq]

theorem exists_g2Derived_of_ne {p : ModQ} (hp : p ≠ 1) :
    ∃ g ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) g (ptQ 8) = p := by
  obtain ⟨c, hc, rfl⟩ := exists_ptQ hp
  exact exists_g2Derived_pt hc

theorem isPGroup_sSubG : IsPGroup 2 ↥sSubG :=
  IsPGroup.of_card (n := 6) (by rw [card_sSubG]; norm_num)

theorem card_S0 (hG : G2Facts) : Nat.card ↥(sSubG ⊓ g2Derived (ZMod 2)) = 32 := by
  classical
  rw [card_eq_idx inf_le_left]
  have h : idx (sSubG ⊓ g2Derived (ZMod 2)) = innerS.toFinset := by
    ext i
    rw [mem_idx, List.mem_toFinset]
    constructor
    · rintro ⟨hi, -, hiD⟩
      exact (hG.inner_iff i hi).1 hiD
    · intro hi
      have hi64 := innerS_lt i hi
      exact ⟨hi64, mem_sSubG.2 ⟨i, hi64, rfl⟩, (hG.inner_iff i hi64).2 hi⟩
  rw [h]
  decide

theorem le_of_two_pow_dvd {n m : ℕ} (hm : m % 2 = 1) (h : 2 ^ n ∣ 2 ^ 5 * m) : 2 ^ n ≤ 2 ^ 5 := by
  by_contra hlt
  push Not at hlt
  have h6 : 6 ≤ n := by
    by_contra h6
    push Not at h6
    exact absurd hlt (not_lt.2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have : 2 ^ 6 ∣ 2 ^ 5 * m := (Nat.pow_dvd_pow 2 h6).trans h
  rw [show 2 ^ 6 = 2 ^ 5 * 2 by norm_num] at this
  have := Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  omega

theorem le_sSubG_of_norm (hG : G2Facts) {X : Subgroup ↥(quasithinG2 (ZMod 2))}
    (hX2 : IsPGroup 2 X)
    (hN0 : sSubG ⊓ g2Derived (ZMod 2) ≤ Subgroup.normalizer (X : Set ↥(quasithinG2 (ZMod 2))))
    (hN : ¬ X ≤ g2Derived (ZMod 2) →
      sSubG ≤ Subgroup.normalizer (X : Set ↥(quasithinG2 (ZMod 2)))) : X ≤ sSubG := by
  by_cases hXD : X ≤ g2Derived (ZMod 2)
  · set S₀ := sSubG ⊓ g2Derived (ZMod 2) with hS₀
    have hY := hX2.to_sup_of_normal_left' (isPGroup_sSubG.to_le inf_le_left) hN0
    have hYD : X ⊔ S₀ ≤ g2Derived (ZMod 2) := sup_le hXD inf_le_right
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hY
    have hdvd : Nat.card ↥(X ⊔ S₀) ∣ Nat.card ↥(g2Derived (ZMod 2)) :=
      Subgroup.card_dvd_of_le hYD
    rw [hn, hG.card_derived, show 6048 = 2 ^ 5 * 189 by norm_num] at hdvd
    have hle := le_of_two_pow_dvd (by norm_num) hdvd
    have heq : X ⊔ S₀ = S₀ := (Subgroup.eq_of_le_of_card_ge le_sup_right
      (by rw [hn, card_S0 hG]; exact hle)).symm
    exact le_sup_left.trans (heq.le.trans inf_le_left)
  · have hY := hX2.to_sup_of_normal_left' isPGroup_sSubG (hN hXD)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hY
    have hdvd : Nat.card ↥(X ⊔ sSubG) ∣ Nat.card ↥(quasithinG2 (ZMod 2)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hn, card_g2Two, show 12096 = 2 ^ 6 * 189 by norm_num] at hdvd
    have hle : 2 ^ n ≤ 2 ^ 6 := by
      by_contra hlt
      push Not at hlt
      have h7 : 7 ≤ n := by
        by_contra h7
        push Not at h7
        exact absurd hlt (not_lt.2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have : 2 ^ 7 ∣ 2 ^ 6 * 189 := (Nat.pow_dvd_pow 2 h7).trans hdvd
      norm_num at this
    have heq : X ⊔ sSubG = sSubG := (Subgroup.eq_of_le_of_card_ge le_sup_right
      (by rw [hn, card_sSubG]; exact hle)).symm
    exact le_sup_left.trans heq.le

theorem collQ_tri {p q r : ModQ} (hpq : CollQ p q) (hrp : CollQ r p) (hrq : CollQ r q) :
    r = p * q := by
  obtain ⟨hp1, hpq'⟩ := collQ_mul hpq
  obtain ⟨hne, -, -⟩ := collQ_ne hpq
  exact collQ_common hne (collQ_symm hrp) (collQ_symm hrq) hp1 hpq'

theorem zC2_conj : mmul (wMatC [2]) (sM 2) = mmul (sM 43) (wMatC [2]) := by
  decide +kernel

end CFSG.Quasithin.H13.L32A.M755
