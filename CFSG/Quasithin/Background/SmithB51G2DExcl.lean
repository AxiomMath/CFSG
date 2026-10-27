module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.G64ExtSq

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit

theorem two_pow_inj {a b : ℕ} (h : (2 : ℕ) ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective le_rfl h

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem g2_num_ge {q : ℕ} (hq : 4 ≤ q) : 6048 ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
  have h1 : 4 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have h2 : 4 ^ 6 - 1 ≤ q ^ 6 - 1 := Nat.sub_le_sub_right h1 1
  have h3 : 4 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  calc 6048 ≤ 4 ^ 6 * ((4 ^ 6 - 1) * (4 ^ 2 - 1)) := by norm_num
    _ ≤ _ := h4

theorem sl2_ne_g2 {q : ℕ} (hq : 4 ≤ q) :
    q ^ 3 * ((q ^ 3) ^ 2 - 1) ≠ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
  intro h
  have h6 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  rw [h6] at h
  have hpos : 0 < q ^ 3 * (q ^ 6 - 1) := by
    have : 4 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have : 0 < q ^ 3 := by positivity
    have : 0 < q ^ 6 - 1 := by omega
    positivity
  have h2 : 1 < q ^ 3 * (q ^ 2 - 1) := by
    have : 4 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have : 1 ≤ q ^ 2 - 1 := by omega
    nlinarith
  have h' : q ^ 3 * (q ^ 6 - 1) * 1 = q ^ 3 * (q ^ 6 - 1) * (q ^ 3 * (q ^ 2 - 1)) := by
    rw [mul_one]
    exact h.trans (by ring)
  have := Nat.eq_of_mul_eq_mul_left hpos h'
  omega

theorem sl3_ne_g2 {q : ℕ} (hq : 4 ≤ q) :
    (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)) ≠
      q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
  intro h
  have e1 : (q ^ 2) ^ 3 = q ^ 6 := by ring
  have e2 : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [e1, e2] at h
  have hpos : 0 < q ^ 6 * (q ^ 6 - 1) := by
    have : 4 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have : 0 < q ^ 6 := by positivity
    have : 0 < q ^ 6 - 1 := by omega
    positivity
  have h' : q ^ 6 * (q ^ 6 - 1) * (q ^ 4 - 1) = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    calc q ^ 6 * (q ^ 6 - 1) * (q ^ 4 - 1) = q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1)) := by ring
      _ = q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := h
      _ = _ := by ring
  have h4 := Nat.eq_of_mul_eq_mul_left hpos h'
  have : 4 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

section Cards

variable {S : Type} [CommGroup S]

theorem card_eq_mod {D : FFModel} {H : Subgroup (MulAut S)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) : Nat.card S = Nat.card D.Mod := by
  have := G64.RealizesVia.card_eq h
  rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at this

theorem card_natMod_fin {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ Fintype.card ι := by
  rw [← Nat.card_congr (MulEquiv.ofBijective (G64.natQuot Γ)
    ⟨G64.natQuot_injective, G64.natQuot_surjective⟩).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem card_zornQMod {K : Type} [Field K] [Finite K] [CharP K 2]
    (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) :
    Nat.card (FFModel.zornQ Γ).Mod = Nat.card K ^ 6 := by
  rw [show Nat.card (FFModel.zornQ Γ).Mod = Nat.card (Multiplicative (Ix3 → K)) from
    Nat.card_congr (zornSecEquiv (F := K) Γ).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Ix3), Fintype.card_sum, Fintype.card_fin]

theorem card_eq_gam {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut S)} {U Z : Subgroup S}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) : Nat.card H = Nat.card D.Gam :=
  (Nat.card_congr (FFC.equivOfRealizes hD h).toEquiv).symm

end Cards

theorem one_le_of_card {K : Type} [Field K] [Finite K] {m : ℕ} (h : Nat.card K = 2 ^ m) :
    1 ≤ m := by
  by_contra h0
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [h, show m = 0 by omega, pow_zero] at h1
  exact lt_irrefl _ h1

theorem case4_of_b42 (hIdent : AsB42Ident) {S : Type} [CommGroup S] [Finite S]
    (hS2 : ∀ s : S, s ^ 2 = 1) {Γ Λ B : Subgroup (MulAut S)} (hHyp : B4Hyp Γ Λ)
    (hB : IsFFStarOffender Γ B) (hc : B42Conclusion Γ Λ B) {n : ℕ} (hn : 1 ≤ n)
    (hcardS : Nat.card S = (2 ^ n) ^ 6)
    (hΛ : (n = 1 ∧ Nat.card Λ = 6048) ∨
      (2 ≤ n ∧ Nat.card Λ = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)))) :
    qOf Γ = ((1 : ℚ) : WithTop ℚ) ∧ Nat.card B = 2 ^ (3 * n) ∧ G2Natural (ffJ Γ) ⊤ ⊥ n := by
  have hΛge : 6048 ≤ Nat.card Λ := by
    rcases hΛ with ⟨-, h⟩ | ⟨h2, h⟩
    · omega
    · rw [h]
      exact g2_num_ge (four_le_two_pow h2)
  have hΛ20160 : Nat.card Λ ≠ 20160 := by
    rcases hΛ with ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · rw [h]
      exact ne_g2_num1527d (Or.inl rfl)
  have hS6 : ∀ k : ℕ, Nat.card S = 2 ^ k → k = 6 * n := fun k hk => by
    rw [hcardS, ← pow_mul] at hk
    exact (two_pow_inj hk).symm.trans (by ring)
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  ·
    exfalso
    obtain ⟨-, ⟨m, K₁, _, _, hK₁, π, hπ⟩, -, -⟩ := h1
    have hc1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hK₁] at hc1
    have hs := card_eq_mod hπ
    rw [card_natMod_fin, Fintype.card_fin, hK₁, ← pow_mul] at hs
    have hm : m * 2 = 6 * n := hS6 _ hs
    rcases hΛ with ⟨rfl, h⟩ | ⟨h2, h⟩
    · have hm3 : m = 3 := by omega
      subst hm3
      rw [h] at hc1
      norm_num at hc1
    · have hm3 : m = 3 * n := by omega
      have e : (2 : ℕ) ^ m = (2 ^ n) ^ 3 := by rw [hm3, ← pow_mul, mul_comm]
      rw [h, e] at hc1
      exact sl2_ne_g2 (four_le_two_pow h2) hc1.symm
  ·
    exfalso
    obtain ⟨-, ⟨m, K₁, _, _, hK₁, π, hπ⟩, -⟩ := h2
    have hc1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hK₁] at hc1
    have hs := card_eq_mod hπ
    rw [card_natMod_fin, Fintype.card_fin, hK₁, ← pow_mul] at hs
    have hm : m * 3 = 6 * n := hS6 _ hs
    rcases hΛ with ⟨rfl, h⟩ | ⟨h2, h⟩
    · have hm2 : m = 2 := by omega
      subst hm2
      rw [h] at hc1
      norm_num at hc1
    · have hm2 : m = 2 * n := by omega
      have e : (2 : ℕ) ^ m = (2 ^ n) ^ 2 := by rw [hm2, ← pow_mul, mul_comm]
      rw [h, e] at hc1
      exact sl3_ne_g2 (four_le_two_pow h2) hc1.symm
  ·
    exfalso
    obtain ⟨⟨m, ⟨K₁, _, _, hK₁, π, hπ⟩, hmJ⟩, -⟩ := h3
    have hs := card_eq_mod hπ
    rw [card_natMod_fin, hK₁, ← pow_mul] at hs
    have hι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := rfl
    rw [hι] at hs
    have hm : m * 4 = 6 * n := hS6 _ hs
    have hm1 : 1 ≤ m := one_le_of_card hK₁
    have hJ : ffJ Γ = Λ := hmJ (by omega)
    have hc1 := card_eq_of_nat_realizes1527d hπ
    rw [hJ, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK₁] at hc1
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num)] at hc1
    rcases hΛ with ⟨rfl, -⟩ | ⟨h2, h⟩
    · omega
    · rw [h] at hc1
      have e4 : ((2 : ℕ) ^ m) ^ (2 ^ 2) = (2 ^ n) ^ 6 := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      rw [e4] at hc1
      have hpos : 0 < (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) := by
        have : 4 ≤ 2 ^ n := four_le_two_pow h2
        have : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left this 6
        have : 0 < (2 ^ n) ^ 6 - 1 := by omega
        positivity
      have e6 : ((2 : ℕ) ^ m) ^ (2 * 2) = (2 ^ n) ^ 6 := by
        rw [show 2 * 2 = 2 ^ 2 by norm_num, e4]
      rw [e6] at hc1
      have h' : (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * (((2 : ℕ) ^ m) ^ (2 * 1) - 1) =
          (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := by
        calc (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * (((2 : ℕ) ^ m) ^ (2 * 1) - 1) =
            (2 ^ n) ^ 6 * ((((2 : ℕ) ^ m) ^ (2 * 1) - 1) * ((2 ^ n) ^ 6 - 1)) := by ring
          _ = _ := hc1.symm
          _ = _ := by ring
      have h5 := Nat.eq_of_mul_eq_mul_left hpos h'
      have h6 : ((2 : ℕ) ^ m) ^ (2 * 1) = (2 ^ n) ^ 2 := by
        have : 1 ≤ ((2 : ℕ) ^ m) ^ (2 * 1) := Nat.one_le_pow _ _ (by positivity)
        have : 1 ≤ ((2 : ℕ) ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        omega
      rw [← pow_mul, ← pow_mul] at h6
      have := two_pow_inj h6
      omega
  ·
    obtain ⟨⟨m, ⟨K₁, _, _, hK₁, π, hπ⟩, hrk, -⟩, hq⟩ := h4
    have hK₁2 : CharP K₁ 2 := FFC.charP_two_of_card_pow hK₁
    have hs := card_eq_mod hπ
    rw [card_zornQMod, hK₁, ← pow_mul] at hs
    have hm : m * 6 = 6 * n := hS6 _ hs
    have hmn : m = n := by omega
    subst hmn
    refine ⟨hq, ?_, ⟨K₁, inferInstance, inferInstance, hK₁, π, hπ⟩⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hB.2.2.1.isPGroup.exists_card_eq
    have hrk' : rk ↥B = k := by
      rw [rk, hk]
      exact padicValNat.prime_pow k
    rw [hk, ← hrk', hrk]
  ·
    exfalso
    obtain ⟨-, hΓJ, -, -⟩ := hIdent S hS2 Γ Λ hHyp B hB (Or.inl h5)
    obtain ⟨⟨m, hm57, π, hπ, -⟩, -⟩ := h5
    have hm5 : 5 ≤ m := by rcases hm57 with rfl | rfl <;> norm_num
    have hJ := card_eq_gam (FFC.symDn_faithful hm5) hπ
    have hΛΓ : Λ ≤ Γ := hHyp.2.1 ▸ quasithinGenFitting_le Γ
    have h1 : Nat.card Λ ≤ Nat.card Γ := Subgroup.card_le_of_le hΛΓ
    rw [hΓJ, hJ] at h1
    change Nat.card Λ ≤ Nat.card (Equiv.Perm (Fin m)) at h1
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h1
    rcases hm57 with rfl | rfl <;> norm_num [Nat.factorial] at h1 <;> omega
  ·
    exfalso
    obtain ⟨-, ⟨π, hπ⟩, -⟩ := h6
    have h1 := card_eq_gam (FFC.altDn_faithful (by norm_num)) hπ
    change Nat.card Λ = Nat.card ↥(alternatingGroup (Fin 6)) at h1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    obtain ⟨-, -, -, hs, -⟩ := h7
    have := hS6 _ hs
    omega
  ·
    exfalso
    obtain ⟨-, -, -, ⟨K₁, _, _, Γ₀, -, -, hhat, -, π, hπ, -⟩⟩ := h8
    have h1 := card_eq_gam (FFModel.nat_faithful Γ₀) hπ
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
    change Nat.card Λ = Nat.card ↥Γ₀ at h1
    omega
  ·
    exfalso
    obtain ⟨-, m, hm45, ⟨K₁, _, _, hK₁, π, hπ⟩, -⟩ := h9
    have hs := card_eq_mod hπ
    rw [card_natMod_fin, Fintype.card_fin, hK₁, pow_one] at hs
    have := hS6 _ hs
    omega
  ·
    exfalso
    obtain ⟨⟨π, hπ⟩, -⟩ := h10
    have h1 := card_eq_gam (G64.extSq_faithful (by norm_num)) hπ
    change Nat.card Λ = Nat.card ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) at h1
    rw [card_statedSL_four_zmod1527d] at h1
    exact hΛ20160 h1
  ·
    exfalso
    obtain ⟨-, -, hs, -⟩ := h11
    have := hS6 _ hs
    omega

end CFSG.Quasithin.B5.G2D
