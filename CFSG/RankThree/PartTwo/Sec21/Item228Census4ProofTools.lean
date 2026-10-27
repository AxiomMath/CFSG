module

public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item228Census4Proof

theorem exists_two_involutions {Q : Type} [Group Q] {m : ℕ} (hm : 2 ≤ m)
    (e : Q ≃* projSL 2 (GaloisField 2 m)) :
    ∃ t₁ t₂ : Q, t₁ ^ 2 = 1 ∧ t₂ ^ 2 = 1 ∧ t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₁ ≠ t₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, hE, hE4⟩ := Commute33Steps.exists_fourGroup_of_mulEquiv_projSL
    (X := (⊤ : Subgroup Q)) hm (Subgroup.topEquiv.trans e)
  have hne : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE4
    omega
  have : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_congr e.toEquiv, card_projSL_two m (by omega)]
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h16 : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
    exact Nat.mul_ne_zero (by omega) (by omega)
  obtain ⟨⟨a, haE⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from h)
    rw [hE4, Nat.card_zpowers, orderOf_eq_prime (hE.2 a haE) ha1] at hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hba' : b ≠ a := fun h => hba (h ▸ Subgroup.mem_zpowers a)
  exact ⟨a, b, hE.2 a haE, hE.2 b hbE, ha1, hb1, hba'.symm⟩

theorem isSimpleGroup_of_mulEquiv {Q : Type*} [Group Q] {m : ℕ} (hm : 2 ≤ m)
    (e : Q ≃* projSL 2 (GaloisField 2 m)) : IsSimpleGroup Q := by
  have := isSimpleGroup_projSL_two hm
  exact e.isSimpleGroup

theorem two_le_of_even {m : ℕ} (hm : 0 < m) (he : Even m) : 2 ≤ m := by
  obtain ⟨r, hr⟩ := he
  omega

theorem exists_cube_root_of_unity {F : Type*} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ τ : F, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [Nat.card_units]; exact h3)
  refine ⟨u, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    norm_num at hu

theorem exists_piField_true (F : Type) [Field F] [Finite F] :
    ∃ p f : ℕ, Sec4.PiField true p f F := by
  have := Fintype.ofFinite F
  have := ringChar.charP F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, ⟨hp, n.pos, by
    rw [Sec4.piCard, Bool.cond_true, Nat.card_eq_fintype_card, hn]⟩⟩

theorem two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  have := Fintype.ofFinite F
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by exact_mod_cast h2)
  have hc : ringChar F = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · exact h1
  have hev := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card] at hev
  obtain ⟨k, hk⟩ := h
  omega

theorem charP_two_of_even_card {F : Type*} [Field F] [Finite F] (h : Even (Nat.card F)) :
    CharP F 2 := by
  have := Fintype.ofFinite F
  refine ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr ?_)
  rw [← Nat.card_eq_fintype_card]
  exact Nat.even_iff.mp h

variable {G : Type} [Group G] [Finite G]

theorem thetaQuotMulAut_pow_three {X : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (X : Set G)) (hb3 : b ^ 3 = 1) :
    Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) ^ 3 = 1 := by
  have h : (⟨b, hbN⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  rw [← map_pow, ← map_pow, h, map_one, map_one]

theorem mem_range_conj_of_not_inducesOuterTheta {X : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (X : Set G)) (h : ¬ Sec4.InducesOuterTheta b X) :
    Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) ∈
      (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
        MulAut (X ⧸ aschbacherSolvableCore 3 X)).range := by
  by_contra h'
  exact h ⟨hbN, h'⟩

end Item228Census4Proof

end CFSG.RankThree.PartTwo.Sec21
