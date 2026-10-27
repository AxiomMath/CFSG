module

public import CFSG.Quasithin.Background.E6EighteenHeOut
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf

theorem factorization_two_card_he : (4030387200 : ℕ).factorization 2 = 10 := by
  rw [show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3935925 by norm_num), add_zero,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem mul_sq_sub_one_ne (p : ℕ) :
    p * (p ^ 2 - 1) ≠ 4030387200 ∧ p * (p ^ 2 - 1) ≠ 8060774400 := by
  have hmono : ∀ a b : ℕ, a ≤ b → a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) := fun a b h =>
    Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
  rcases le_or_gt p 1591 with h1 | h1
  · have h := hmono _ _ h1
    norm_num at h
    constructor <;> omega
  · rcases le_or_gt p 2005 with h2 | h2
    · have h1' := hmono _ _ h1
      have h2' := hmono _ _ h2
      norm_num at h1' h2'
      constructor <;> omega
    · have h := hmono _ _ h2
      norm_num at h
      constructor <;> omega

section He

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}

theorem card_quot_center_of_isHeQuot
    (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) = 4030387200 := by
  obtain ⟨φ⟩ := nonempty_qbar_mulEquiv_he hKq hHe
  rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.He.card_He]

theorem he_dvd_card_of_isHeQuot
    (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) : 4030387200 ∣ Nat.card ↥K := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K),
    card_quot_center_of_isHeQuot hKq hHe]
  exact Dvd.intro _ rfl

theorem card_of_isHeQuot_of_isSimpleGroup
    (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) (hs : IsSimpleGroup ↥K) :
    Nat.card ↥K = 4030387200 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K),
    card_quot_center_of_isHeQuot hKq hHe,
    Inn.center_eq_bot_of_isQuasisimple_of_simple hKq hs, Subgroup.card_bot, mul_one]

theorem card_center_ne_three_of_isHeQuot
    (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K) : Nat.card (Subgroup.center ↥K) ≠ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(Subgroup.center ↥K) := by
    rw [center_eq_pCore_of_isHeQuot hKq hHe]
    exact CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk]
  intro h
  rcases k with _ | _ | k
  · norm_num at h
  · norm_num at h
  · have : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
    rw [h] at this
    norm_num at this

end He

theorem not_e68Cases_of_isHeQuot
    {G : Type} [Group G] [Finite G] {T M V U K : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hKq : CFSG.IsQuasisimple ↥K) (hHe : IsHeQuot K)
    (hm : E3.mQuot V (V ⊓ Subgroup.centralizer (K : Set G)) ≤ 3) :
    ¬ (E68Case1 hV T M U K ∨ E68Case2 hV T M U K ∨ E68Case3 T M V U K ∨ E68Case4 M V U K ∨
      E68Case5 M V U K) := by
  have hQ := card_quot_center_of_isHeQuot hKq hHe
  have hdvd := he_dvd_card_of_isHeQuot hKq hHe
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have hle := Nat.le_of_dvd hpos hdvd
  have hfac : ∀ {X : Type} [Group X], Nat.card X = 4030387200 → ∀ {t : StatedLieTag} {r f : ℕ},
      StatedLieAdmissible t r 2 f → LieModel X t r 2 f → lieSylowExponent t r * f = 10 := by
    intro X _ hX t r f hadm hmod
    have h := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput X t r 2 f hadm
      hmod).2.2
    rw [hX, factorization_two_card_he] at h
    exact h.symm
  have hsimple : ∀ {t : StatedLieTag} {r p f : ℕ}, StatedClassicalModel ↥K t r p f →
      Nat.card ↥K = 4030387200 := fun h =>
    card_of_isHeQuot_of_isSimpleGroup hKq hHe
      (CFSG.LieType.Simplicity.fam_classical_converse _ ⟨_, _, _, _, h⟩).2.2
  rintro (h1 | h2 | h3 | h4 | h5)
  ·
    obtain ⟨n, hmod, -, -, -, -, hn, -, -⟩ := h1
    rw [hn] at hm
    rcases hmod with ⟨-, hL⟩ | ⟨hodd, hn3, hS⟩ | ⟨-, hL⟩ | ⟨-, hL⟩
    · have := hfac hQ hL.1 (Or.inl ⟨by decide, hL⟩)
      simp only [lieSylowExponent] at this
      omega
    · have hadm : StatedLieAdmissible .twistedB2 0 2 n :=
        ⟨Nat.prime_two, by omega, rfl, rfl, hodd, hn3⟩
      have := hfac hQ hadm (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hS⟩)))
      simp only [lieSylowExponent] at this
      omega
    · have := hfac hQ hL.1 (Or.inl ⟨by decide, hL⟩)
      simp only [lieSylowExponent] at this
      omega
    · have := hfac hQ hL.1 (Or.inl ⟨by decide, hL⟩)
      simp only [lieSylowExponent] at this
      omega
  ·
    obtain ⟨n, -, hmod, -⟩ := h2
    rcases hmod with ⟨-, hsp⟩ | ⟨-, ⟨e6⟩⟩
    · have := hfac (hsimple hsp) hsp.1 (Or.inl ⟨by decide, hsp⟩)
      simp only [lieSylowExponent] at this
      omega
    · have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin,
        ← Nat.card_congr e6.toEquiv] at h
      have h6 : Nat.factorial 6 = 720 := by decide
      omega
  ·
    obtain ⟨hl4, -⟩ := h3
    have := hfac (hsimple hl4) hl4.1 (Or.inl ⟨by decide, hl4⟩)
    simp only [lieSylowExponent] at this
    omega
  ·
    obtain ⟨hA | ⟨hz, -⟩ | ⟨hz, -⟩, -⟩ := h4
    · obtain ⟨e7⟩ := hA
      rw [Nat.card_congr e7.toEquiv, card_alternatingGroup_seven] at hle
      omega
    · exact card_center_ne_three_of_isHeQuot hKq hHe hz
    · exact card_center_ne_three_of_isHeQuot hKq hHe hz
  ·
    obtain ⟨hmod, -⟩ := h5
    rcases hmod with ⟨p, -, hp⟩ | h33 | ⟨e11⟩
    · have h := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput ↥K .PSL 2 p 1
        hp.1 (Or.inl ⟨by decide, hp⟩)).2.1
      rw [hsimple hp] at h
      simp only [lieOrderDivisor, lieOrderNumerator, pow_one] at h
      norm_num at h
      have hg : Nat.gcd 2 (p - 1) = 1 ∨ Nat.gcd 2 (p - 1) = 2 :=
        (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_left 2 (p - 1))
      obtain ⟨hne1, hne2⟩ := mul_sq_sub_one_ne p
      rcases hg with hg | hg <;> rw [hg] at h <;> omega
    · have h := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput ↥K .PSL 3 3 1
        h33.1 (Or.inl ⟨by decide, h33⟩)).2.1
      simp only [lieOrderDivisor, lieOrderNumerator, pow_one] at h
      norm_num at h
      rw [show (27 * ∏ x ∈ Finset.Icc 2 3, (3 ^ x - 1) : ℕ) = 5616 by decide] at h
      omega
    · obtain ⟨e⟩ := e11
      have hc : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
      rw [Nat.card_congr e.toEquiv, hc] at hle
      omega

end E6

end CFSG.Quasithin
