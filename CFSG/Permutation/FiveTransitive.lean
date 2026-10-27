module

public import CFSG.Permutation.FiveTransitive.Reduction
public import CFSG.Permutation.FiveTransitive.LowDegreeClassification
public import CFSG.Permutation.FiveTransitive.SmallDegreeClassification
public import CFSG.Permutation.FiveTransitive.Degree28Classification
public import CFSG.Permutation.FiveTransitive.Degree29Classification
public import CFSG.Permutation.FiveTransitive.Degree31Classification
public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleClassification
public import CFSG.Permutation.FiveTransitive.PrimePredFour
public import CFSG.Permutation.FiveTransitive.ThreePrimeFourClassification
public import CFSG.Permutation.FiveTransitive.Degree36Classification
public import CFSG.Permutation.FiveTransitive.Degree39Classification
public import CFSG.Permutation.FiveTransitive.Degree43Classification
public import CFSG.Permutation.FiveTransitive.Degree48Classification
public import CFSG.Permutation.FiveTransitive.Degree52Classification
public import CFSG.Permutation.FiveTransitive.Degree53Classification
public import CFSG.Permutation.FiveTransitive.Degree54Classification
public import CFSG.Permutation.FiveTransitive.Degree58Classification
public import CFSG.Permutation.FiveTransitive.Degree59Classification
public import CFSG.Permutation.FiveTransitive.Degree60Classification
public import CFSG.Permutation.FiveTransitive.Degree67Classification
public import CFSG.Permutation.FiveTransitive.Degree68Classification
public import CFSG.Permutation.FiveTransitive.Degree69Classification
public import CFSG.Permutation.FiveTransitive.Degree72Classification
public import CFSG.Permutation.FiveTransitive.Degree79Classification
public import CFSG.Permutation.FiveTransitive.Degree80Classification

public section

namespace CFSG

namespace FiveTransitive

theorem subgroup_card_classification_of_card_le_eighty :
    ∀ n : ℕ, ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (P : Subgroup (Equiv.Perm Y)),
      Fintype.card Y = n → 5 ≤ n → n ≤ 80 → MulAction.IsMultiplyPretransitive P Y 5 →
      Nat.card P = n.factorial ∨
        (7 ≤ n ∧ Nat.card P = n.factorial / 2) ∨
        (n = 12 ∧ Nat.card P = 95040) ∨
        (n = 24 ∧ Nat.card P = 244823040) := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih Y _ _ P hY hdegree hle h5P
  let _ : Fintype P := Fintype.ofFinite P
  have hfive : 5 ≤ Fintype.card Y := by omega
  have h5explicit : ∀ a b : Fin 5 → Y,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp h5P) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨g, fun i => DFunLike.congr_fun hg i⟩
  by_cases hlow : Fintype.card Y ≤ 13
  · have h := LowDegreeClassification.classification_of_five_transitive_of_card_le_thirteen
      P Y hfive hlow h5explicit
    simpa only [Nat.card_eq_fintype_card, hY] using h
  have hlarge : 14 ≤ Fintype.card Y := by omega
  by_cases hmid : Fintype.card Y ≤ 27
  · have h := SmallDegreeClassification.subgroup_card_classification Y P hfive hmid h5P
    simpa only [hY] using h
  by_cases hdegree28 : Fintype.card Y = 28
  · rcases Degree28Classification.subgroup_card_classification P hdegree28 h5P with h | h
    · exact Or.inl (by simpa only [hY] using h)
    · exact Or.inr (Or.inl (by simpa only [hY] using h))
  by_cases hdegree29 : Fintype.card Y = 29
  · rcases Degree29Classification.subgroup_card_classification P hdegree29 h5P with h | h
    · exact Or.inl (by simpa only [hY] using h)
    · exact Or.inr (Or.inl (by simpa only [hY] using h))
  by_cases hdegree31 : Fintype.card Y = 31
  · rcases Degree31Classification.subgroup_card_classification P hdegree31 h5P with h | h
    · exact Or.inl (by simpa only [hY] using h)
    · exact Or.inr (Or.inl (by simpa only [hY] using h))
  by_cases htwoPrime : ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧
      (Fintype.card Y = 2 * p + 3 ∨ Fintype.card Y = 2 * p + 4)
  · obtain ⟨p,hp,hp13,hdeg⟩ := htwoPrime
    have hclass : Nat.card P = (Fintype.card Y).factorial ∨
        (7 ≤ Fintype.card Y ∧ Nat.card P = (Fintype.card Y).factorial / 2) := by
      rcases hdeg with h | h
      · exact TwoPrimeCycleClassification.subgroup_card_classification p 3 hp hp13
          (Or.inl rfl) P h h5P
      · exact TwoPrimeCycleClassification.subgroup_card_classification p 4 hp hp13
          (Or.inr rfl) P h h5P
    rcases hclass with h | h
    · exact Or.inl (by simpa only [hY] using h)
    · exact Or.inr (Or.inl (by simpa only [hY] using h))
  have h30 : 30 ≤ Fintype.card Y := by omega
  have h31 : 31 ≤ Fintype.card Y := by
    by_contra hn
    exact htwoPrime ⟨13,by norm_num,by norm_num,Or.inr (by omega)⟩
  have h29 : 29 ≤ Fintype.card Y := by omega
  have h28 : 28 ≤ Fintype.card Y := by omega
  by_cases hAlt : alternatingGroup Y ≤ P
  · rcases alt_le_perm_card_dichotomy Y P (by omega) hAlt with hSym | hHalf
    · exact Or.inl (by simpa only [hY] using hSym)
    · exact Or.inr (Or.inl ⟨by omega, by simpa only [hY] using hHalf⟩)
  by_cases hp3 : (Fintype.card Y - 3).Prime
  · exact False.elim (hAlt (PrimePredFour.alternatingGroup_le_of_sub_three_prime
      Y P (by omega) h5P hp3))
  by_cases hp4 : (Fintype.card Y - 4).Prime
  · exact False.elim (hAlt (PrimePredFour.alternatingGroup_le_of_sub_four_prime
      Y P (by omega) h5P hp4))
  have h36 : 36 ≤ Fintype.card Y := by
    have h32 : 32 ≤ Fintype.card Y := by omega
    by_contra hn
    have hu : Fintype.card Y ≤ 35 := by omega
    have hc : Fintype.card Y = 32 ∨ Fintype.card Y = 33 ∨
        Fintype.card Y = 34 ∨ Fintype.card Y = 35 := by omega
    rcases hc with hc | hc | hc | hc
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  by_cases hdegree36 : Fintype.card Y = 36
  · exact False.elim (hAlt (Degree36Classification.alternatingGroup_le P hdegree36 h5P))
  have h39 : 39 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 37 ∨ Fintype.card Y = 38 := by omega
    exact htwoPrime ⟨17,by norm_num,by norm_num,hc⟩
  by_cases hdegree39 : Fintype.card Y = 39
  · exact False.elim (hAlt (Degree39Classification.alternatingGroup_le P hdegree39 h5P))
  have h42 : 42 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 40 ∨ Fintype.card Y = 41 := by omega
    rcases hc with hc | hc
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  have h43 : 43 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 42 := by omega
    exact htwoPrime ⟨19,by norm_num,by norm_num,Or.inr (by omega)⟩
  by_cases hdegree43 : Fintype.card Y = 43
  · exact False.elim (hAlt (Degree43Classification.alternatingGroup_le P hdegree43 h5P))
  have h48 : 48 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 44 ∨ Fintype.card Y = 45 ∨
        Fintype.card Y = 46 ∨ Fintype.card Y = 47 := by omega
    rcases hc with hc | hc | hc | hc
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  by_cases hdegree48 : Fintype.card Y = 48
  · exact False.elim (hAlt (Degree48Classification.alternatingGroup_le P hdegree48 h5P))
  have h52 : 52 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 49 ∨ Fintype.card Y = 50 ∨ Fintype.card Y = 51 := by omega
    rcases hc with hc | hc | hc
    · exact htwoPrime ⟨23,by norm_num,by norm_num,Or.inl (by omega)⟩
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  by_cases hdegree52 : Fintype.card Y = 52
  · exact False.elim (hAlt (Degree52Classification.alternatingGroup_le P hdegree52 h5P))
  by_cases hdegree53 : Fintype.card Y = 53
  · exact False.elim (hAlt (Degree53Classification.alternatingGroup_le P hdegree53 h5P))
  by_cases hdegree54 : Fintype.card Y = 54
  · exact False.elim (hAlt (Degree54Classification.alternatingGroup_le P hdegree54 h5P))
  have h55 : 55 ≤ Fintype.card Y := by omega
  by_cases hthreePrime : ∃ p : ℕ, p.Prime ∧ 17 ≤ p ∧ Fintype.card Y = 3 * p + 4
  · obtain ⟨p,hp,hp17,hdeg⟩ := hthreePrime
    apply False.elim
    apply hAlt
    apply ThreePrimeFourClassification.alternatingGroup_le hp hp17 P hdeg h5P
    intro F _ _ J hF hlt hJ
    exact ih (Fintype.card F) (by omega) F J rfl hF (by omega) hJ
  have h58 : 58 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 55 ∨ Fintype.card Y = 56 ∨ Fintype.card Y = 57 := by omega
    rcases hc with hc | hc | hc
    · exact hthreePrime ⟨17,by norm_num,by norm_num,by omega⟩
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  by_cases hdegree58 : Fintype.card Y = 58
  · exact False.elim (hAlt (Degree58Classification.alternatingGroup_le P hdegree58 h5P))
  have h59 : 59 ≤ Fintype.card Y := by omega
  by_cases hdegree59 : Fintype.card Y = 59
  · exact False.elim (hAlt (Degree59Classification.alternatingGroup_le P hdegree59 h5P))
  have h60 : 60 ≤ Fintype.card Y := by omega
  by_cases hdegree60 : Fintype.card Y = 60
  · exact False.elim (hAlt (Degree60Classification.alternatingGroup_le P hdegree60 h5P))
  have h67 : 67 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 61 ∨ Fintype.card Y = 62 ∨ Fintype.card Y = 63 ∨
        Fintype.card Y = 64 ∨ Fintype.card Y = 65 ∨ Fintype.card Y = 66 := by omega
    rcases hc with hc | hc | hc | hc | hc | hc
    · exact hthreePrime ⟨19,by norm_num,by norm_num,by omega⟩
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact htwoPrime ⟨31,by norm_num,by norm_num,Or.inr (by omega)⟩
  by_cases hdegree67 : Fintype.card Y = 67
  · exact False.elim (hAlt (Degree67Classification.alternatingGroup_le P hdegree67 h5P))
  have h68 : 68 ≤ Fintype.card Y := by omega
  by_cases hdegree68 : Fintype.card Y = 68
  · exact False.elim (hAlt (Degree68Classification.alternatingGroup_le P hdegree68 h5P))
  have h69 : 69 ≤ Fintype.card Y := by omega
  by_cases hdegree69 : Fintype.card Y = 69
  · exact False.elim (hAlt (Degree69Classification.alternatingGroup_le P hdegree69 h5P))
  have h72 : 72 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 70 ∨ Fintype.card Y = 71 := by omega
    rcases hc with hc | hc
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
  by_cases hdegree72 : Fintype.card Y = 72
  · exact False.elim (hAlt (Degree72Classification.alternatingGroup_le P hdegree72 h5P))
  have h79 : 79 ≤ Fintype.card Y := by
    by_contra hn
    have hc : Fintype.card Y = 73 ∨ Fintype.card Y = 74 ∨ Fintype.card Y = 75 ∨
        Fintype.card Y = 76 ∨ Fintype.card Y = 77 ∨ Fintype.card Y = 78 := by omega
    rcases hc with hc | hc | hc | hc | hc | hc
    · exact hthreePrime ⟨23,by norm_num,by norm_num,by omega⟩
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact hp3 (by rw [hc]; norm_num)
    · exact hp4 (by rw [hc]; norm_num)
    · exact htwoPrime ⟨37,by norm_num,by norm_num,Or.inr (by omega)⟩
  by_cases hdegree79 : Fintype.card Y = 79
  · exact False.elim (hAlt (Degree79Classification.alternatingGroup_le P hdegree79 h5P))
  have h80 : 80 ≤ Fintype.card Y := by omega
  by_cases hdegree80 : Fintype.card Y = 80
  · exact False.elim (hAlt (Degree80Classification.alternatingGroup_le P hdegree80 h5P))
  exfalso
  omega

theorem subgroup_card_classification_of_prime_offset
    (Y : Type) [Fintype Y] [DecidableEq Y] (P : Subgroup (Equiv.Perm Y))
    (hdegree : 9 ≤ Fintype.card Y)
    (hprime : (Fintype.card Y - 3).Prime ∨ (Fintype.card Y - 4).Prime ∨
      ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧
        (Fintype.card Y = 2 * p + 3 ∨ Fintype.card Y = 2 * p + 4))
    (h5P : MulAction.IsMultiplyPretransitive P Y 5) :
    Nat.card P = (Fintype.card Y).factorial ∨
      Nat.card P = (Fintype.card Y).factorial / 2 := by
  refine alt_le_perm_card_dichotomy Y P (by omega) ?_
  rcases hprime with hp3 | hp4 | ⟨p, hp, hp13, hdeg⟩
  · exact PrimePredFour.alternatingGroup_le_of_sub_three_prime Y P (by omega) h5P hp3
  · exact PrimePredFour.alternatingGroup_le_of_sub_four_prime Y P hdegree h5P hp4
  · rcases hdeg with hdeg | hdeg
    · exact TwoPrimeCycleClassification.alternatingGroup_le p 3 hp hp13 (Or.inl rfl) P hdeg h5P
    · exact TwoPrimeCycleClassification.alternatingGroup_le p 4 hp hp13 (Or.inr rfl) P hdeg h5P

theorem five_transitive_card_classification_of_card_le_eighty (G X : Type) [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X) (hle : Fintype.card X ≤ 80)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    let n := Fintype.card X
    Fintype.card G = n.factorial ∨
    (7 ≤ n ∧ Fintype.card G = n.factorial / 2) ∨
    (n = 12 ∧ Fintype.card G = 95040) ∨
    (n = 24 ∧ Fintype.card G = 244823040) := by
  classical
  let P := (MulAction.toPermHom G X).range
  have h5P := isMultiplyPretransitive_range_toPermHom G X 5
    (isMultiplyPretransitive_of_explicit G X 5 h5)
  have h := subgroup_card_classification_of_card_le_eighty (Fintype.card X) X P rfl hcard hle h5P
  have hcardP : Nat.card P = Fintype.card G := card_range_toPermHom G X
  simpa only [hcardP] using h

theorem five_transitive_card_classification_of_degree (G X : Type) [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (hdeg : Fintype.card X ≤ 80 ∨ (Fintype.card X - 3).Prime ∨ (Fintype.card X - 4).Prime ∨
      ∃ p : ℕ, p.Prime ∧ (Fintype.card X = 2 * p + 3 ∨ Fintype.card X = 2 * p + 4))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    let n := Fintype.card X
    Fintype.card G = n.factorial ∨
    (7 ≤ n ∧ Fintype.card G = n.factorial / 2) ∨
    (n = 12 ∧ Fintype.card G = 95040) ∨
    (n = 24 ∧ Fintype.card G = 244823040) := by
  classical
  by_cases hle : Fintype.card X ≤ 80
  · exact five_transitive_card_classification_of_card_le_eighty G X hcard hle h5
  let P := (MulAction.toPermHom G X).range
  have h5P := isMultiplyPretransitive_range_toPermHom G X 5
    (isMultiplyPretransitive_of_explicit G X 5 h5)
  have hcardP : Nat.card P = Fintype.card G := card_range_toPermHom G X
  have hprime : (Fintype.card X - 3).Prime ∨ (Fintype.card X - 4).Prime ∨
      ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧
        (Fintype.card X = 2 * p + 3 ∨ Fintype.card X = 2 * p + 4) := by
    rcases hdeg with hdeg | hdeg | hdeg | ⟨p, hp, hdeg⟩
    · exact absurd hdeg hle
    · exact Or.inl hdeg
    · exact Or.inr (Or.inl hdeg)
    · exact Or.inr (Or.inr ⟨p, hp, by rcases hdeg with h | h <;> omega, hdeg⟩)
  dsimp only
  rcases subgroup_card_classification_of_prime_offset X P (by omega) hprime h5P with h | h
  · exact Or.inl (by simpa only [hcardP] using h)
  · exact Or.inr (Or.inl ⟨by omega, by simpa only [hcardP] using h⟩)

end FiveTransitive

end CFSG
