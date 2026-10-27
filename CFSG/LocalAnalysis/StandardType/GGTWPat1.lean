module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWPatAbs
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggTW_cast_cartan_pair {p : ℕ} (hp : 3 ≤ p) {a a' b : ℤ}
    (hpair : (a = 0 ∧ a' = 0) ∨ (a = -1 ∧ a' = -1) ∨
      (a * a' = 2 ∧ a < 0 ∧ a' < 0) ∨ (a * a' = 3 ∧ a < 0 ∧ a' < 0))
    (hb : b = 0 ∨ b = -1)
    (h1 : (a : ZMod p) = (b : ZMod p)) (h2 : (a' : ZMod p) = (b : ZMod p)) :
    a = b ∧ a' = b := by
  have hamem : a = 0 ∨ a = -1 ∨ a = -2 ∨ a = -3 := by
    rcases hpair with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨h, ha, ha'⟩ | ⟨h, ha, ha'⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) ha ha' h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · rcases l05nDP4_neg_pair_of_mul (Or.inr rfl) ha ha' h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inr h1))
  have ha'mem : a' = 0 ∨ a' = -1 ∨ a' = -2 ∨ a' = -3 := by
    rcases hpair with ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨h, ha, ha'⟩ | ⟨h, ha, ha'⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) ha ha' h with ⟨_, hr⟩ | ⟨_, hr⟩
      · exact Or.inr (Or.inr (Or.inl hr))
      · exact Or.inr (Or.inl hr)
    · rcases l05nDP4_neg_pair_of_mul (Or.inr rfl) ha ha' h with ⟨_, hr⟩ | ⟨_, hr⟩
      · exact Or.inr (Or.inr (Or.inr hr))
      · exact Or.inr (Or.inl hr)
  constructor
  · by_contra hne
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have hne' : b - a ≠ 0 := by omega
    have hp_le : (p : ℤ) ≤ |b - a| := Int.le_abs_of_dvd hne' h1
    have hbound : |b - a| ≤ 3 := by
      rcases hamem with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num
    have hp3 : (p : ℤ) = 3 := by omega
    have habs : |b - a| = 3 := by omega
    have h30 : a = -3 ∧ b = 0 := by
      rcases hamem with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at habs
      exact ⟨rfl, rfl⟩
    have ha3 : a = -3 := h30.1
    have hb0 : b = 0 := h30.2
    have hprod : a * a' = 3 := by
      rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
      · omega
      · omega
      · nlinarith
      · exact h
    have ha'1 : a' = -1 := by nlinarith
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    have hp1 : (p : ℤ) ∣ 1 := by
      have : b - a' = 1 := by omega
      rwa [this] at h2
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hp1
    omega
  · by_contra hne
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    have hne' : b - a' ≠ 0 := by omega
    have hp_le : (p : ℤ) ≤ |b - a'| := Int.le_abs_of_dvd hne' h2
    have hbound : |b - a'| ≤ 3 := by
      rcases ha'mem with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num
    have hp3 : (p : ℤ) = 3 := by omega
    have habs : |b - a'| = 3 := by omega
    have h30 : a' = -3 ∧ b = 0 := by
      rcases ha'mem with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at habs
      exact ⟨rfl, rfl⟩
    have ha'3 : a' = -3 := h30.1
    have hb0 : b = 0 := h30.2
    have hprod : a' * a = 3 := by
      rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
      · omega
      · omega
      · nlinarith
      · nlinarith
    have ha1 : a = -1 := by nlinarith
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have hp1 : (p : ℤ) ∣ 1 := by
      have : b - a = 1 := by omega
      rwa [this] at h1
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hp1
    omega

private theorem l05nT1_transport {p N : ℕ} (hp : 3 ≤ p)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10)
    (pos : GGTWPos) {φ : Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N pos c.val}}
    (hcart : ∀ k l : Fin (N - 3),
      CartanMatrix.A (N - 1) (φ k).1 (φ l).1 = CartanMatrix.A (N - 3) k l)
    (hplace : ∀ k : Fin (N - 3), ggTWPlace pos (φ k).1.val = k.val)
    {MK : CoxeterMatrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})}
    {CK : Matrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})
      (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      (CK (some i) (some j) : ZMod p) = (CartanMatrix.A (N - 1) i.1 j.1 : ZMod p)) :
    ∃ (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n ∧
      ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK none (some i) = (if i.1 = c0 then m else 0) ∧
          CK (some i) none = (if i.1 = c0 then n else 0) := by
  have hL : 2 ≤ N - 3 := by rcases hN with h | h | h | h | h <;> omega
  have hr : N - 3 = 2 ∨ N - 3 = 3 ∨ N - 3 = 4 ∨ N - 3 = 6 ∨ N - 3 = 7 := by
    rcases hN with h | h | h | h | h <;> omega
  let σ : Option (Fin (N - 3)) ≃ Option {c : Fin (N - 1) // ggTWInJ N pos c.val} :=
    Equiv.optionCongr φ
  let M₀ : CoxeterMatrix (Option (Fin (N - 3))) := MK.reindex σ.symm
  let C₀ : Matrix (Option (Fin (N - 3))) (Option (Fin (N - 3))) ℤ :=
    Matrix.reindex σ.symm σ.symm CK
  have hM₀ : GGIsWeylMatrix M₀ := l05nDP4_weyl_reindex hWK σ.symm
  have hC₀ : GGIntCartan M₀ C₀ := by
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · simp only [C₀, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hCK.1 (σ u)
    · have h := hCK.2 (σ u) (σ v) (fun hh => huv (σ.injective hh))
      simpa [M₀, C₀, CoxeterMatrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        using h
  have hJ₀ : ∀ i j : Fin (N - 3), C₀ (some i) (some j) = CartanMatrix.A (N - 3) i j := by
    intro i j
    change CK (some (φ i)) (some (φ j)) = CartanMatrix.A (N - 3) i j
    by_cases hij : i = j
    · subst hij
      rw [hCK.1 (some (φ i))]
      simp [CartanMatrix.A]
    · have hne : (some (φ i) : Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) ≠
          some (φ j) := by simp [hij]
      have hpair : (CK (some (φ i)) (some (φ j)) = 0 ∧ CK (some (φ j)) (some (φ i)) = 0) ∨
          (CK (some (φ i)) (some (φ j)) = -1 ∧ CK (some (φ j)) (some (φ i)) = -1) ∨
          (CK (some (φ i)) (some (φ j)) * CK (some (φ j)) (some (φ i)) = 2 ∧
            CK (some (φ i)) (some (φ j)) < 0 ∧ CK (some (φ j)) (some (φ i)) < 0) ∨
          (CK (some (φ i)) (some (φ j)) * CK (some (φ j)) (some (φ i)) = 3 ∧
            CK (some (φ i)) (some (φ j)) < 0 ∧ CK (some (φ j)) (some (φ i)) < 0) := by
        rcases hCK.2 (some (φ i)) (some (φ j)) hne with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ |
          ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      have hb : CartanMatrix.A (N - 3) i j = 0 ∨ CartanMatrix.A (N - 3) i j = -1 := by
        rcases l05nDP4_cartanA_mem (N - 3) i j with h | h | h
        · exact absurd (l05nDP4_cartanA_eq_two h) hij
        · exact Or.inr h
        · exact Or.inl h
      have h1 : (CK (some (φ i)) (some (φ j)) : ZMod p) =
          (CartanMatrix.A (N - 3) i j : ZMod p) := by
        rw [hJ (φ i) (φ j), hcart i j]
      have h2 : (CK (some (φ j)) (some (φ i)) : ZMod p) =
          (CartanMatrix.A (N - 3) i j : ZMod p) := by
        rw [hJ (φ j) (φ i), hcart j i, CFSG.ClassicalInvolution.ModelFacts.cartanA_symm (N - 3) j i]
      exact (ggTW_cast_cartan_pair hp hpair hb h1 h2).1
  obtain ⟨k, m, n, hpat, hrow⟩ := ggTW_pattern_abs (L := N - 3) hL hr hM₀ hC₀ hJ₀
  have hiff : ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val}, φ.symm i = k ↔ i = φ k := by
    intro i
    rw [Equiv.symm_apply_eq]
  have hC0 : ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      C₀ none (some (φ.symm i)) = CK none (some i) := by
    intro i
    show CK (σ none) (σ (some (φ.symm i))) = CK none (some i)
    simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
      Equiv.apply_symm_apply]
  have hC0' : ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      C₀ (some (φ.symm i)) none = CK (some i) none := by
    intro i
    show CK (σ (some (φ.symm i))) (σ none) = CK (some i) none
    simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
      Equiv.apply_symm_apply]
  have hrow' : ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK none (some i) = (if i.1 = (φ k).1 then m else 0) ∧
        CK (some i) none = (if i.1 = (φ k).1 then n else 0) := by
    intro i
    have hrowi := hrow (φ.symm i)
    rw [hC0 i, hC0' i] at hrowi
    rcases hrowi with ⟨hr1, hr2⟩
    refine ⟨?_, ?_⟩
    · by_cases hik : i.1 = (φ k).1
      · have h2 : φ.symm i = k := (hiff i).mpr (Subtype.ext hik)
        rw [if_pos h2] at hr1
        rw [if_pos hik]
        exact hr1
      · have h2 : φ.symm i ≠ k := fun hh => hik (congrArg Subtype.val ((hiff i).mp hh))
        rw [if_neg h2] at hr1
        rw [if_neg hik]
        exact hr1
    · by_cases hik : i.1 = (φ k).1
      · have h2 : φ.symm i = k := (hiff i).mpr (Subtype.ext hik)
        rw [if_pos h2] at hr2
        rw [if_pos hik]
        exact hr2
      · have h2 : φ.symm i ≠ k := fun hh => hik (congrArg Subtype.val ((hiff i).mp hh))
        rw [if_neg h2] at hr2
        rw [if_neg hik]
        exact hr2
  refine ⟨(φ k).1, m, n, ?_, hrow'⟩
  unfold GGTWPat1
  refine ⟨(φ k).2, ?_⟩
  rw [hplace k]
  exact hpat

theorem ggTW_pattern1_rows {p N : ℕ} (hp : 3 ≤ p)
    (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (pos : GGTWPos)
    {MK : CoxeterMatrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})}
    {CK : Matrix (Option {c : Fin (N - 1) // ggTWInJ N pos c.val})
      (Option {c : Fin (N - 1) // ggTWInJ N pos c.val}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      (CK (some i) (some j) : ZMod p) = (CartanMatrix.A (N - 1) i.1 j.1 : ZMod p)) :
    ∃ (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n ∧
      ∀ i : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK none (some i) = (if i.1 = c0 then m else 0) ∧
          CK (some i) none = (if i.1 = c0 then n else 0) := by
  cases pos with
  | ends =>
    let toJ : Fin (N - 3) → {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} := fun k =>
      ⟨⟨k.val + 1, by omega⟩, by
        change 1 ≤ k.val + 1 ∧ k.val + 1 + 3 ≤ N
        omega⟩
    let posFun : {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} → Fin (N - 3) := fun i =>
      ⟨i.1.val - 1, by
        have h := i.2
        change 1 ≤ i.1.val ∧ i.1.val + 3 ≤ N at h
        change i.1.val - 1 < N - 3
        omega⟩
    have hleft : ∀ k, posFun (toJ k) = k := by
      intro k
      apply Fin.ext
      change (k.val + 1) - 1 = k.val
      omega
    have hright : ∀ i, toJ (posFun i) = i := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      change (i.1.val - 1) + 1 = i.1.val
      have h := i.2
      change 1 ≤ i.1.val ∧ i.1.val + 3 ≤ N at h
      omega
    let φ : Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} :=
      { toFun := toJ, invFun := posFun, left_inv := hleft, right_inv := hright }
    have hcart : ∀ k l : Fin (N - 3),
        CartanMatrix.A (N - 1) (φ k).1 (φ l).1 = CartanMatrix.A (N - 3) k l := by
      intro k l
      change CartanMatrix.A (N - 1) (⟨k.val + 1, by omega⟩ : Fin (N - 1))
        (⟨l.val + 1, by omega⟩ : Fin (N - 1)) = CartanMatrix.A (N - 3) k l
      simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
      try (split_ifs <;> omega)
    have hplace : ∀ k : Fin (N - 3), ggTWPlace GGTWPos.ends (φ k).1.val = k.val := by
      intro k
      change (k.val + 1) - 1 = k.val
      omega
    exact l05nT1_transport hp hN GGTWPos.ends (φ := φ) hcart hplace hWK hCK hJ
  | adj =>
    let toJ : Fin (N - 3) → {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} := fun k =>
      ⟨⟨k.val, by omega⟩, by
        change k.val + 4 ≤ N
        omega⟩
    let posFun : {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} → Fin (N - 3) := fun i =>
      ⟨i.1.val, by
        have h := i.2
        change i.1.val + 4 ≤ N at h
        change i.1.val < N - 3
        omega⟩
    have hleft : ∀ k, posFun (toJ k) = k := by
      intro k
      apply Fin.ext
      rfl
    have hright : ∀ i, toJ (posFun i) = i := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      rfl
    let φ : Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} :=
      { toFun := toJ, invFun := posFun, left_inv := hleft, right_inv := hright }
    have hcart : ∀ k l : Fin (N - 3),
        CartanMatrix.A (N - 1) (φ k).1 (φ l).1 = CartanMatrix.A (N - 3) k l := by
      intro k l
      change CartanMatrix.A (N - 1) (⟨k.val, by omega⟩ : Fin (N - 1))
        (⟨l.val, by omega⟩ : Fin (N - 1)) = CartanMatrix.A (N - 3) k l
      simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
      try (split_ifs <;> omega)
    have hplace : ∀ k : Fin (N - 3), ggTWPlace GGTWPos.adj (φ k).1.val = k.val := by
      intro k
      change k.val = k.val
      rfl
    exact l05nT1_transport hp hN GGTWPos.adj (φ := φ) hcart hplace hWK hCK hJ

end CFSG.StandardType
