module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45InspShape
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45InspMat
public import CFSG.LocalAnalysis.UniquenessCase.UCInspBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS

open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem bad_pair_large_char {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hp7 : 7 ≤ p) : ∃ D₀ D₁ : Subgroup PSL(2, K), Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧
      ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_unip (K := K) (p := p) (by omega)
  have hpodd : Odd p := hp.out.odd_of_ne_two (by omega)
  refine bad_pair_of_prod hx hy (hxy ▸ hpodd) ?_ ?_ ?_ ?_ <;> rw [hxy]
  · omega
  · omega
  · omega
  · intro h9
    have := hp.out
    rw [h9] at this
    exact absurd this (by decide)

theorem bad_pair_char_two {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 3 ≤ f) : ∃ D₀ D₁ : Subgroup PSL(2, K), Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧
      ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  have h8 : 8 ∣ 2 ^ f := by
    have : 2 ^ 3 ∣ 2 ^ f := pow_dvd_pow 2 hf
    simpa using this
  have hpos : 0 < 2 ^ f := by positivity
  have hl' : orderOf l = 2 ^ f - 1 := hl.trans hcard
  have hodd : Odd (orderOf l) := by
    obtain ⟨m, hm⟩ := h8
    exact ⟨4 * m - 1, by omega⟩
  have hne : l ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hl'
    omega
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_torus l hodd hne
  refine bad_pair_of_prod hx hy (hxy ▸ hodd) ?_ ?_ ?_ ?_ <;> rw [hxy, hl'] <;> omega

theorem bad_pair_five_odd {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 5 ^ f)
    (hodd : Odd f) (hf : 3 ≤ f) : ∃ D₀ D₁ : Subgroup PSL(2, K), Nat.card D₀ = 3 ∧
      Nat.card D₁ = 3 ∧ ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = 5 ^ f - 1 := by rw [Nat.card_units, hK]
  have h58 : 5 ^ f % 8 = 5 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have h125 : 125 ≤ 5 ^ f :=
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨m, hm⟩ : ∃ m, 5 ^ f - 1 = 4 * m := ⟨(5 ^ f - 1) / 4, by omega⟩
  have hm_odd : Odd m := ⟨(m - 1) / 2, by omega⟩
  have hm31 : 31 ≤ m := by omega
  have h4 : 4 ∣ orderOf g := by rw [hg, hcard, hm]; exact dvd_mul_right 4 m
  have hl : orderOf (g ^ 4) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) h4, hg, hcard, hm]; omega
  have hne : g ^ 4 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hl
    omega
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_torus (g ^ 4) (hl ▸ hm_odd) hne
  refine bad_pair_of_prod hx hy (hxy ▸ hl ▸ hm_odd) ?_ ?_ ?_ ?_ <;> rw [hxy, hl] <;> omega

theorem bad_pair_five_even {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 5 ^ f)
    (hf : Even f) : ∃ D₀ D₁ : Subgroup PSL(2, K), Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧
      ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h24 : 5 ^ 2 - 1 ∣ 5 ^ f - 1 := Nat.pow_sub_one_dvd_pow_sub_one 5 (even_iff_two_dvd.1 hf)
    exact (by norm_num : 3 ∣ 5 ^ 2 - 1).trans h24
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  obtain ⟨D, hD, hDN, hDc⟩ := exists_borel_data ht
  have hR : IsPGroup 5 (rootGroup K) := IsPGroup.of_card (n := f) ((card_rootGroup).trans hK)
  obtain ⟨g, hg⟩ := exists_bad_of_normalizes (ℓ := 5) (by norm_num) (by norm_num) (by norm_num)
    hD hR hDN hDc
  exact ⟨D, D.map (MulAut.conj g).toMonoidHom, hD,
    by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hD], hg⟩

theorem le_pRank_char_three {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 3 ^ f) :
    f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup PSL(2, K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact Insp.le_pRank (by norm_num) (rootGroup K) le_top rootGroup_isElemAbelian
    ((card_rootGroup).trans hK)

theorem exists_bad_pair_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h2 : p ^ f ≠ 2) (h3 : p ^ f ≠ 3) (h4 : p ^ f ≠ 4)
    (h5 : p ^ f ≠ 5) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup PSL(2, K)) ≤ 1) :
    ∃ D₀ D₁ : Subgroup PSL(2, K), Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧
      ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have : 3 ≤ f := by
      by_contra hlt
      have : f = 1 ∨ f = 2 := by omega
      rcases this with rfl | rfl <;> simp_all
    exact bad_pair_char_two hK this
  by_cases hp3 : p = 3
  · subst hp3
    have : f ≤ 1 := (le_pRank_char_three hK).trans hrk
    have : f = 1 := by omega
    subst this
    simp at h3
  by_cases hp5 : p = 5
  · subst hp5
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have : f = 1 := by omega
      subst this
      simp at h5
    rcases Nat.even_or_odd f with he | ho
    · exact bad_pair_five_even hK he
    · exact bad_pair_five_odd hK ho (by obtain ⟨k, hk⟩ := ho; omega)
  · have hp7 : 7 ≤ p := by
      have h2' := hp.two_le
      have hne4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      have hne6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
      omega
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    exact bad_pair_large_char hp7

theorem exists_bad_pair_of_lieModel {S : Type} [Group S] [Finite S]
    {p f : ℕ} (hL : LieModel S .PSL 2 p f) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1)
    (hA5 : ¬ CFSG.Quasithin.IsAlt 5 S) :
    ∃ D₀ D₁ : Subgroup S, Nat.card D₀ = 3 ∧ Nat.card D₁ = 3 ∧ ¬ Z3E9A5Mod2 (D₀ ⊔ D₁) := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨hp, hf, -, h22, h23⟩ := hadm
    have h2 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
    have h3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
    have h4 : p ^ f ≠ 4 := fun h => hA5 ⟨e.trans
      (CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
        (Or.inl (hK.trans h))).some⟩
    have h5 : p ^ f ≠ 5 := fun h => hA5 ⟨e.trans
      (CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
        (Or.inr (hK.trans h))).some⟩
    let e' : S ≃* PSL(2, K) := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup PSL(2, K)) ≤ 1 := by
      have := Insp.pRank_congr (p := 3) (G := S) (B := PSL(2, K)) (by norm_num) e'
      omega
    obtain ⟨D₀, D₁, h0, h1, hbad⟩ := exists_bad_pair_psl2 hp hf hK h2 h3 h4 h5 hrk'
    exact ⟨D₀.map e'.symm.toMonoidHom, D₁.map e'.symm.toMonoidHom,
      by rw [Subgroup.card_map_of_injective e'.symm.injective, h0],
      by rw [Subgroup.card_map_of_injective e'.symm.injective, h1],
      bad_pair_of_mulEquiv e' hbad⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK.InspPS
