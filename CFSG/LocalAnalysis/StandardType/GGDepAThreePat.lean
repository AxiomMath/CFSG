module

public import CFSG.LocalAnalysis.StandardType.GGDepAThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTWPatE8
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma lr7p_A_symm (n : ℕ) (i j : Fin n) : CartanMatrix.A n i j = CartanMatrix.A n j i := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    by_cases h : (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    · rw [if_pos h, if_pos (h.elim Or.inr Or.inl)]
    · rw [if_neg h, if_neg (fun hh => h (hh.elim Or.inr Or.inl))]

private lemma lr7p_cartanA_eq_two {n : ℕ} {i j : Fin n}
    (h : CartanMatrix.A n i j = 2) : i = j := by
  by_contra hij
  simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false] at h
  split_ifs at h <;> omega

private lemma lr7p_cartanA_mem (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j = 2 ∨ CartanMatrix.A n i j = -1 ∨ CartanMatrix.A n i j = 0 := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (by simp [CartanMatrix.A])
  · simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

private lemma lr7p_intCartan_off {Γ : Type*} {M : CoxeterMatrix Γ}
    {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {i j : Γ} (hij : i ≠ j) :
    C i j = 0 ∨ C i j = -1 ∨ C i j = -2 ∨ C i j = -3 := by
  rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ |
    ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) h2 h3 h1 with ⟨ha, -⟩ | ⟨ha, -⟩
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
  · rcases l05nDP4_neg_pair_of_mul (Or.inr rfl) h2 h3 h1 with ⟨ha, -⟩ | ⟨ha, -⟩
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr ha))

private lemma lr7p_no_neg_three {Γ : Type*} {M : CoxeterMatrix Γ}
    {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {i j : Γ}
    (hsym : (C i j : ZMod 3) = (C j i : ZMod 3))
    (hij : i ≠ j) : C i j ≠ -3 := by
  intro h3
  rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ |
    ⟨-, h1, h2, h3'⟩ | ⟨-, h1, h2, h3'⟩
  · omega
  · omega
  · rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) h2 h3' h1 with ⟨ha, -⟩ | ⟨ha, -⟩
    · omega
    · omega
  · rcases l05nDP4_neg_pair_of_mul (Or.inr rfl) h2 h3' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · omega
    · rw [h3, hb] at hsym
      exact absurd hsym (by decide)

private lemma lr7p_cast {a b : ℤ}
    (ha : a = 0 ∨ a = -1 ∨ a = -2 ∨ a = -3)
    (hb : b = 2 ∨ b = 0 ∨ b = -1) (h : (a : ZMod 3) = (b : ZMod 3))
    (h2 : b = 2 → a = 2) (h3 : a ≠ -3) : a = b := by
  rcases ha with rfl | rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)
  · rcases hb with rfl | rfl | rfl
    · exact absurd (h2 rfl) (by norm_num)
    · exact absurd h (by decide)
    · rfl
  · rcases hb with rfl | rfl | rfl <;> exact absurd h (by decide)
  · exact absurd rfl h3

private lemma lr7p_cartanA_emb {N : ℕ} (hN : N = 6 ∨ N = 9)
    {b' : Fin (N - 1)} (hb : b'.val = 0 ∨ b'.val + 2 = N) (i j : Fin (N - 2)) :
    CartanMatrix.A (N - 1)
        (if b'.val = 0 then ⟨i.val + 1, by omega⟩ else ⟨i.val, by omega⟩)
        (if b'.val = 0 then ⟨j.val + 1, by omega⟩ else ⟨j.val, by omega⟩) =
      CartanMatrix.A (N - 2) i j := by
  rcases hN with rfl | rfl <;> rcases hb with h0 | hl
  · simp only [if_pos h0]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h0' : ¬ b'.val = 0 := by omega
    simp only [if_neg h0']
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  · simp only [if_pos h0]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h0' : ¬ b'.val = 0 := by omega
    simp only [if_neg h0']
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]

private theorem lr7p_dispatch {L : ℕ} (hL : L = 4 ∨ L = 7)
    {M : CoxeterMatrix (Option (Fin L))} (hW : GGIsWeylMatrix M)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ (k : Fin L) (μ : ℕ), (μ = 3 ∨ μ = 4) ∧ (∀ i, M none (some i) = if i = k then μ else 2) ∧
      ((k.val = 0 ∨ k.val + 1 = L) ∨ (μ = 3 ∧ (k.val = 1 ∨ k.val + 2 = L)) ∨
        (μ = 3 ∧ L = 7 ∧ (k.val = 2 ∨ k.val = 4))) := by
  have hL3 : 3 ≤ L := by omega
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, e, _hn, hcase⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩
  · have hn1 : n = L + 1 := by
      have hcard := Fintype.card_congr e
      simpa [Fintype.card_fin, Fintype.card_option] using hcard
    subst n
    rcases hcase with hMA | ⟨_hn2, hMB⟩ | ⟨_hn4, hMD⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_A hL3 e hMA hJ
      exact ⟨k, 3, Or.inl rfl, hμ, Or.inl hk⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_B hL3 e hMB hJ
      exact ⟨k, 4, Or.inr rfl, hμ, Or.inl hk⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_D hL3 e hMD hJ
      exact ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inl ⟨rfl, hk⟩)⟩
  · exfalso
    have hcard := Fintype.card_congr e
    have h6 : (6 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega
  · exfalso
    have hcard := Fintype.card_congr e
    have h7 : (7 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega
  · have hL7 : L = 7 := by
      have hcard := Fintype.card_congr e
      have h8 : (8 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
      omega
    subst L
    obtain ⟨k, hk, hμ⟩ := ggTW_ext_E8 e hMe hJ
    exact ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inr ⟨rfl, rfl, hk⟩)⟩
  · exfalso
    have hcard := Fintype.card_congr e
    have h4 : (4 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega
  · exfalso
    have hcard := Fintype.card_congr e
    have h2 : (2 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega

private theorem lr7p_pattern_abs {L : ℕ} (hL : L = 4 ∨ L = 7)
    {M : CoxeterMatrix (Option (Fin L))} {C : Matrix (Option (Fin L)) (Option (Fin L)) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin L, C (some i) (some j) = CartanMatrix.A L i j) :
    ∃ (k : Fin L) (m n : ℤ),
      (((k.val = 0 ∨ k.val + 1 = L) ∧
          ((m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1))) ∨
        (3 ≤ L ∧ (k.val = 1 ∨ k.val + 2 = L) ∧ m = -1 ∧ n = -1) ∨
        (L = 7 ∧ (k.val = 2 ∨ k.val = 4) ∧ m = -1 ∧ n = -1)) ∧
      ∀ i, C none (some i) = (if i = k then m else 0) ∧
        C (some i) none = (if i = k then n else 0) := by
  have hMA := l05nDP4_MJ hC hJ
  obtain ⟨k, μ, hμ, hrow, hpos⟩ := lr7p_dispatch hL hW hMA
  have hL3 : 3 ≤ L := by omega
  rcases hμ with rfl | rfl
  ·
    refine ⟨k, -1, -1, ?_, ?_⟩
    · rcases hpos with hend | ⟨-, hsec⟩ | ⟨-, hL7, hk24⟩
      · exact Or.inl ⟨hend, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr (Or.inl ⟨hL3, hsec, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨hL7, hk24, rfl, rfl⟩)
    · intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 3 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, -⟩ | ⟨hm, h1, h2⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
  ·
    have hkM : M none (some k) = 4 := by rw [hrow k, if_pos rfl]
    have hprod : C none (some k) * C (some k) none = 2 ∧ C none (some k) < 0 ∧
        C (some k) none < 0 := by
      rcases hC.2 none (some k) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ |
        ⟨hm, -, -, -⟩
      · rw [hkM] at hm; omega
      · rw [hkM] at hm; omega
      · exact ⟨h1, h2, h3⟩
      · rw [hkM] at hm; omega
    have hend : k.val = 0 ∨ k.val + 1 = L := by
      rcases hpos with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) hprod.2.1 hprod.2.2 hprod.1 with
      ⟨hm1, hn2⟩ | ⟨hm2, hn1⟩
    · refine ⟨k, -1, -2, Or.inl ⟨hend, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm1 hn2; exact ⟨hm1, hn2⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
    · refine ⟨k, -2, -1, Or.inl ⟨hend, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm2 hn1; exact ⟨hm2, hn1⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega

theorem ggDepAThree_pattern {N : ℕ} (hN : N = 6 ∨ N = 9) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ} (e : Fin (N - 1) ≃ Λ)
    (hb : (e.symm b).val = 0 ∨ (e.symm b).val + 2 = N)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      (CartanMatrix.A (N - 1) (e.symm i) (e.symm j) : ZMod 3)) :
    ∃ (c0 : Fin (N - 1)) (m n : ℤ), GGDepAPatE N (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  set b' : Fin (N - 1) := e.symm b with hb'def
  let emb : Fin (N - 2) → Fin (N - 1) := fun k =>
    if b'.val = 0 then ⟨k.val + 1, by omega⟩ else ⟨k.val, by omega⟩
  have hemb_val : ∀ k : Fin (N - 2), (emb k).val = if b'.val = 0 then k.val + 1 else k.val := by
    intro k
    by_cases h : b'.val = 0
    · simp only [emb, if_pos h]
    · simp only [emb, if_neg h]
  have hemb_ne : ∀ k : Fin (N - 2), emb k ≠ b' := by
    intro k hh
    have hhv : (emb k).val = b'.val := congrArg Fin.val hh
    rw [hemb_val k] at hhv
    rcases hb with h0 | hl
    · rw [if_pos h0] at hhv; omega
    · rw [if_neg (by omega : ¬ b'.val = 0)] at hhv; omega
  let toJ : Fin (N - 2) → {i : Λ // i ≠ b} := fun k => ⟨e (emb k), by
    intro hh
    exact hemb_ne k (by
      have hh' := congrArg e.symm hh
      simpa [← hb'def] using hh')⟩
  let posFun : {i : Λ // i ≠ b} → Fin (N - 2) := fun i =>
    if h : b'.val = 0 then
      ⟨(e.symm i.val).val - 1, by
        have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hlt := (e.symm i.val).isLt
        have hv : (e.symm i.val).val ≠ 0 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, h]))
        omega⟩
    else
      ⟨(e.symm i.val).val, by
        have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hlt := (e.symm i.val).isLt
        have hl : b'.val = N - 2 := by
          rcases hb with h0 | hl
          · exact absurd h0 h
          · omega
        have hv : (e.symm i.val).val ≠ N - 2 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, hl]))
        omega⟩
  have hpos_left : ∀ k : Fin (N - 2), posFun (toJ k) = k := by
    intro k
    apply Fin.ext
    by_cases h0 : b'.val = 0
    · simp only [posFun, toJ, dif_pos h0, hemb_val k, if_pos h0, Equiv.symm_apply_apply]
      omega
    · simp only [posFun, toJ, dif_neg h0, hemb_val k, if_neg h0, Equiv.symm_apply_apply]
  have hpos_right : ∀ i : {i : Λ // i ≠ b}, toJ (posFun i) = i := by
    intro i
    apply Subtype.ext
    have hemb : emb (posFun i) = e.symm i.val := by
      apply Fin.ext
      by_cases h0 : b'.val = 0
      · have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hv : (e.symm i.val).val ≠ 0 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, h0]))
        simp only [posFun, dif_pos h0, emb, if_pos h0, hemb_val, if_pos h0]
        omega
      · simp only [posFun, dif_neg h0, emb, if_neg h0, hemb_val, if_neg h0]
    show e (emb (posFun i)) = i.val
    rw [hemb, Equiv.apply_symm_apply]
  let posEquiv : Fin (N - 2) ≃ {i : Λ // i ≠ b} :=
    { toFun := toJ, invFun := posFun, left_inv := hpos_left, right_inv := hpos_right }
  let σ : Option (Fin (N - 2)) ≃ Option {i : Λ // i ≠ b} := Equiv.optionCongr posEquiv
  let M₀ : CoxeterMatrix (Option (Fin (N - 2))) := MK.reindex σ.symm
  let C₀ : Matrix (Option (Fin (N - 2))) (Option (Fin (N - 2))) ℤ :=
    Matrix.reindex σ.symm σ.symm CK
  have hM₀ : GGIsWeylMatrix M₀ := l05nDP4_weyl_reindex hWK σ.symm
  have hC₀ : GGIntCartan M₀ C₀ := by
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · simp only [C₀, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hCK.1 (σ u)
    · have h := hCK.2 (σ u) (σ v) (fun hh => huv (σ.injective hh))
      simpa [M₀, C₀, CoxeterMatrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        using h
  have hemb_c0 : ∀ k : Fin (N - 2), e.symm (posEquiv k).val = emb k := by
    intro k
    show e.symm (e (emb k)) = emb k
    exact e.symm_apply_apply (emb k)
  have hJ₀ : ∀ i j : Fin (N - 2), C₀ (some i) (some j) = CartanMatrix.A (N - 2) i j := by
    intro i j
    change CK (some (posEquiv i)) (some (posEquiv j)) = CartanMatrix.A (N - 2) i j
    by_cases hij : i = j
    · subst hij
      rw [hCK.1 (posEquiv i)]
      simp [CartanMatrix.A]
    · have hne : posEquiv i ≠ posEquiv j := fun h => hij (posEquiv.injective h)
      have hmod : (CK (some (posEquiv i)) (some (posEquiv j)) : ZMod 3) =
          (CartanMatrix.A (N - 2) i j : ZMod 3) := by
        have h1 := hJ (posEquiv i) (posEquiv j)
        rw [hemb_c0 i, hemb_c0 j] at h1
        rw [h1, lr7p_cartanA_emb hN hb i j]
      have hsym : (CK (some (posEquiv i)) (some (posEquiv j)) : ZMod 3) =
          (CK (some (posEquiv j)) (some (posEquiv i)) : ZMod 3) := by
        rw [hJ (posEquiv i) (posEquiv j), hJ (posEquiv j) (posEquiv i)]
        rw [hemb_c0 i, hemb_c0 j]
        rw [lr7p_A_symm (N - 1) (emb i) (emb j)]
      refine lr7p_cast ?_ ?_ hmod ?_ ?_
      · exact lr7p_intCartan_off hCK (fun h => hne (Option.some.inj h))
      · rcases lr7p_cartanA_mem (N - 2) i j with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · intro hb2
        exact absurd (lr7p_cartanA_eq_two hb2) hij
      · exact lr7p_no_neg_three hCK hsym (fun h => hne (Option.some.inj h))
  have hL4 : N - 2 = 4 ∨ N - 2 = 7 := by rcases hN with rfl | rfl <;> norm_num
  obtain ⟨k, m, n, hpat, hrow⟩ := lr7p_pattern_abs (L := N - 2) hL4 hM₀ hC₀ hJ₀
  have hposeq : (if b'.val = 0 then (emb k).val - 1 else (emb k).val) = k.val := by
    by_cases h0 : b'.val = 0
    · rw [if_pos h0, hemb_val k, if_pos h0]; omega
    · rw [if_neg h0, hemb_val k, if_neg h0]
  have hiff : ∀ i : {i : Λ // i ≠ b}, posEquiv.symm i = k ↔ e.symm i.val = emb k := by
    intro i
    constructor
    · intro hh
      have hi : i = posEquiv k := by rw [← hh, Equiv.apply_symm_apply]
      calc e.symm i.val = e.symm (posEquiv k).val := by rw [hi]
        _ = emb k := hemb_c0 k
    · intro hh
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      show i.val = e (emb k)
      rw [← hh, Equiv.apply_symm_apply]
  have hrow' : ∀ i : {i : Λ // i ≠ b}, CK none (some i) =
      (if e.symm i = emb k then m else 0) ∧
      CK (some i) none = (if e.symm i = emb k then n else 0) := by
    intro i
    have hC0 : C₀ none (some (posEquiv.symm i)) = CK none (some i) := by
      show CK (σ none) (σ (some (posEquiv.symm i))) = CK none (some i)
      simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.apply_symm_apply]
    have hC0' : C₀ (some (posEquiv.symm i)) none = CK (some i) none := by
      show CK (σ (some (posEquiv.symm i))) (σ none) = CK (some i) none
      simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.apply_symm_apply]
    have hrowi := hrow (posEquiv.symm i)
    rw [hC0, hC0'] at hrowi
    rcases hrowi with ⟨hr1, hr2⟩
    refine ⟨?_, ?_⟩
    · by_cases hik : e.symm i = emb k
      · have h2 : posEquiv.symm i = k := (hiff i).2 hik
        rw [if_pos h2] at hr1
        rw [if_pos hik]
        exact hr1
      · have h2 : posEquiv.symm i ≠ k := fun hh => hik ((hiff i).1 hh)
        rw [if_neg h2] at hr1
        rw [if_neg hik]
        exact hr1
    · by_cases hik : e.symm i = emb k
      · have h2 : posEquiv.symm i = k := (hiff i).2 hik
        rw [if_pos h2] at hr2
        rw [if_pos hik]
        exact hr2
      · have h2 : posEquiv.symm i ≠ k := fun hh => hik ((hiff i).1 hh)
        rw [if_neg h2] at hr2
        rw [if_neg hik]
        exact hr2
  refine ⟨emb k, m, n, ?_, fun i => hrow' i⟩
  unfold GGDepAPatE
  rcases hpat with hABC | hD | hE8
  · left
    unfold GGDepAPat
    refine ⟨hb, hemb_ne k, Or.inl ⟨?_, hABC.2⟩⟩
    simp only [hposeq]
    exact hABC.1
  · left
    unfold GGDepAPat
    refine ⟨hb, hemb_ne k, Or.inr (Or.inl ⟨hD.1, ?_, hD.2.2.1, hD.2.2.2⟩)⟩
    simp only [hposeq]
    exact hD.2.1
  · right
    have hN9 : N = 9 := by omega
    refine ⟨hN9, hb, hemb_ne k, hE8.2.2.1, hE8.2.2.2, ?_⟩
    simp only [hposeq]
    exact hE8.2.1

end CFSG.StandardType
