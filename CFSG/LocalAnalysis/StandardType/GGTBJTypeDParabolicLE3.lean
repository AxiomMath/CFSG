module

public import CFSG.LocalAnalysis.StandardType.GGTBJWeylParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGTWReflConj
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem cartanD_ne_zero (n : ℕ) {u v : Fin n} (h : u ≠ v) :
    CartanMatrix.D n u v ≠ 0 ↔ ( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
      (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
      (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
      (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
  have hz : CartanMatrix.D n u v = 0 ↔ ¬( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
      (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
      (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
      (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
    unfold CartanMatrix.D
    rw [Matrix.of_apply, if_neg h]
    by_cases hn : n ≤ 2
    · rw [if_pos hn]
      have hAll : ¬( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
          (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
          (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
          (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
      simp [hAll]
    · rw [if_neg hn]
      by_cases hA : (u.val + 1 = v.val ∧ v.val + 2 < n)
      · rw [if_pos hA]; simp [hA]
      · rw [if_neg hA]
        by_cases hB : (v.val + 1 = u.val ∧ u.val + 2 < n)
        · rw [if_pos hB]; simp [hB]
        · rw [if_neg hB]
          by_cases hC : (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n))
          · rw [if_pos hC]; simp [hC]
          · rw [if_neg hC]
            by_cases hD : (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n))
            · rw [if_pos hD]; simp [hD]
            · rw [if_neg hD]; simp [hA, hB, hC, hD]
  constructor
  · intro hD; by_contra hP; exact hD (hz.mpr hP)
  · intro hP; intro hD; exact (hz.mp hD) hP

private lemma cartanD_eq_neg_one {n : ℕ} {u v : Fin n} (h : u ≠ v)
    (hz : CartanMatrix.D n u v ≠ 0) : CartanMatrix.D n u v = -1 := by
  by_cases hn : n ≤ 2
  · exfalso
    apply hz
    unfold CartanMatrix.D
    rw [Matrix.of_apply, if_neg h, if_pos hn]
  · unfold CartanMatrix.D at hz ⊢
    rw [Matrix.of_apply, if_neg h, if_neg hn] at hz ⊢
    split_ifs at hz ⊢ <;> first | rfl | (exfalso; exact hz rfl) | omega

private lemma cartanD_shift_ne_zero_iff {n c : ℕ} (hc : c ≤ n) (h3 : 3 ≤ n - c)
    {i j : Fin n} (hij : i ≠ j) (hi : c ≤ i.val) (hj : c ≤ j.val) :
    (CartanMatrix.D n i j ≠ 0) ↔
      (CartanMatrix.D (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
        ⟨j.val - c, by omega⟩ ≠ 0) := by
  have hij' : (⟨i.val - c, by omega⟩ : Fin (n - c)) ≠ ⟨j.val - c, by omega⟩ := by
    intro h; exact hij (by ext; have := congrArg Fin.val h; simp at this; omega)
  rw [cartanD_ne_zero n hij, cartanD_ne_zero (n - c) hij']
  simp only [Fin.val_mk]
  constructor
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · rcases hB with hB | hB
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inr (by omega)⟩))
    · rcases hB with hB | hB
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, Or.inl (by omega)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, Or.inr (by omega)⟩))
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · rcases hB with hB | hB
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inr (by omega)⟩))
    · rcases hB with hB | hB
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, Or.inl (by omega)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, Or.inr (by omega)⟩))

private lemma cartanD_shift_eq_val {n c : ℕ} (hc : c ≤ n) (h3 : 3 ≤ n - c)
    {i j : Fin n} (hi : c ≤ i.val) (hj : c ≤ j.val) :
    CartanMatrix.D n i j =
      CartanMatrix.D (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
        ⟨j.val - c, by omega⟩ := by
  by_cases hij : i = j
  · subst hij
    rw [show CartanMatrix.D n i i = 2 from by
      unfold CartanMatrix.D; rw [Matrix.of_apply, if_pos rfl]]
    rw [show CartanMatrix.D (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
        ⟨i.val - c, by omega⟩ = 2 from by
      unfold CartanMatrix.D; rw [Matrix.of_apply, if_pos rfl]]
  · have hiff := cartanD_shift_ne_zero_iff hc h3 hij hi hj
    by_cases hz : CartanMatrix.D n i j = 0
    · have hz' : CartanMatrix.D (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
          ⟨j.val - c, by omega⟩ = 0 := by
        by_contra hne; exact (hiff.mpr hne) hz
      rw [hz, hz']
    · have h1 : CartanMatrix.D n i j = -1 := cartanD_eq_neg_one hij hz
      have h2 : CartanMatrix.D (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
          ⟨j.val - c, by omega⟩ = -1 :=
        cartanD_eq_neg_one
          (by intro h; exact hij (by ext; have := congrArg Fin.val h; simp at this; omega))
          (hiff.mp hz)
      rw [h1, h2]

private lemma ggCoxeterMatrixD_shift_val {n c : ℕ} (hc : c ≤ n) (h3 : 3 ≤ n - c)
    (i j : Fin n) (hi : c ≤ i.val) (hj : c ≤ j.val) :
    ggCoxeterMatrixD n i j =
      ggCoxeterMatrixD (n - c) (⟨i.val - c, by omega⟩ : Fin (n - c))
        ⟨j.val - c, by omega⟩ := by
  rw [ggCoxeterMatrixD_apply, ggCoxeterMatrixD_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos (by ext; simp)]
  · have hij' : (⟨i.val - c, by omega⟩ : Fin (n - c)) ≠ ⟨j.val - c, by omega⟩ := by
      intro h; exact hij (by ext; have := congrArg Fin.val h; simp at this; omega)
    rw [if_neg hij, if_neg hij']
    rw [cartanD_shift_eq_val hc h3 hi hj]

private lemma ggIsWeylMatrix_D_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    GGIsWeylMatrix (ggCoxeterMatrixD N) := by
  by_cases h3 : N = 3
  · subst h3
    have hDA : ggCoxeterMatrixD 3 = (CoxeterMatrix.A 3).reindex (Equiv.swap 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> (rw [CoxeterMatrix.reindex_apply]; decide)
    exact Or.inl ⟨3, Equiv.swap 0 1, by norm_num, Or.inl hDA⟩
  · refine Or.inl ⟨N, Equiv.refl _, by omega, Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    rfl

private lemma ggIsWeylMatrix_A_of_one_le {N : ℕ} (hN : 1 ≤ N) :
    GGIsWeylMatrix (CoxeterMatrix.A N) :=
  Or.inl ⟨N, Equiv.refl _, hN, Or.inl (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl))⟩

private def shiftDEquiv (n c : ℕ) (hc : c ≤ n) :
    {j : Fin n // c ≤ j.val} ≃ Fin (n - c) where
  toFun j := ⟨j.1.val - c, by have := j.1.isLt; omega⟩
  invFun i := ⟨⟨i.val + c, by have := i.isLt; omega⟩, Nat.le_add_left c i.val⟩
  left_inv j := by ext; simp only [Fin.val_mk]; omega
  right_inv i := by ext; simp only [Fin.val_mk]; omega

private def ltSubtypeEquiv (n c : ℕ) (hc : c ≤ n) :
    {j : Fin n // j.val < c} ≃ Fin c where
  toFun j := ⟨j.1.val, j.2⟩
  invFun i := ⟨⟨i.val, by have := i.isLt; omega⟩, i.isLt⟩
  left_inv j := by ext; rfl
  right_inv i := by ext; rfl

private lemma parMatrix_D_eq {n c : ℕ} (hc : c ≤ n) (h3 : 3 ≤ n - c) :
    parMatrix (ggCoxeterMatrixD n) {j : Fin n | c ≤ j.val} =
      (ggCoxeterMatrixD (n - c)).reindex (shiftDEquiv n c hc).symm := by
  ext i j
  simp only [parMatrix_apply, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
  exact ggCoxeterMatrixD_shift_val hc h3 i.1 j.1 i.2 j.2

private lemma coxeterA_apply (n : ℕ) (u v : Fin n) :
    CoxeterMatrix.A n u v =
      if u = v then 1 else if ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) then 3 else 2 := by
  show (if u = v then 1 else if (v.val + 1 = u.val ∨ u.val + 1 = v.val) then 3 else 2) =
       (if u = v then 1 else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then 3 else 2)
  by_cases huv : u = v
  · rw [if_pos huv, if_pos huv]
  · rw [if_neg huv, if_neg huv]
    by_cases h : (v.val + 1 = u.val ∨ u.val + 1 = v.val)
    · rw [if_pos h, if_pos (h.elim Or.inr Or.inl)]
    · rw [if_neg h, if_neg (fun hh => h (hh.elim Or.inr Or.inl))]

private lemma cartanD_tail_ne_zero_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hi : i.val + 1 < n) (hj : j.val + 1 < n) :
    CartanMatrix.D n i j ≠ 0 ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [cartanD_ne_zero n hij]
  constructor
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩) <;> omega
  · rintro (h | h)
    · by_cases hlt : j.val + 2 < n
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))
    · by_cases hlt : i.val + 2 < n
      · exact Or.inr (Or.inl ⟨h, hlt⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, Or.inl (by omega)⟩))

private def shiftAEquiv (n m : ℕ) (hmn : m ≤ n) :
    {j : Fin n // n - m ≤ j.val ∧ j.val + 1 < n} ≃ Fin (m - 1) where
  toFun j := ⟨j.1.val - (n - m), by have h1 := j.2.1; have h2 := j.2.2; have h3 := j.1.isLt; omega⟩
  invFun i := ⟨⟨n - m + i.val, by have := i.isLt; omega⟩, by
    have hi := i.isLt
    constructor
    · show n - m ≤ n - m + i.val; omega
    · show n - m + i.val + 1 < n; omega⟩
  left_inv j := by ext; simp only [Fin.val_mk]; omega
  right_inv i := by ext; simp only [Fin.val_mk]; omega

private lemma parMatrix_A_eq {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    parMatrix (ggCoxeterMatrixD n) {j : Fin n | n - m ≤ j.val ∧ j.val + 1 < n} =
      (CoxeterMatrix.A (m - 1)).reindex (shiftAEquiv n m hmn).symm := by
  ext i j
  simp only [parMatrix_apply, CoxeterMatrix.reindex_apply, Equiv.symm_symm]
  rw [ggCoxeterMatrixD_apply, coxeterA_apply]
  have hi : (shiftAEquiv n m hmn i).val = i.1.val - (n - m) := rfl
  have hj : (shiftAEquiv n m hmn j).val = j.1.val - (n - m) := rfl
  have hile : n - m ≤ i.1.val := i.2.1
  have hjle : n - m ≤ j.1.val := j.2.1
  by_cases hij : i.1 = j.1
  · have hs : shiftAEquiv n m hmn i = shiftAEquiv n m hmn j := by
      rw [Subtype.ext hij]
    rw [if_pos hij, if_pos hs]
  · have hij' : i ≠ j := fun h => hij (congrArg Subtype.val h)
    have hshift : shiftAEquiv n m hmn i ≠ shiftAEquiv n m hmn j :=
      fun h => hij' ((shiftAEquiv n m hmn).injective h)
    rw [if_neg hij, if_neg hshift]
    by_cases hadj : (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val)
    · have hD : CartanMatrix.D n i.1 j.1 ≠ 0 :=
        (cartanD_tail_ne_zero_iff hij i.2.2 j.2.2).mpr hadj
      rw [if_neg hD]
      have hadj' : (shiftAEquiv n m hmn i).val + 1 = (shiftAEquiv n m hmn j).val ∨
          (shiftAEquiv n m hmn j).val + 1 = (shiftAEquiv n m hmn i).val := by
        rw [hi, hj]; omega
      rw [if_pos hadj']
    · have hD0 : CartanMatrix.D n i.1 j.1 = 0 := by
        by_contra hne
        exact hadj ((cartanD_tail_ne_zero_iff hij i.2.2 j.2.2).mp hne)
      rw [if_pos hD0]
      have hadj' : ¬ ((shiftAEquiv n m hmn i).val + 1 = (shiftAEquiv n m hmn j).val ∨
          (shiftAEquiv n m hmn j).val + 1 = (shiftAEquiv n m hmn i).val) := by
        rw [hi, hj]; omega
      rw [if_neg hadj']

private theorem cI_mem_closure_singleton_eq {E : Type} [Group E] {g t : E}
    (hg : g * g = 1) (ht : t ∈ Subgroup.closure ({g} : Set E)) : t = 1 ∨ t = g := by
  refine Subgroup.closure_induction (p := fun t _ => t = 1 ∨ t = g) ?_ ?_ ?_ ?_ ht
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  · exact Or.inl rfl
  · intro x y hx hy ihx ihy
    rcases ihx with hx1 | hxg <;> rcases ihy with hy1 | hyg
    · exact Or.inl (by simp [hx1, hy1])
    · exact Or.inr (by simp [hx1, hyg])
    · exact Or.inr (by simp [hxg, hy1])
    · exact Or.inl (by rw [hxg, hyg]; exact hg)
  · intro x hx ih
    rcases ih with hx1 | hxg
    · exact Or.inl (by rw [hx1]; exact inv_one)
    · exact Or.inr (by rw [hxg]; exact inv_eq_of_mul_eq_one_right hg)

private theorem cI_refl_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {φ : MulAut ↥Bs} (hr : GGIsReflection p φ) : φ ≠ 1 := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Nonempty ↥Bs := ⟨(1 : ↥Bs)⟩
  rintro rfl
  obtain ⟨-, hc⟩ := hr
  simp only [MulAut.one_apply] at hc
  have hc' : Nat.card {b : ↥Bs // True} * p = Nat.card ↥Bs := by simpa using hc
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at hc'
  have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

private theorem cI_reflConjSimple_subsingleton {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {Λ : Type} [Nonempty Λ]
    (φ : Λ → MulAut ↥Bs) (hA : A = Subgroup.closure (Set.range φ))
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hsub : Subsingleton Λ) :
    GGReflConjSimple p A φ := by
  let i₀ : Λ := Classical.arbitrary Λ
  intro t ht hr
  rw [hA] at ht
  have hrange : Set.range φ = {φ i₀} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton_iff.mpr (congrArg φ (hsub.allEq i i₀))
    · rintro rfl
      exact ⟨i₀, rfl⟩
  rw [hrange] at ht
  have hg : φ i₀ * φ i₀ = 1 := by
    have h := (hrefl i₀).1
    simpa [pow_two] using h
  have ht' : t = 1 ∨ t = φ i₀ := cI_mem_closure_singleton_eq hg ht
  rcases ht' with h | h
  · exact absurd h (cI_refl_ne_one hr)
  · exact ⟨1, Subgroup.one_mem _, i₀, by rw [h]; group⟩

private theorem cI_isElemAbelian {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : IsElemAbelian p Bs := by
  have hcomm : ∀ a b : Bs, a * b = b * a := by
    intro a b
    apply Additive.ofMul.injective
    apply ι.injective
    change ι (Additive.ofMul a + Additive.ofMul b) =
      ι (Additive.ofMul b + Additive.ofMul a)
    rw [map_add, map_add, add_comm]
  have hpow : ∀ b : Bs, b ^ p = 1 := by
    intro b
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_self, zero_smul, ofMul_one, map_zero]
  have h := isElemAbelian_range hcomm hpow Bs.subtype
  rwa [Subgroup.range_subtype] at h

theorem ggTBJTypeDParabolicLE3_endD {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n c : ℕ} (hc : 1 ≤ c) (hc3 : c ≤ 3) (hnc : 3 ≤ n - c)
    {M : CoxeterMatrix (Fin n)} (hM : M = ggCoxeterMatrixD n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.D n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)} (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Fin n // c ≤ j.val} => φ j)) :
    (c = 1 → GGResSideDatum p Bs X J) ∧ (2 ≤ c → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  subst hM
  subst hC
  have hn4 : 4 ≤ n := by omega
  let Jset : Set (Fin n) := {j | c ≤ j.val}
  let T : Finset (Fin n) := Finset.univ.filter (fun j => j.val < c)
  have hTmem : ∀ j : Fin n, j ∈ T ↔ j.val < c := by intro j; simp [T]
  have hTnot : ∀ j : Fin n, j ∉ T ↔ c ≤ j.val := by
    intro j; rw [hTmem]; constructor <;> omega
  have hcD : c ≤ n := by omega
  have hTcard : T.card = c := by
    have h1 : T.card = Fintype.card {j : Fin n // j.val < c} :=
      (Fintype.card_subtype (p := fun j : Fin n => j.val < c)).symm
    rw [h1]
    exact (Fintype.card_congr (ltSubtypeEquiv n c hcD)).trans (Fintype.card_fin c)
  have hcardD : Fintype.card Jset = n - c :=
    (Fintype.card_congr (shiftDEquiv n c hcD)).trans (Fintype.card_fin _)
  have hJset : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j.1) := hJ
  have hWM : GGIsWeylMatrix (ggCoxeterMatrixD n) := ggIsWeylMatrix_D_of_three_le (by omega)
  have hMC : GGIntCartan (ggCoxeterMatrixD n) (CartanMatrix.D n) := ggIntCartan_D n
  have hWMJ_Jset : GGIsWeylMatrix (parMatrix (ggCoxeterMatrixD n) Jset) := by
    rw [parMatrix_D_eq hcD hnc]
    exact l05nBL_weyl_reindex (ggIsWeylMatrix_D_of_three_le hnc) (shiftDEquiv n c hcD).symm
  have hIntD : GGIntCartan (parMatrix (ggCoxeterMatrixD n) Jset)
      (fun j j' => CartanMatrix.D n j.1 j'.1) :=
    ⟨fun j => (ggIntCartan_D n).1 j.1,
     fun j j' hij => (ggIntCartan_D n).2 j.1 j'.1 (fun h => hij (Subtype.ext h))⟩
  have h3Jset : 3 ≤ Fintype.card Jset := by rw [hcardD]; exact hnc
  have hRC_Jset : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j.1) :=
    ggReflConjSimple_of_weylMatrix hp (M := parMatrix (ggCoxeterMatrixD n) Jset)
      (C := fun j j' => CartanMatrix.D n j.1 j'.1) (l05nBL_weylFixed hWMJ_Jset) h3Jset hIntD ι
      (fun j : Jset => φ j.1) (fun j : Jset => h j.1) (fun j : Jset => α j.1)
      (fun j j' => hpair j.1 j'.1) (fun j w => hlin j.1 w) hJset
  let eT : Jset ≃ {j : Fin n // j ∉ T} := Equiv.subtypeEquivRight (fun j => (hTnot j).symm)
  have hJ_T : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Fin n // j ∉ T} => φ j.1) := by
    rw [hJset]
    congr 1
    ext x
    constructor
    · rintro ⟨j, hx⟩; exact ⟨eT j, hx⟩
    · rintro ⟨j, hx⟩; exact ⟨eT.symm j, hx⟩
  have hparT : parMatrix (ggCoxeterMatrixD n) {j : Fin n | j ∉ T} =
      (parMatrix (ggCoxeterMatrixD n) Jset).reindex eT := rfl
  have hWMJ_T : GGIsWeylMatrix (parMatrix (ggCoxeterMatrixD n) {j : Fin n | j ∉ T}) := by
    rw [hparT]
    exact l05nBL_weyl_reindex hWMJ_Jset eT
  have hRC_T : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin n // j ∉ T} => φ j.1) := by
    intro t ht hr
    obtain ⟨w, hw, i, hi⟩ := hRC_Jset t ht hr
    exact ⟨w, hw, eT i, hi⟩
  have hmain := ggTBJWeylParabolicLE3 (p := p) (X := X) (J := J)
    (M := ggCoxeterMatrixD n) (C := CartanMatrix.D n) hWM hMC hlin hrefl hpair hf hclos
    T (by omega) (by omega) hJ_T hWMJ_T hRC_T
  constructor
  · intro hc1
    have hcard1 : T.card = 1 := by rw [hTcard, hc1]
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
    exact hmain.1 b hb
  · intro hc2
    exact hmain.2 (by rw [hTcard]; exact hc2)

theorem ggTBJTypeDParabolicLE3_endA {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) (hc3 : n - m + 1 ≤ 3)
    (hn : 4 ≤ n)
    {M : CoxeterMatrix (Fin n)} (hM : M = ggCoxeterMatrixD n)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : C = CartanMatrix.D n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)} (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin n // n - m ≤ j.val ∧ j.val + 1 < n} => φ j)) :
    (n - m + 1 = 1 → GGResSideDatum p Bs X J) ∧ (2 ≤ n - m + 1 → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  subst hM
  subst hC
  let Jset : Set (Fin n) := {j | n - m ≤ j.val ∧ j.val + 1 < n}
  let T : Finset (Fin n) := Finset.univ.filter (fun j => j.val < n - m ∨ j.val = n - 1)
  have hTmem : ∀ j : Fin n, j ∈ T ↔ (j.val < n - m ∨ j.val = n - 1) := by intro j; simp [T]
  have hTnot : ∀ j : Fin n, j ∉ T ↔ (n - m ≤ j.val ∧ j.val + 1 < n) := by
    intro j
    rw [hTmem]
    constructor
    · intro h
      constructor
      · by_contra hlt; exact h (Or.inl (by omega))
      · by_contra hge; exact h (Or.inr (by omega))
    · rintro ⟨h1, h2⟩ hh
      rcases hh with hh | hh <;> omega
  have hTcard : T.card = n - m + 1 := by
    have hsplit : T = (Finset.univ.filter (fun j : Fin n => j.val < n - m)) ∪
        ({⟨n - 1, by omega⟩} : Finset (Fin n)) := by
      ext j
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by rw [h])
    have hdisj : Disjoint (Finset.univ.filter (fun j : Fin n => j.val < n - m))
        ({⟨n - 1, by omega⟩} : Finset (Fin n)) := by
      rw [Finset.disjoint_left]
      intro j hj hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_singleton] at hmem
      have hmem' : j.val = n - 1 := by simpa using congrArg Fin.val hmem
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    have hcardlt : (Finset.univ.filter (fun j : Fin n => j.val < n - m)).card = n - m := by
      have h1 : (Finset.univ.filter (fun j : Fin n => j.val < n - m)).card =
          Fintype.card {j : Fin n // j.val < n - m} :=
        (Fintype.card_subtype (p := fun j : Fin n => j.val < n - m)).symm
      rw [h1]
      exact (Fintype.card_congr (ltSubtypeEquiv n (n - m) (by omega))).trans
        (Fintype.card_fin _)
    rw [hcardlt, Finset.card_singleton]
  have hcardA : Fintype.card Jset = m - 1 :=
    (Fintype.card_congr (shiftAEquiv n m hmn)).trans (Fintype.card_fin _)
  have hJset : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Jset => φ j.1) := hJ
  have hWM : GGIsWeylMatrix (ggCoxeterMatrixD n) := ggIsWeylMatrix_D_of_three_le (by omega)
  have hMC : GGIntCartan (ggCoxeterMatrixD n) (CartanMatrix.D n) := ggIntCartan_D n
  have hWMJ_Jset : GGIsWeylMatrix (parMatrix (ggCoxeterMatrixD n) Jset) := by
    rw [parMatrix_A_eq hm hmn]
    exact l05nBL_weyl_reindex (ggIsWeylMatrix_A_of_one_le (by omega : 1 ≤ m - 1))
      (shiftAEquiv n m hmn).symm
  have hIntA : GGIntCartan (parMatrix (ggCoxeterMatrixD n) Jset)
      (fun j j' => CartanMatrix.D n j.1 j'.1) :=
    ⟨fun j => (ggIntCartan_D n).1 j.1,
     fun j j' hij => (ggIntCartan_D n).2 j.1 j'.1 (fun h => hij (Subtype.ext h))⟩
  have hRC_Jset : GGReflConjSimple p (ggAutomizer J Bs) (fun j : Jset => φ j.1) := by
    by_cases hm2 : m = 2
    · subst hm2
      haveI : Nonempty Jset := ⟨(shiftAEquiv n 2 hmn).symm ⟨0, by omega⟩⟩
      haveI : Subsingleton Jset := ⟨fun a b =>
        (shiftAEquiv n 2 hmn).injective (Fin.ext (by
          have ha := (shiftAEquiv n 2 hmn a).isLt
          have hb := (shiftAEquiv n 2 hmn b).isLt
          omega))⟩
      exact cI_reflConjSimple_subsingleton (fun j : Jset => φ j.1) hJset
        (fun j => hrefl j.1) inferInstance
    · by_cases hm3 : m = 3
      · have hm1 : 2 ≤ m - 1 := by omega
        let fJ := ggParabolic_equiv_of_generator_equiv (ggCoxeterMatrixD n) Jset φ f hf hJset
        have hfJ : ∀ j : Jset,
            (fJ ((parMatrix (ggCoxeterMatrixD n) Jset).simple j) : MulAut ↥Bs) = φ j.1 :=
          fun j => ggParabolic_equiv_of_generator_equiv_simple (ggCoxeterMatrixD n) f
            φ hf Jset hJset j
        exact ggTW_refl_conj_of_typeA hp hm1 (cI_isElemAbelian ι)
          (shiftAEquiv n m hmn).symm (parMatrix_A_eq hm hmn) (ggAutomizer J Bs) fJ
          (fun j : Jset => φ j.1) hfJ (fun j => hrefl j.1)
      · have hm4 : 4 ≤ m := by omega
        have h3 : 3 ≤ Fintype.card Jset := by rw [hcardA]; omega
        exact ggReflConjSimple_of_weylMatrix hp (l05nBL_weylFixed hWMJ_Jset) h3 hIntA ι
          (fun j : Jset => φ j.1) (fun j : Jset => h j.1) (fun j : Jset => α j.1)
          (fun j j' => hpair j.1 j'.1) (fun j w => hlin j.1 w) hJset
  let eT : Jset ≃ {j : Fin n // j ∉ T} := Equiv.subtypeEquivRight (fun j => (hTnot j).symm)
  have hJ_T : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Fin n // j ∉ T} => φ j.1) := by
    rw [hJset]
    congr 1
    ext x
    constructor
    · rintro ⟨j, hx⟩; exact ⟨eT j, hx⟩
    · rintro ⟨j, hx⟩; exact ⟨eT.symm j, hx⟩
  have hparT : parMatrix (ggCoxeterMatrixD n) {j : Fin n | j ∉ T} =
      (parMatrix (ggCoxeterMatrixD n) Jset).reindex eT := rfl
  have hWMJ_T : GGIsWeylMatrix (parMatrix (ggCoxeterMatrixD n) {j : Fin n | j ∉ T}) := by
    rw [hparT]
    exact l05nBL_weyl_reindex hWMJ_Jset eT
  have hRC_T : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin n // j ∉ T} => φ j.1) := by
    intro t ht hr
    obtain ⟨w, hw, i, hi⟩ := hRC_Jset t ht hr
    exact ⟨w, hw, eT i, hi⟩
  have hmain := ggTBJWeylParabolicLE3 (p := p) (X := X) (J := J)
    (M := ggCoxeterMatrixD n) (C := CartanMatrix.D n) hWM hMC hlin hrefl hpair hf hclos
    T (by omega) (by omega) hJ_T hWMJ_T hRC_T
  constructor
  · intro hc1
    have hcard1 : T.card = 1 := by rw [hTcard, hc1]
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
    exact hmain.1 b hb
  · intro hc2
    exact hmain.2 (by rw [hTcard]; exact hc2)

end CFSG.StandardType

end
