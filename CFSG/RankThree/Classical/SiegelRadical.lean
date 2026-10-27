module

public import CFSG.RankThree.Classical.CentralPairing
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank
open scoped Matrix

section Decomp

variable {K : Type*} [Field K] {r : ℕ}

@[expose] def offGen (ψ : K → K) (i j : Fin r) (x : K) : Matrix (Fin r) (Fin r) K :=
  Matrix.single i j x + Matrix.single j i (ψ x)

@[expose] def triTerm (ψ : K → K) (B : Matrix (Fin r) (Fin r) K) (ij : Fin r × Fin r) :
    Matrix (Fin r) (Fin r) K :=
  if ij.1 < ij.2 then offGen ψ ij.1 ij.2 (B ij.1 ij.2)
  else if ij.1 = ij.2 then Matrix.single ij.1 ij.1 (B ij.1 ij.1) else 0

theorem sum_triTerm (ψ : K → K) {B : Matrix (Fin r) (Fin r) K}
    (hB : ∀ i j, i < j → B j i = ψ (B i j)) : ∑ ij, triTerm ψ B ij = B := by
  ext k l
  rw [Matrix.sum_apply]
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [Fintype.sum_eq_single (k, l)]
    · simp [triTerm, hkl, offGen, hkl.ne']
    · rintro ⟨i, j⟩ hij
      simp only [triTerm, offGen]
      split_ifs with h1 h2
      · simp only [Matrix.add_apply, Matrix.single_apply]
        split_ifs with h3 h4 h4
        · exact absurd (Prod.ext h3.1 h3.2) hij
        · exact absurd (Prod.ext h3.1 h3.2) hij
        · exact absurd (h4.2 ▸ h4.1 ▸ h1) (lt_asymm hkl)
        · simp
      · simp only [Matrix.single_apply]
        split_ifs with h3
        · exact absurd (h3.1.symm.trans h3.2) hkl.ne
        · rfl
      · rfl
  · rw [Fintype.sum_eq_single (k, k)]
    · simp [triTerm]
    · rintro ⟨i, j⟩ hij
      simp only [triTerm, offGen]
      split_ifs with h1 h2
      · simp only [Matrix.add_apply, Matrix.single_apply]
        split_ifs with h3 h4 h4
        · exact absurd (h3.1 ▸ h3.2 ▸ h1) (lt_irrefl _)
        · exact absurd (h3.1 ▸ h3.2 ▸ h1) (lt_irrefl _)
        · exact absurd (h4.1 ▸ h4.2 ▸ h1) (lt_irrefl _)
        · simp
      · simp only [Matrix.single_apply]
        split_ifs with h3
        · exact absurd (Prod.ext h3.1 (h2 ▸ h3.1)) hij
        · rfl
      · rfl
  · rw [Fintype.sum_eq_single (l, k)]
    · simp [triTerm, hkl, offGen, hkl.ne', hB l k hkl]
    · rintro ⟨i, j⟩ hij
      simp only [triTerm, offGen]
      split_ifs with h1 h2
      · simp only [Matrix.add_apply, Matrix.single_apply]
        split_ifs with h3 h4 h4
        · exact absurd (h3.2 ▸ h3.1 ▸ h1) (lt_asymm hkl)
        · exact absurd (h3.2 ▸ h3.1 ▸ h1) (lt_asymm hkl)
        · exact absurd (Prod.ext h4.2 h4.1) hij
        · simp
      · simp only [Matrix.single_apply]
        split_ifs with h3
        · exact absurd (h3.1.symm.trans h3.2) hkl.ne'
        · rfl
      · rfl

theorem diagonal_mul_single' (d : Fin r → K) (i j : Fin r) (c : K) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · rw [h.1]
  · simp

theorem single_mul_diagonal' (d : Fin r → K) (i j : Fin r) (c : K) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · rw [h.2]
  · simp

theorem diagonal_mul_offGen_mul_diagonal (ψ : K → K) (a : Fin r → K) (i j : Fin r) (x : K)
    (hψ : ψ (a i * a j * x) = a i * a j * ψ x) :
    Matrix.diagonal a * offGen ψ i j x * Matrix.diagonal a = offGen ψ i j (a i * a j * x) := by
  rw [offGen, offGen, Matrix.mul_add, Matrix.add_mul, diagonal_mul_single',
    diagonal_mul_single', single_mul_diagonal', single_mul_diagonal', hψ]
  congr 1 <;> congr 1 <;> ring

theorem diagonal_mul_single_mul_diagonal (a : Fin r → K) (i : Fin r) (x : K) :
    Matrix.diagonal a * Matrix.single i i x * Matrix.diagonal a =
      Matrix.single i i (a i ^ 2 * x) := by
  rw [diagonal_mul_single', single_mul_diagonal']
  congr 1
  ring

end Decomp

section Generic

variable {K : Type*} [Field K] {r : ℕ}

theorem update_one_apply (m : Fin r) (c : K) (i : Fin r) :
    Function.update (1 : Fin r → K) m c i = if i = m then c else 1 := by
  rw [Function.update_apply]
  rfl

theorem psi_intCast_mul (ψ : K →+ K) (z : ℤ) (x : K) : ψ ((z : K) * x) = (z : K) * ψ x := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem offGen_mul (ψ : K →+ K) (i j : Fin r) (σ x : K) (hσ : ψ (σ * x) = σ * ψ x) :
    offGen ψ i j (σ * x) = σ • offGen ψ i j x := by
  rw [offGen, offGen, hσ, smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul,
    smul_eq_mul]

theorem neg_one_eq_natCast {p : ℕ} [hp : Fact p.Prime] [CharP K p] :
    (-1 : K) = ((p - 1 : ℕ) : K) := by
  rw [Nat.cast_sub hp.out.one_le, CharP.cast_eq_zero, Nat.cast_one, zero_sub]

variable {Y X : Type*} [Group Y] [Group X] {φ : Y →* X}

theorem liftPair_eq_one_of_diag_weight {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y)
    {V : AddSubgroup (Matrix (Fin r) (Fin r) K)} (ρ : Multiplicative V →* X)
    {d : Fin r → K} {g : X}
    (hg : ∀ v w : V, (w : Matrix (Fin r) (Fin r) K) =
      Matrix.diagonal d * (v : Matrix (Fin r) (Fin r) K) * Matrix.diagonal d →
      g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd w))
    {u w : V} {s t : ℕ}
    (hu : Matrix.diagonal d * (u : Matrix (Fin r) (Fin r) K) * Matrix.diagonal d =
      (s : K) • (u : Matrix (Fin r) (Fin r) K))
    (hw : Matrix.diagonal d * (w : Matrix (Fin r) (Fin r) K) * Matrix.diagonal d =
      (t : K) • (w : Matrix (Fin r) (Fin r) K))
    (hst : 1 ≤ s * t) (hcop : ¬ p ∣ s * t - 1) : liftPair hφ ρ u w = 1 := by
  have hpu : p • u = 0 := Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul K,
      CharP.cast_eq_zero, zero_smul])
  refine liftPair_eq_one_of_weight hφ ρ hZ hp.out hpu hst hcop ?_
  refine liftPair_conj' hφ ρ hZ g (hg u (s • u) ?_) (hg w (t • w) ?_)
  · rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul K, hu]
  · rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul K, hw]

theorem diag_offGen_diag (ψ : K →+ K) (m : Fin r) (z : ℤ) (i j : Fin r) (x : K) :
    Matrix.diagonal (Function.update (1 : Fin r → K) m (z : K)) * offGen ψ i j x *
        Matrix.diagonal (Function.update (1 : Fin r → K) m (z : K)) =
      (Function.update (1 : Fin r → K) m (z : K) i *
        Function.update (1 : Fin r → K) m (z : K) j) • offGen ψ i j x := by
  have hint : ∃ w : ℤ, Function.update (1 : Fin r → K) m (z : K) i *
      Function.update (1 : Fin r → K) m (z : K) j = (w : K) := by
    simp only [update_one_apply]
    split_ifs
    · exact ⟨z * z, by push_cast; ring⟩
    · exact ⟨z, by ring⟩
    · exact ⟨z, by ring⟩
    · exact ⟨1, by push_cast; ring⟩
  obtain ⟨w, hw⟩ := hint
  rw [diagonal_mul_offGen_mul_diagonal ψ _ i j x (by rw [hw]; exact psi_intCast_mul ψ w x), hw,
    offGen_mul ψ i j _ x (psi_intCast_mul ψ w x)]

theorem diag_single_diag (m : Fin r) (c : K) (i : Fin r) (x : K) :
    Matrix.diagonal (Function.update (1 : Fin r → K) m c) * Matrix.single i i x *
        Matrix.diagonal (Function.update (1 : Fin r → K) m c) =
      (Function.update (1 : Fin r → K) m c i ^ 2) • Matrix.single i i x := by
  rw [diagonal_mul_single_mul_diagonal, Matrix.smul_single, smul_eq_mul]

theorem radical_liftPair_eq_one {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y)
    (V : AddSubgroup (Matrix (Fin r) (Fin r) K)) (ρ : Multiplicative V →* X) (ψ : K →+ K)
    (hoff : ∀ i j : Fin r, i < j → ∀ x, offGen ψ i j x ∈ V)
    (hdiag : ∀ v : V, ∀ i, Matrix.single i i ((v : Matrix (Fin r) (Fin r) K) i i) ∈ V)
    (hsymm : ∀ v : V, ∀ i j, i < j →
      (v : Matrix (Fin r) (Fin r) K) j i = ψ ((v : Matrix (Fin r) (Fin r) K) i j))
    (htorus : ∀ (m : Fin r) (c : K), (c = 2 ∨ c = -1) → ∃ g : X, ∀ v w : V,
      (w : Matrix (Fin r) (Fin r) K) = Matrix.diagonal (Function.update (1 : Fin r → K) m c) *
        (v : Matrix (Fin r) (Fin r) K) * Matrix.diagonal (Function.update (1 : Fin r → K) m c) →
      g * ρ (Multiplicative.ofAdd v) * g⁻¹ = ρ (Multiplicative.ofAdd w))
    (hsq : ∀ (i : Fin r) (v w : V),
      liftPair hφ ρ ⟨Matrix.single i i ((v : Matrix (Fin r) (Fin r) K) i i), hdiag v i⟩
        ⟨Matrix.single i i ((w : Matrix (Fin r) (Fin r) K) i i), hdiag w i⟩ = 1)
    (v w : V) : liftPair hφ ρ v w = 1 := by
  have hp2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcop1 : ¬ p ∣ (p - 1) * 1 - 1 := by
    rw [mul_one]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcop1' : ¬ p ∣ 1 * (p - 1) - 1 := by rw [one_mul]; rw [mul_one] at hcop1; exact hcop1
  have hcop2 : ¬ p ∣ 2 * 2 - 1 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hcop4 : ¬ p ∣ 4 * 1 - 1 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hm1 : (-1 : K) = ((-1 : ℤ) : K) := by push_cast; ring
  have h2 : (2 : K) = ((2 : ℤ) : K) := by push_cast; ring
  have hmem : ∀ (u : V) (ij : Fin r × Fin r), triTerm ψ u ij ∈ V := by
    intro u ij
    unfold triTerm
    split_ifs with h1 h2
    · exact hoff _ _ h1 _
    · exact hdiag u ij.1
    · exact V.zero_mem
  let gen : V → Fin r × Fin r → V := fun u ij => ⟨triTerm ψ u ij, hmem u ij⟩
  have hsum : ∀ u : V, u = ∑ ij, gen u ij := fun u => Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_triTerm ψ (hsymm u)).symm)
  have hoffoff : ∀ (i j k l : Fin r) (hij : i < j) (hkl : k < l) (x y : K),
      liftPair hφ ρ ⟨offGen ψ i j x, hoff i j hij x⟩ ⟨offGen ψ k l y, hoff k l hkl y⟩ = 1 := by
    intro i j k l hij hkl x y
    by_cases hsame : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := hsame
      obtain ⟨g, hg⟩ := htorus i 2 (Or.inl rfl)
      refine liftPair_eq_one_of_diag_weight hφ hZ ρ hg (s := 2) (t := 2) ?_ ?_ (by norm_num)
        hcop2
      · rw [h2, diag_offGen_diag, update_one_apply, update_one_apply, ite_eq_left rfl,
          ite_eq_right hij.ne', ← h2]
        norm_num
      · rw [h2, diag_offGen_diag, update_one_apply, update_one_apply, ite_eq_left rfl,
          ite_eq_right hij.ne', ← h2]
        norm_num
    ·
      have hcase : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) := by
        by_contra hno
        apply hsame
        have hi : i = k ∨ i = l := by
          by_contra h
          push Not at h
          exact hno (Or.inl h)
        have hj : j = k ∨ j = l := by
          by_contra h
          push Not at h
          exact hno (Or.inr h)
        rcases hi with rfl | rfl
        · rcases hj with rfl | rfl
          · exact absurd hij (lt_irrefl _)
          · exact ⟨rfl, rfl⟩
        · rcases hj with rfl | rfl
          · exact absurd hij (lt_asymm hkl)
          · exact absurd hij (lt_irrefl _)
      rcases hcase with ⟨hik, hil⟩ | ⟨hjk, hjl⟩
      · obtain ⟨g, hg⟩ := htorus i (-1) (Or.inr rfl)
        refine liftPair_eq_one_of_diag_weight hφ hZ ρ hg (s := p - 1) (t := 1) ?_ ?_
          (by rw [mul_one]; omega) hcop1
        · rw [hm1, diag_offGen_diag, update_one_apply, update_one_apply, ← hm1, ite_eq_left rfl,
            ite_eq_right hij.ne', mul_one, ← neg_one_eq_natCast]
        · rw [hm1, diag_offGen_diag, update_one_apply, update_one_apply, ← hm1,
            ite_eq_right (Ne.symm hik), ite_eq_right (Ne.symm hil), mul_one, Nat.cast_one]
      · obtain ⟨g, hg⟩ := htorus j (-1) (Or.inr rfl)
        refine liftPair_eq_one_of_diag_weight hφ hZ ρ hg (s := p - 1) (t := 1) ?_ ?_
          (by rw [mul_one]; omega) hcop1
        · rw [hm1, diag_offGen_diag, update_one_apply, update_one_apply, ← hm1, ite_eq_right hij.ne,
            ite_eq_left rfl, one_mul, ← neg_one_eq_natCast]
        · rw [hm1, diag_offGen_diag, update_one_apply, update_one_apply, ← hm1,
            ite_eq_right (Ne.symm hjk), ite_eq_right (Ne.symm hjl), mul_one, Nat.cast_one]
  have hoffdiag : ∀ (i j k : Fin r) (hij : i < j) (x : K) (u : V),
      liftPair hφ ρ ⟨offGen ψ i j x, hoff i j hij x⟩ ⟨Matrix.single k k
        ((u : Matrix (Fin r) (Fin r) K) k k), hdiag u k⟩ = 1 ∧
      liftPair hφ ρ ⟨Matrix.single k k ((u : Matrix (Fin r) (Fin r) K) k k), hdiag u k⟩
        ⟨offGen ψ i j x, hoff i j hij x⟩ = 1 := by
    intro i j k hij x u
    obtain ⟨g, hg⟩ := htorus i (-1) (Or.inr rfl)
    have hoffw : Matrix.diagonal (Function.update (1 : Fin r → K) i (-1)) * offGen ψ i j x *
        Matrix.diagonal (Function.update (1 : Fin r → K) i (-1)) =
          ((p - 1 : ℕ) : K) • offGen ψ i j x := by
      rw [hm1, diag_offGen_diag, update_one_apply, update_one_apply, ← hm1, ite_eq_left rfl,
        ite_eq_right hij.ne', mul_one, ← neg_one_eq_natCast]
    have hdiagw : Matrix.diagonal (Function.update (1 : Fin r → K) i (-1)) *
        Matrix.single k k ((u : Matrix (Fin r) (Fin r) K) k k) *
        Matrix.diagonal (Function.update (1 : Fin r → K) i (-1)) =
          ((1 : ℕ) : K) • Matrix.single k k ((u : Matrix (Fin r) (Fin r) K) k k) := by
      rw [diag_single_diag, update_one_apply]
      split_ifs <;> norm_num
    exact ⟨liftPair_eq_one_of_diag_weight hφ hZ ρ hg hoffw hdiagw (by rw [mul_one]; omega)
        hcop1,
      liftPair_eq_one_of_diag_weight hφ hZ ρ hg hdiagw hoffw (by rw [one_mul]; omega) hcop1'⟩
  have hdiagdiag : ∀ i k : Fin r, i ≠ k → ∀ u u' : V,
      liftPair hφ ρ ⟨Matrix.single i i ((u : Matrix (Fin r) (Fin r) K) i i), hdiag u i⟩
        ⟨Matrix.single k k ((u' : Matrix (Fin r) (Fin r) K) k k), hdiag u' k⟩ = 1 := by
    intro i k hik u u'
    obtain ⟨g, hg⟩ := htorus i 2 (Or.inl rfl)
    refine liftPair_eq_one_of_diag_weight hφ hZ ρ hg (s := 4) (t := 1) ?_ ?_ (by norm_num)
      hcop4
    · rw [diag_single_diag, update_one_apply, ite_eq_left rfl]
      norm_num
    · rw [diag_single_diag, update_one_apply, ite_eq_right (Ne.symm hik)]
      norm_num
  rw [hsum v, hsum w]
  refine liftPair_eq_one_of_sum hφ ρ hZ _ _ _ _ fun ij _ kl _ => ?_
  obtain ⟨i, j⟩ := ij
  obtain ⟨k, l⟩ := kl
  have hgen : ∀ (u : V) (a b : Fin r), (∃ hab : a < b, gen u (a, b) =
      ⟨offGen ψ a b ((u : Matrix (Fin r) (Fin r) K) a b), hoff a b hab _⟩) ∨
      (a = b ∧ gen u (a, b) = ⟨Matrix.single a a ((u : Matrix (Fin r) (Fin r) K) a a),
        hdiag u a⟩) ∨ gen u (a, b) = 0 := by
    intro u a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact Or.inl ⟨hab, Subtype.ext (by simp [gen, triTerm, hab])⟩
    · exact Or.inr (Or.inl ⟨rfl, Subtype.ext (by simp [gen, triTerm])⟩)
    · exact Or.inr (Or.inr (Subtype.ext (by
        simp [gen, triTerm, not_lt.mpr hab.le, hab.ne'])))
  rcases hgen v i j with ⟨hij, hv⟩ | ⟨rfl, hv⟩ | hv <;>
    rcases hgen w k l with ⟨hkl, hw⟩ | ⟨rfl, hw⟩ | hw
  · rw [hv, hw]
    exact hoffoff i j k l hij hkl _ _
  · rw [hv, hw]
    exact (hoffdiag i j k hij _ w).1
  · rw [hw, liftPair_zero_right hφ ρ hZ]
  · rw [hv, hw]
    exact (hoffdiag k l i hkl _ v).2
  · rw [hv, hw]
    by_cases hik : i = k
    · subst hik
      exact hsq i v w
    · exact hdiagdiag i k hik v w
  · rw [hw, liftPair_zero_right hφ ρ hZ]
  all_goals rw [hv, liftPair_zero_left hφ ρ hZ]

end Generic

@[expose] def ltPairsEquiv (r : ℕ) : {ij : Fin r × Fin r // ij.1 < ij.2} ≃ Σ j : Fin r, Fin j where
  toFun ij := ⟨ij.1.2, ⟨ij.1.1.val, ij.2⟩⟩
  invFun jk := ⟨(⟨jk.2.val, jk.2.isLt.trans jk.1.isLt⟩, jk.1), jk.2.isLt⟩
  left_inv ij := by
    obtain ⟨⟨i, j⟩, h⟩ := ij
    rfl
  right_inv jk := by
    obtain ⟨j, k⟩ := jk
    rfl

theorem card_ltPairs (r : ℕ) :
    Fintype.card {ij : Fin r × Fin r // ij.1 < ij.2} = r * (r - 1) / 2 := by
  rw [Fintype.card_congr (ltPairsEquiv r), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) r, Finset.sum_range_id]

section Siegel

variable {F : Type*} [Field F] {r : ℕ}

@[expose] def siegelMat (B : Matrix (Fin r) (Fin r) F) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
  Matrix.fromBlocks 1 B 0 1

theorem siegelMat_mul (B B' : Matrix (Fin r) (Fin r) F) :
    siegelMat B * siegelMat B' = siegelMat (B + B') := by
  rw [siegelMat, siegelMat, siegelMat, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem siegelMat_zero : siegelMat (0 : Matrix (Fin r) (Fin r) F) = 1 :=
  Matrix.fromBlocks_one

theorem siegelMat_injective : Function.Injective (siegelMat (F := F) (r := r)) := by
  intro B B' h
  have := congrArg Matrix.toBlocks₁₂ h
  simpa [siegelMat] using this

@[expose] def siegelGL (B : Matrix (Fin r) (Fin r) F) : GL (Fin r ⊕ Fin r) F :=
  ⟨siegelMat B, siegelMat (-B), by rw [siegelMat_mul, add_neg_cancel, siegelMat_zero],
    by rw [siegelMat_mul, neg_add_cancel, siegelMat_zero]⟩

theorem coe_siegelGL (B : Matrix (Fin r) (Fin r) F) :
    (siegelGL B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = siegelMat B :=
  rfl

theorem siegelGL_add (B B' : Matrix (Fin r) (Fin r) F) :
    siegelGL (B + B') = siegelGL B * siegelGL B' :=
  Units.ext (siegelMat_mul B B').symm

theorem siegelGL_zero : siegelGL (0 : Matrix (Fin r) (Fin r) F) = 1 :=
  Units.ext siegelMat_zero

@[expose] def torusGL (a : Fin r → Fˣ) : GL (Fin r ⊕ Fin r) F :=
  ⟨Matrix.fromBlocks (Matrix.diagonal fun i => (a i : F)) 0 0
      (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)),
    Matrix.fromBlocks (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) 0 0
      (Matrix.diagonal fun i => (a i : F)),
    by
      rw [Matrix.fromBlocks_multiply]
      simp [Matrix.diagonal_mul_diagonal, ← Matrix.fromBlocks_one],
    by
      rw [Matrix.fromBlocks_multiply]
      simp [Matrix.diagonal_mul_diagonal, ← Matrix.fromBlocks_one]⟩

theorem coe_torusGL (a : Fin r → Fˣ) :
    (torusGL a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      Matrix.fromBlocks (Matrix.diagonal fun i => (a i : F)) 0 0
        (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) :=
  rfl

theorem coe_torusGL_inv (a : Fin r → Fˣ) :
    (↑(torusGL a)⁻¹ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      Matrix.fromBlocks (Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)) 0 0
        (Matrix.diagonal fun i => (a i : F)) :=
  rfl

theorem torusGL_conj_siegelGL (a : Fin r → Fˣ) (B : Matrix (Fin r) (Fin r) F) :
    torusGL a * siegelGL B * (torusGL a)⁻¹ =
      siegelGL (Matrix.diagonal (fun i => (a i : F)) * B * Matrix.diagonal fun i => (a i : F)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_torusGL, coe_torusGL_inv, coe_siegelGL, coe_siegelGL,
    siegelMat, siegelMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]

@[expose] noncomputable def updateUnits (m : Fin r) {c : F} (hc : c ≠ 0) : Fin r → Fˣ :=
  Function.update 1 m (Units.mk0 c hc)

theorem coe_updateUnits (m : Fin r) {c : F} (hc : c ≠ 0) :
    (fun i => ((updateUnits m hc i : Fˣ) : F)) = Function.update (1 : Fin r → F) m c := by
  funext i
  rw [updateUnits, update_one_apply, Function.update_apply]
  split_ifs <;> rfl

end Siegel

section Count

variable {F : Type*} [Field F] {r : ℕ}

@[expose] def symMatrices (r : ℕ) (F : Type*) [Field F] :
    AddSubgroup (Matrix (Fin r) (Fin r) F) where
  carrier := {B | Bᵀ = B}
  add_mem' {a b} ha hb := by
    change (a + b)ᵀ = a + b
    rw [Matrix.transpose_add, ha, hb]
  zero_mem' := Matrix.transpose_zero
  neg_mem' {a} ha := by
    change (-a)ᵀ = -a
    rw [Matrix.transpose_neg, ha]

theorem mem_symMatrices {B : Matrix (Fin r) (Fin r) F} : B ∈ symMatrices r F ↔ Bᵀ = B :=
  Iff.rfl

@[expose] def symMatricesEquiv : symMatrices r F ≃
    (Fin r → F) × ({ij : Fin r × Fin r // ij.1 < ij.2} → F) where
  toFun B := (fun i => (B : Matrix (Fin r) (Fin r) F) i i,
    fun ij => (B : Matrix (Fin r) (Fin r) F) ij.1.1 ij.1.2)
  invFun du := ⟨Matrix.of fun k l => if h1 : k = l then du.1 k
      else if h2 : k < l then du.2 ⟨(k, l), h2⟩
      else du.2 ⟨(l, k), lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)⟩, by
    ext k l
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    by_cases h1 : k = l
    · subst h1
      simp
    · rw [dite_eq_right (Ne.symm h1), dite_eq_right h1]
      by_cases h2 : k < l
      · rw [dite_eq_right (not_lt.mpr h2.le), dite_eq_left h2]
      · rw [dite_eq_left (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)), dite_eq_right h2]⟩
  left_inv B := by
    apply Subtype.ext
    ext k l
    simp only [Matrix.of_apply]
    by_cases h1 : k = l
    · subst h1
      simp
    · rw [dite_eq_right h1]
      by_cases h2 : k < l
      · rw [dite_eq_left h2]
      · rw [dite_eq_right h2]
        exact congrFun (congrFun B.2 k) l
  right_inv du := by
    obtain ⟨d, u⟩ := du
    refine Prod.ext (funext fun i => ?_) (funext fun ij => ?_)
    · simp [Matrix.of_apply]
    · obtain ⟨⟨k, l⟩, h⟩ := ij
      simp [Matrix.of_apply, h.ne, h]

theorem card_symMatrices [Finite F] :
    Nat.card (symMatrices r F) = Nat.card F ^ (r * (r + 1) / 2) := by
  rw [Nat.card_congr symMatricesEquiv, Nat.card_prod, Nat.card_fun, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := {ij : Fin r × Fin r // ij.1 < ij.2}), card_ltPairs, ← pow_add]
  congr 1
  rcases r with _ | r
  · rfl
  · have h : (r + 1) * (r + 1 + 1) = (r + 1) * r + 2 * (r + 1) := by ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num), Nat.add_sub_cancel, add_comm]

end Count

theorem isElemAbelian_range {V G : Type*} [AddCommGroup V] [Group G] {p : ℕ}
    (hV : ∀ v : V, p • v = 0) (ρ : Multiplicative V →* G) : IsElemAbelian p ρ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow]
    have : v ^ p = 1 := by
      change Multiplicative.ofAdd (p • v.toAdd) = 1
      rw [hV]
      rfl
    rw [this, map_one]

theorem nsmul_char_eq_zero {K : Type*} [Field K] {p : ℕ} [CharP K p] {r : ℕ}
    (V : AddSubgroup (Matrix (Fin r) (Fin r) K)) (v : V) : p • v = 0 :=
  Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul K,
      CharP.cast_eq_zero, zero_smul])

section Symplectic

variable {F : Type} [Field F] {r : ℕ}

theorem siegelGL_mem_statedSp {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) :
    siegelGL B ∈ StatedSp r F := by
  refine Subgroup.subset_closure ?_
  change (siegelMat B)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * siegelMat B =
    Matrix.fromBlocks 0 1 (-1) 0
  rw [siegelMat, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, hB]
  simp

theorem torusGL_mem_statedSp (a : Fin r → Fˣ) : torusGL a ∈ StatedSp r F := by
  refine Subgroup.subset_closure ?_
  change (torusGL a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    (torusGL a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = Matrix.fromBlocks 0 1 (-1) 0
  rw [coe_torusGL, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]

@[expose] def siegelSpHom (r : ℕ) (F : Type) [Field F] :
    Multiplicative (symMatrices r F) →* StatedSp r F where
  toFun B := ⟨siegelGL (B.toAdd : Matrix (Fin r) (Fin r) F), siegelGL_mem_statedSp B.toAdd.2⟩
  map_one' := Subtype.ext siegelGL_zero
  map_mul' _ _ := Subtype.ext (siegelGL_add _ _)

theorem siegelSpHom_injective : Function.Injective (siegelSpHom r F) := by
  intro B B' h
  have := congrArg (fun g : StatedSp r F => ((g : GL (Fin r ⊕ Fin r) F) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h
  exact Multiplicative.toAdd.injective (Subtype.ext (siegelMat_injective this))

@[expose] def siegelRadicalSp (r : ℕ) (F : Type) [Field F] : Subgroup (StatedSp r F) :=
  (siegelSpHom r F).range

theorem mem_siegelRadicalSp {g : StatedSp r F} : g ∈ siegelRadicalSp r F ↔
    ∃ B : Matrix (Fin r) (Fin r) F, Bᵀ = B ∧
      ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        Matrix.fromBlocks 1 B 0 1 := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.toAdd, B.toAdd.2, rfl⟩
  · rintro ⟨B, hB, hg⟩
    exact ⟨Multiplicative.ofAdd ⟨B, hB⟩, Subtype.ext (Units.ext hg.symm)⟩

theorem siegel_radical_sp {p f : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (r : ℕ) :
    IsElemAbelian p (siegelRadicalSp r F) ∧
      Nat.card (siegelRadicalSp r F) = (p ^ f) ^ (r * (r + 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  refine ⟨isElemAbelian_range (nsmul_char_eq_zero _) _, ?_⟩
  rw [siegelRadicalSp, MonoidHom.range_eq_map, Subgroup.card_map_of_injective siegelSpHom_injective,
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, card_symMatrices, hF]

theorem siegel_radical_sp_preimage_comm {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = p ^ f) (r : ℕ) {E : Type*} [Group E]
    (π : E →* StatedSp r F) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center E) :
    ∀ x ∈ (siegelRadicalSp r F).comap π, ∀ y ∈ (siegelRadicalSp r F).comap π,
      x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hp2 : p ≠ 2 := by omega
  have h9 : p ^ f ≠ 9 := by
    intro h
    have h3 : p ∣ 9 := h ▸ dvd_pow_self p (by rintro rfl; simp at h)
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h3))
    omega
  set ρ := siegelSpHom r F
  have hdiagmem : ∀ (i : Fin r) (x : F), Matrix.single i i x ∈ symMatrices r F := fun i x => by
    rw [mem_symMatrices, Matrix.transpose_single]
  have hg : ∀ (a : Fin r → Fˣ) (v w : symMatrices r F), (w : Matrix (Fin r) (Fin r) F) =
      Matrix.diagonal (fun i => (a i : F)) * (v : Matrix (Fin r) (Fin r) F) *
        Matrix.diagonal (fun i => (a i : F)) →
      (⟨torusGL a, torusGL_mem_statedSp a⟩ : StatedSp r F) * ρ (Multiplicative.ofAdd v) *
        (⟨torusGL a, torusGL_mem_statedSp a⟩ : StatedSp r F)⁻¹ = ρ (Multiplicative.ofAdd w) := by
    intro a v w hw
    apply Subtype.ext
    change torusGL a * siegelGL (v : Matrix (Fin r) (Fin r) F) * (torusGL a)⁻¹ =
      siegelGL (w : Matrix (Fin r) (Fin r) F)
    rw [torusGL_conj_siegelGL, hw]
  have hsq : ∀ (i : Fin r) (v w : symMatrices r F),
      liftPair hπ ρ ⟨Matrix.single i i ((v : Matrix (Fin r) (Fin r) F) i i), hdiagmem i _⟩
        ⟨Matrix.single i i ((w : Matrix (Fin r) (Fin r) F) i i), hdiagmem i _⟩ = 1 := by
    intro i v w
    let _ := centerCommGroup E
    let δ : F → symMatrices r F := fun x => ⟨Matrix.single i i x, hdiagmem i x⟩
    have hδ : ∀ x x', δ (x + x') = δ x + δ x' := fun x x' =>
      Subtype.ext (Matrix.single_add i i x x')
    let b : F → F → Additive (Subgroup.center E) := fun x y => liftPairAdd hπ ρ hZ (δ x) (δ y)
    have hb := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero hp2 hF b
      (fun x x' y => by simp only [b, hδ, liftPairAdd_add_left])
      (fun x y y' => by simp only [b, hδ, liftPairAdd_add_right])
      (fun x => liftPairAdd_self hπ ρ hZ (δ x))
      (fun c hc x y => by
        refine liftPairAdd_congr hπ ρ hZ (liftPair_conj' hπ ρ hZ _
          (hg (updateUnits i hc) (δ x) (δ (c ^ 2 * x)) ?_)
          (hg (updateUnits i hc) (δ y) (δ (c ^ 2 * y)) ?_))
        · rw [coe_updateUnits, diag_single_diag, update_one_apply, ite_eq_left rfl,
            Matrix.smul_single, smul_eq_mul]
        · rw [coe_updateUnits, diag_single_diag, update_one_apply, ite_eq_left rfl,
            Matrix.smul_single, smul_eq_mul])
      h9 ((v : Matrix (Fin r) (Fin r) F) i i) ((w : Matrix (Fin r) (Fin r) F) i i)
    exact (liftPairAdd_eq_zero_iff hπ ρ hZ _ _).mp hb
  have hvanish := radical_liftPair_eq_one hp3 hπ hZ (symMatrices r F) ρ (AddMonoidHom.id F)
    (fun i j _ x => by
      rw [mem_symMatrices, offGen, Matrix.transpose_add, Matrix.transpose_single,
        Matrix.transpose_single, add_comm]
      rfl)
    (fun v i => hdiagmem i _)
    (fun v i j _ => by
      rw [AddMonoidHom.id_apply]
      exact congrFun (congrFun v.2 i) j)
    (fun m c hc => by
      have hc0 : c ≠ 0 := by
        rcases hc with rfl | rfl
        · intro h
          have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
          have := Nat.le_of_dvd (by norm_num) this
          omega
        · exact neg_ne_zero.mpr one_ne_zero
      refine ⟨_, fun v w hw => hg (updateUnits m hc0) v w ?_⟩
      rw [coe_updateUnits]
      exact hw)
    hsq
  intro x hx y hy
  exact mul_comm_of_liftPair_eq_one hπ ρ hZ hvanish hx hy

end Symplectic

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {r : ℕ}

@[expose] def skewHermMatrices (h : UnitaryFieldData p f K) (r : ℕ) :
    AddSubgroup (Matrix (Fin r) (Fin r) K) where
  carrier := {B | B + (B.map h.bar)ᵀ = 0}
  add_mem' {a b} ha hb := by
    change a + b + ((a + b).map h.bar)ᵀ = 0
    rw [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add]
    change a + (a.map h.bar)ᵀ = 0 at ha
    change b + (b.map h.bar)ᵀ = 0 at hb
    rw [show a + b + ((a.map h.bar)ᵀ + (b.map h.bar)ᵀ) =
      (a + (a.map h.bar)ᵀ) + (b + (b.map h.bar)ᵀ) by abel, ha, hb, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin r) (Fin r) K) + ((0 : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 0
    simp
  neg_mem' {a} ha := by
    change -a + ((-a).map h.bar)ᵀ = 0
    change a + (a.map h.bar)ᵀ = 0 at ha
    rw [Matrix.map_neg _ (map_neg h.bar), Matrix.transpose_neg, ← neg_add, ha, neg_zero]

theorem mem_skewHermMatrices_iff (h : UnitaryFieldData p f K) {B : Matrix (Fin r) (Fin r) K} :
    B ∈ skewHermMatrices h r ↔ ∀ k l, B k l + h.bar (B l k) = 0 := by
  change B + (B.map h.bar)ᵀ = 0 ↔ _
  constructor
  · intro hB k l
    have := congrFun (congrFun hB k) l
    simpa using this
  · intro hB
    ext k l
    simpa using hB k l

@[expose] noncomputable def skewHermMatricesEquiv (h : UnitaryFieldData p f K) :
    skewHermMatrices h r ≃ (Fin r → h.traceZero) × ({ij : Fin r × Fin r // ij.1 < ij.2} → K) where
  toFun B := (fun i => ⟨(B : Matrix (Fin r) (Fin r) K) i i, by
      have := (mem_skewHermMatrices_iff h).mp B.2 i i
      exact (h.mem_traceZero).mpr this⟩,
    fun ij => (B : Matrix (Fin r) (Fin r) K) ij.1.1 ij.1.2)
  invFun du := ⟨Matrix.of fun k l => if h1 : k = l then (du.1 k : K)
      else if h2 : k < l then du.2 ⟨(k, l), h2⟩
      else -h.bar (du.2 ⟨(l, k), lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)⟩), by
    rw [mem_skewHermMatrices_iff]
    intro k l
    simp only [Matrix.of_apply]
    by_cases h1 : k = l
    · subst h1
      simp only [dite_true]
      exact (h.mem_traceZero).mp (du.1 k).2
    · rw [dite_eq_right h1, dite_eq_right (Ne.symm h1)]
      by_cases h2 : k < l
      · rw [dite_eq_left h2, dite_eq_right (not_lt.mpr h2.le), map_neg, h.bar_bar, add_neg_cancel]
      · rw [dite_eq_right h2, dite_eq_left (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)),
          neg_add_cancel]⟩
  left_inv B := by
    apply Subtype.ext
    ext k l
    simp only [Matrix.of_apply]
    by_cases h1 : k = l
    · subst h1
      simp
    · rw [dite_eq_right h1]
      by_cases h2 : k < l
      · rw [dite_eq_left h2]
      · rw [dite_eq_right h2]
        have := (mem_skewHermMatrices_iff h).mp B.2 k l
        linear_combination -this
  right_inv du := by
    obtain ⟨d, u⟩ := du
    refine Prod.ext (funext fun i => ?_) (funext fun ij => ?_)
    · simp [Matrix.of_apply]
    · obtain ⟨⟨k, l⟩, hkl⟩ := ij
      simp [Matrix.of_apply, hkl.ne, hkl]

theorem card_skewHermMatrices (h : UnitaryFieldData p f K) :
    Nat.card (skewHermMatrices h r) = (p ^ f) ^ (r ^ 2) := by
  have := h.finite
  rw [Nat.card_congr (skewHermMatricesEquiv h), Nat.card_prod, Nat.card_fun, Nat.card_fun,
    h.card_traceZero, h.card_eq_sq, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := {ij : Fin r × Fin r // ij.1 < ij.2}), card_ltPairs,
    ← pow_mul (p ^ f) 2 (r * (r - 1) / 2), ← pow_add]
  congr 1
  have h2 : 2 * (r * (r - 1) / 2) = r * (r - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self r)
  rcases r with _ | r
  · rfl
  · rw [h2, Nat.add_sub_cancel]
    ring

@[expose] def hypGram2 (r : ℕ) (K : Type) [Field K] : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.fromBlocks 0 1 1 0

theorem siegelGL_mem_gramSU (h : UnitaryFieldData p f K) {B : Matrix (Fin r) (Fin r) K}
    (hB : B ∈ skewHermMatrices h r) : siegelGL B ∈ gramSU h (hypGram2 r K) := by
  refine (mem_gramSU).mpr ⟨?_, ?_⟩
  · change ((siegelMat B).map h.bar)ᵀ * Matrix.fromBlocks 0 1 1 0 * siegelMat B =
      Matrix.fromBlocks 0 1 1 0
    have hB' : B + (B.map h.bar)ᵀ = 0 := hB
    rw [siegelMat, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.map_zero _ (map_zero h.bar), Matrix.transpose_one, Matrix.transpose_zero]
    simp [add_comm, hB']
  · change (siegelMat B).det = 1
    rw [siegelMat, Matrix.det_fromBlocks_zero₂₁]
    simp

theorem torusGL_mem_gramSU (h : UnitaryFieldData p f K) {a : Fin r → Kˣ}
    (ha : ∀ i, h.bar (a i) = a i) : torusGL a ∈ gramSU h (hypGram2 r K) := by
  have ha' : ∀ i, h.bar (((a i)⁻¹ : Kˣ) : K) = (((a i)⁻¹ : Kˣ) : K) := fun i => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha]
  refine (mem_gramSU).mpr ⟨?_, ?_⟩
  · change ((torusGL a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map h.bar)ᵀ *
      Matrix.fromBlocks 0 1 1 0 * (torusGL a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.fromBlocks 0 1 1 0
    rw [coe_torusGL, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.diagonal_map (map_zero h.bar), Matrix.map_zero _ (map_zero h.bar),
      ha, ha', Matrix.diagonal_transpose, Matrix.transpose_zero]
    simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  · rw [coe_torusGL, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Matrix.det_diagonal,
      ← Finset.prod_mul_distrib]
    simp

@[expose] def siegelSUHom (h : UnitaryFieldData p f K) (r : ℕ) :
    Multiplicative (skewHermMatrices h r) →* gramSU h (hypGram2 r K) where
  toFun B := ⟨siegelGL (B.toAdd : Matrix (Fin r) (Fin r) K), siegelGL_mem_gramSU h B.toAdd.2⟩
  map_one' := Subtype.ext siegelGL_zero
  map_mul' _ _ := Subtype.ext (siegelGL_add _ _)

theorem siegelSUHom_injective (h : UnitaryFieldData p f K) :
    Function.Injective (siegelSUHom h r) := by
  intro B B' hBB'
  have := congrArg (fun g : gramSU h (hypGram2 r K) => ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hBB'
  exact Multiplicative.toAdd.injective (Subtype.ext (siegelMat_injective this))

@[expose] def siegelRadicalSU (h : UnitaryFieldData p f K) (r : ℕ) :
    Subgroup (gramSU h (hypGram2 r K)) :=
  (siegelSUHom h r).range

theorem mem_siegelRadicalSU (h : UnitaryFieldData p f K) {g : gramSU h (hypGram2 r K)} :
    g ∈ siegelRadicalSU h r ↔ ∃ B : Matrix (Fin r) (Fin r) K, B + (B.map h.bar)ᵀ = 0 ∧
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        Matrix.fromBlocks 1 B 0 1 := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.toAdd, B.toAdd.2, rfl⟩
  · rintro ⟨B, hB, hg⟩
    exact ⟨Multiplicative.ofAdd ⟨B, hB⟩, Subtype.ext (Units.ext hg.symm)⟩

theorem siegel_radical_su (h : UnitaryFieldData p f K) (r : ℕ) :
    IsElemAbelian p (siegelRadicalSU h r) ∧ Nat.card (siegelRadicalSU h r) = (p ^ f) ^ (r ^ 2) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  refine ⟨isElemAbelian_range (nsmul_char_eq_zero _) _, ?_⟩
  rw [siegelRadicalSU, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (siegelSUHom_injective h), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, card_skewHermMatrices]

theorem siegel_radical_su_preimage_comm (h : UnitaryFieldData p f K) (hp3 : 3 < p) (r : ℕ)
    {E : Type*} [Group E] (π : E →* gramSU h (hypGram2 r K)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center E) :
    ∀ x ∈ (siegelRadicalSU h r).comap π, ∀ y ∈ (siegelRadicalSU h r).comap π,
      x * y = y * x := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  have h9 : p ^ f ≠ 9 := by
    intro h9
    have h3 : p ∣ 9 := h9 ▸ dvd_pow_self p (by have := h.one_le; omega)
    have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp
      (h.prime.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h3))
    omega
  set ρ := siegelSUHom h r
  let V := skewHermMatrices h r
  have hg : ∀ (a : Fin r → Kˣ) (ha : ∀ i, h.bar (a i) = a i) (v w : V),
      (w : Matrix (Fin r) (Fin r) K) =
      Matrix.diagonal (fun i => (a i : K)) * (v : Matrix (Fin r) (Fin r) K) *
        Matrix.diagonal (fun i => (a i : K)) →
      (⟨torusGL a, torusGL_mem_gramSU h ha⟩ : gramSU h (hypGram2 r K)) *
        ρ (Multiplicative.ofAdd v) *
        (⟨torusGL a, torusGL_mem_gramSU h ha⟩ : gramSU h (hypGram2 r K))⁻¹ =
          ρ (Multiplicative.ofAdd w) := by
    intro a ha v w hw
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change torusGL a * siegelGL (v : Matrix (Fin r) (Fin r) K) * (torusGL a)⁻¹ =
      siegelGL (w : Matrix (Fin r) (Fin r) K)
    rw [torusGL_conj_siegelGL, hw]
  have hupdate : ∀ (m : Fin r) {c : K} (hc : c ≠ 0), h.bar c = c →
      ∀ i, h.bar (updateUnits m hc i) = updateUnits m hc i := by
    intro m c hc hbc i
    have := congrFun (coe_updateUnits m hc) i
    rw [this, update_one_apply]
    split_ifs
    · exact hbc
    · exact map_one h.bar
  have hdiagmem : ∀ (v : V) (i : Fin r),
      Matrix.single i i ((v : Matrix (Fin r) (Fin r) K) i i) ∈ V := by
    intro v i
    rw [mem_skewHermMatrices_iff]
    intro k l
    simp only [Matrix.single_apply]
    split_ifs with h1 h2 h2
    · exact (mem_skewHermMatrices_iff h).mp v.2 i i
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · rw [map_zero, add_zero]
  obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  have hbarτ : h.bar τ = -τ := by
    have := (h.mem_traceZero).mp hτ
    rw [UnitaryFieldData.trace] at this
    linear_combination this
  have hδmem : ∀ (i : Fin r) (x : h.fixedField), Matrix.single i i (τ * (x : K)) ∈ V := by
    intro i x
    rw [mem_skewHermMatrices_iff]
    intro k l
    simp only [Matrix.single_apply]
    split_ifs with h1 h2 h2
    · rw [map_mul, hbarτ, (h.mem_fixedField).mp x.2]
      ring
    · exact absurd ⟨h1.2, h1.1⟩ h2
    · exact absurd ⟨h2.2, h2.1⟩ h1
    · rw [map_zero, add_zero]
  have hsq : ∀ (i : Fin r) (v w : V),
      liftPair hπ ρ ⟨Matrix.single i i ((v : Matrix (Fin r) (Fin r) K) i i), hdiagmem v i⟩
        ⟨Matrix.single i i ((w : Matrix (Fin r) (Fin r) K) i i), hdiagmem w i⟩ = 1 := by
    intro i v w
    let _ := centerCommGroup E
    let δ : h.fixedField → V := fun x => ⟨Matrix.single i i (τ * (x : K)), hδmem i x⟩
    have hδ : ∀ x x', δ (x + x') = δ x + δ x' := fun x x' =>
      Subtype.ext (by
        change Matrix.single i i (τ * ((x + x' : h.fixedField) : K)) =
          Matrix.single i i (τ * (x : K)) + Matrix.single i i (τ * (x' : K))
        rw [Subfield.coe_add, mul_add, Matrix.single_add])
    let b : h.fixedField → h.fixedField → Additive (Subgroup.center E) := fun x y =>
      liftPairAdd hπ ρ hZ (δ x) (δ y)
    have hcard := h.card_fixedField
    have hdiag_eq : ∀ u : V, ∃ x : h.fixedField,
        Matrix.single i i ((u : Matrix (Fin r) (Fin r) K) i i) = Matrix.single i i (τ * x) := by
      intro u
      have hmem : (u : Matrix (Fin r) (Fin r) K) i i ∈ (h.traceZero : Set K) :=
        (h.mem_traceZero).mpr ((mem_skewHermMatrices_iff h).mp u.2 i i)
      rw [h.traceZero_eq_mul_image hτ hτ0] at hmem
      obtain ⟨x, hx, hxe⟩ := hmem
      exact ⟨⟨x, hx⟩, by rw [← hxe]⟩
    obtain ⟨x, hx⟩ := hdiag_eq v
    obtain ⟨y, hy⟩ := hdiag_eq w
    have hb := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero hp2 hcard b
      (fun x x' y => by simp only [b, hδ, liftPairAdd_add_left])
      (fun x y y' => by simp only [b, hδ, liftPairAdd_add_right])
      (fun x => liftPairAdd_self hπ ρ hZ (δ x))
      (fun c hc x y => by
        have hc' : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
        have hbc : h.bar (c : K) = c := (h.mem_fixedField).mp c.2
        refine liftPairAdd_congr hπ ρ hZ (liftPair_conj' hπ ρ hZ _
          (hg (updateUnits i hc') (hupdate i hc' hbc) (δ x) (δ (c ^ 2 * x)) ?_)
          (hg (updateUnits i hc') (hupdate i hc' hbc) (δ y) (δ (c ^ 2 * y)) ?_))
        · rw [coe_updateUnits, diag_single_diag, update_one_apply, ite_eq_left rfl,
            Matrix.smul_single, smul_eq_mul]
          change Matrix.single i i (τ * ((c ^ 2 * x : h.fixedField) : K)) = _
          push_cast
          ring_nf
        · rw [coe_updateUnits, diag_single_diag, update_one_apply, ite_eq_left rfl,
            Matrix.smul_single, smul_eq_mul]
          change Matrix.single i i (τ * ((c ^ 2 * y : h.fixedField) : K)) = _
          push_cast
          ring_nf)
      h9 x y
    have h1 : (⟨Matrix.single i i ((v : Matrix (Fin r) (Fin r) K) i i), hdiagmem v i⟩ : V) =
        δ x := Subtype.ext hx
    have h2 : (⟨Matrix.single i i ((w : Matrix (Fin r) (Fin r) K) i i), hdiagmem w i⟩ : V) =
        δ y := Subtype.ext hy
    rw [h1, h2]
    exact (liftPairAdd_eq_zero_iff hπ ρ hZ _ _).mp hb
  have hvanish := radical_liftPair_eq_one hp3 hπ hZ V ρ (-h.bar.toAddMonoidHom)
    (fun i j hij x => by
      rw [mem_skewHermMatrices_iff]
      intro k l
      have hψ : ∀ y, (-h.bar.toAddMonoidHom) y = -h.bar y := fun y => rfl
      simp only [offGen, hψ, Matrix.add_apply]
      by_cases hA : i = k ∧ j = l
      · obtain ⟨rfl, rfl⟩ := hA
        simp [hij.ne, hij.ne', h.bar_bar]
      · by_cases hB : j = k ∧ i = l
        · obtain ⟨rfl, rfl⟩ := hB
          simp [hij.ne, hij.ne']
        · have hA' : ¬ (i = l ∧ j = k) := fun h' => hB ⟨h'.2, h'.1⟩
          have hB' : ¬ (j = l ∧ i = k) := fun h' => hA ⟨h'.2, h'.1⟩
          simp [hA, hB, hA', hB'])
    hdiagmem
    (fun v i j _ => by
      have := (mem_skewHermMatrices_iff h).mp v.2 j i
      change _ = -h.bar _
      linear_combination this)
    (fun m c hc => by
      have hc0 : c ≠ 0 := by
        rcases hc with rfl | rfl
        · intro h0
          have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
          have := Nat.le_of_dvd (by norm_num) this
          omega
        · exact neg_ne_zero.mpr one_ne_zero
      have hbc : h.bar c = c := by
        rcases hc with rfl | rfl
        · rw [map_ofNat]
        · rw [map_neg, map_one]
      refine ⟨_, fun v w hw => hg (updateUnits m hc0) (hupdate m hc0 hbc) v w ?_⟩
      rw [coe_updateUnits]
      exact hw)
    hsq
  intro x hx y hy
  exact mul_comm_of_liftPair_eq_one hπ ρ hZ hvanish (Subgroup.mem_comap.mp hx)
    (Subgroup.mem_comap.mp hy)

end Unitary

end CFSG.RankThree.Classical
