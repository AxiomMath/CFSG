module

public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG Matrix
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj StatedScalars StatedClassicalModel)

section Matrices

variable {n : ℕ} {K : Type} [Field K]

theorem commute_diagGL_swap (u : Fin n → Kˣ) (i j : Fin n)
    (hu : ∀ a, u (Equiv.swap i j a) = u a) :
    Commute (diagGL n K u) (Matrix.GeneralLinearGroup.swap K i j) := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, Matrix.GeneralLinearGroup.val_swap]
  rw [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  by_cases hab : Equiv.swap i j a = b
  · subst hab
    simp [hu]
  · have h2 : a ≠ (Equiv.swap i j) b := fun h' => hab (by rw [h']; simp)
    simp [hab, h2]

theorem diagGL_unitary (q : ℕ) (hq : q ≠ 0) (u : Fin n → Kˣ) (hu : ∀ i, (u i) ^ (q + 1) = 1) :
    (((diagGL n K u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ *
      ((diagGL n K u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [coe_diagGL, Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := congrArg Units.val (hu i)
  rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one] at this
  exact this

theorem det_swap_of_charTwo [CharP K 2] {i j : Fin n} (h : i ≠ j) :
    (Matrix.swap K i j).det = 1 := by
  rw [Matrix.swap, Matrix.det_permutation, Equiv.Perm.sign_swap h]
  simp [CharTwo.neg_eq]

theorem swap_unitary (q : ℕ) (hq : q ≠ 0) (i j : Fin n) :
    ((Matrix.swap K i j).map (· ^ q))ᵀ * Matrix.swap K i j = 1 := by
  have h : ((Matrix.swap K i j).map (· ^ q)) = Matrix.swap K i j := by
    ext a b
    simp [Matrix.swap, Matrix.map_apply, PEquiv.toMatrix_apply, Equiv.Perm.permMatrix,
      apply_ite, hq]
  rw [h, Matrix.transpose_swap, Matrix.swap_mul_self]

theorem swap_not_mem_scalars {i j : Fin n} (h : i ≠ j) :
    Matrix.GeneralLinearGroup.swap K i j ∉ StatedScalars (Fin n) K := by
  rw [StatedScalars, MonoidHom.mem_range]
  rintro ⟨c, hc⟩
  have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) hc
  simp [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h] at this

end Matrices

theorem psu_torus_rank :
    ∀ (T : Type) [Group T] [Finite T] (n f p : ℕ), p.Prime → 5 ≤ p → p ∣ n → 6 ≤ n → p ∣ 2 ^ f + 1 →
      StatedClassicalModel T .PSU n 2 f → ¬ LocalRankLeTwo p T := by
  intro T _ _ n f p hp hp5 hpn hn6 hpq hmodel hloc
  obtain ⟨hadm, K, _, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hP : LocalRankLeTwo p (StatedProj (StatedSU n (2 ^ f) K)) :=
    localRankLeTwo_of_mulEquiv e hp hloc
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : 2 ^ f ≠ 0 := pow_ne_zero f two_ne_zero
  have hcardU : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have key : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [h1, h2]
      ring
    rw [key]
    exact hpq.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hcardU
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
      rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hMq : ∀ x ∈ Subgroup.zpowers ζ, x ^ (2 ^ f + 1) = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]; exact hpq))
  let j₀ : Fin n := ⟨2, by omega⟩
  let j₁ : Fin n := ⟨3, by omega⟩
  let j₂ : Fin n := ⟨4, by omega⟩
  let j₃ : Fin n := ⟨5, by omega⟩
  let s₀ : Fin n := ⟨0, by omega⟩
  let s₁ : Fin n := ⟨1, by omega⟩
  have h01 : j₀ ≠ j₁ := by simp [j₀, j₁, Fin.ext_iff]
  have h02 : j₀ ≠ j₂ := by simp [j₀, j₂, Fin.ext_iff]
  have h03 : j₀ ≠ j₃ := by simp [j₀, j₃, Fin.ext_iff]
  have h12 : j₁ ≠ j₂ := by simp [j₁, j₂, Fin.ext_iff]
  have h13 : j₁ ≠ j₃ := by simp [j₁, j₃, Fin.ext_iff]
  have h23 : j₂ ≠ j₃ := by simp [j₂, j₃, Fin.ext_iff]
  have hs0 : s₀ ≠ j₀ := by simp [s₀, j₀, Fin.ext_iff]
  have hs1 : s₀ ≠ j₁ := by simp [s₀, j₁, Fin.ext_iff]
  have hs2 : s₀ ≠ j₂ := by simp [s₀, j₂, Fin.ext_iff]
  have hs3 : s₀ ≠ j₃ := by simp [s₀, j₃, Fin.ext_iff]
  have ht0 : s₁ ≠ j₀ := by simp [s₁, j₀, Fin.ext_iff]
  have ht1 : s₁ ≠ j₁ := by simp [s₁, j₁, Fin.ext_iff]
  have ht2 : s₁ ≠ j₂ := by simp [s₁, j₂, Fin.ext_iff]
  have ht3 : s₁ ≠ j₃ := by simp [s₁, j₃, Fin.ext_iff]
  have hs01 : s₀ ≠ s₁ := by simp [s₀, s₁, Fin.ext_iff]
  let g : GL (Fin n) K := Matrix.GeneralLinearGroup.swap K s₀ s₁
  have hgval : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.swap K s₀ s₁ := rfl
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Units.ext (Matrix.swap_mul_self s₀ s₁)
  have hgG : g ∈ StatedSU n (2 ^ f) K :=
    Subgroup.subset_closure ⟨by rw [hgval]; exact det_swap_of_charTwo hs01,
      by rw [hgval]; exact swap_unitary _ hq0 s₀ s₁⟩
  refine not_localRankLeTwo_of_torus (StatedSU n (2 ^ f) K) j₀ j₁ j₂ j₃ s₀ h01 h02 h03 h12 h13
    h23 hs0 hs1 hs2 hs3 (Subgroup.zpowers ζ) (by rw [Nat.card_zpowers, hζ]) ?_ ?_
    (Subgroup.zpowers g) (Subgroup.zpowers_le.mpr hgG) ?_ ?_ ?_ hP
  · intro x hx
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hx).trans (by rw [hζ]))
  · intro a ha b hb c hc
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show ((diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).det = 1
      rw [coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod, prod_torusVec, Units.val_one]
    · exact diagGL_unitary (2 ^ f) hq0 _ fun i => hMq _ (torusVec_mem ha hb hc i)
  · exact ⟨g, Subgroup.mem_zpowers g, swap_not_mem_scalars hs01⟩
  · intro u hu
    have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hu).trans hord)
  · intro a _ b _ c _ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hcomm : Commute (diagGL n K (torusVec j₀ j₁ j₂ j₃ a b c)) g :=
      commute_diagGL_swap _ s₀ s₁ fun x => by
        by_cases hx0 : x = s₀
        · subst hx0
          rw [Equiv.swap_apply_left, torusVec_apply_of_ne ht0 ht1 ht2 ht3,
            torusVec_apply_of_ne hs0 hs1 hs2 hs3]
        · by_cases hx1 : x = s₁
          · subst hx1
            rw [Equiv.swap_apply_right, torusVec_apply_of_ne ht0 ht1 ht2 ht3,
              torusVec_apply_of_ne hs0 hs1 hs2 hs3]
          · rw [Equiv.swap_apply_of_ne_of_ne hx0 hx1]
    rw [(hcomm.zpow_right k).mul_inv_cancel]
    exact Subgroup.zpow_mem_zpowers g k

end CFSG.RankThree.PartOne.Sec66T
