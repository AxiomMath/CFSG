module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6NormA
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6NormB

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

private def dm (i : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.diagonal fun r : Fin 6 => if r.val % 3 = i.val then 0 else 1

private theorem dm_inj : ∀ i i' : Fin 3, dm i = dm i' → i = i' := by decide

private theorem uu_sq_add (j : Fin 3) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    ((uu j ^ k : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 +
      ((uu j ^ k : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1 = dm j := by
  rcases hk with rfl | rfl <;> fin_cases j <;> decide

private theorem uu_sq_add' (i : Fin 3) :
    ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 +
      ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1 = dm i := by
  fin_cases i <;> decide

private theorem exists_plane_perm {σ : G6} (hσ : σ ∈ Subgroup.normalizer (B3 : Set G6)) :
    ∃ (π : Fin 3 → Fin 3) (k : Fin 3 → ℕ), (∀ i, k i = 1 ∨ k i = 2) ∧
      ∀ i, σ * uu i * σ⁻¹ = uu (π i) ^ k i := by
  choose π k hk using fun i => normalizer_special hσ i
  exact ⟨π, k, fun i => (hk i).1, fun i => (hk i).2⟩

private theorem mul_dm {σ : G6} {π : Fin 3 → Fin 3} {k : Fin 3 → ℕ}
    (hk : ∀ i, k i = 1 ∨ k i = 2) (h : ∀ i, σ * uu i * σ⁻¹ = uu (π i) ^ k i) (i : Fin 3) :
    (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i =
      dm (π i) * (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have h1 : σ * uu i = (uu (π i) ^ k i) * σ := mul_inv_eq_iff_eq_mul.mp (h i)
  have h2 : (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      ((uu (π i) ^ k i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have := congrArg Units.val h1
    rwa [Units.val_mul, Units.val_mul] at this
  rw [← uu_sq_add (π i) (k i) (hk i), ← uu_sq_add' i]
  generalize (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = S at h2 ⊢
  generalize ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = U at h2 ⊢
  generalize ((uu (π i) ^ k i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = T at h2 ⊢
  have h3 : S * U ^ 2 = T ^ 2 * S := by
    calc S * U ^ 2 = (S * U) * U := by rw [pow_two, Matrix.mul_assoc]
      _ = (T * S) * U := by rw [h2]
      _ = T * (S * U) := by rw [Matrix.mul_assoc]
      _ = T * (T * S) := by rw [h2]
      _ = T ^ 2 * S := by rw [pow_two, Matrix.mul_assoc]
  rw [Matrix.mul_add, Matrix.mul_add, h3, h2, Matrix.mul_one, Matrix.add_mul, Matrix.add_mul,
    Matrix.one_mul]

private def pidx (π : Fin 3 → Fin 3) (c : Fin 6) : Fin 6 :=
  ⟨(π ⟨c.val % 3, by omega⟩).val, by have := (π ⟨c.val % 3, by omega⟩).isLt; omega⟩

private theorem pidx_lt (π : Fin 3 → Fin 3) (c : Fin 6) : (pidx π c).val < 3 :=
  (π ⟨c.val % 3, by omega⟩).isLt

private theorem supp_of_mul_dm {S : Matrix (Fin 6) (Fin 6) (ZMod 2)} {π : Fin 3 → Fin 3}
    (h : ∀ i, S * dm i = dm (π i) * S) (r c : Fin 6) (hrc : S r c ≠ 0) :
    r.val % 3 = (pidx π c).val := by
  have e := congr_fun (congr_fun (h ⟨c.val % 3, by omega⟩) r) c
  simp only [dm, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  by_contra hne
  simp only [pidx] at hne
  simp [hne] at e
  exact hrc e.symm

private theorem r_eq_of_mod : ∀ r a : Fin 6, a.val < 3 → r.val % 3 = a.val → r = a ∨ r = a + 3 := by
  decide

private theorem onPair_col {S : Matrix (Fin 6) (Fin 6) (ZMod 2)} {π : Fin 3 → Fin 3}
    (h : ∀ i, S * dm i = dm (π i) * S) (c : Fin 6) : OnPair (pidx π c) (fun r => S r c) := by
  intro r h1 h2
  by_contra hne
  rcases r_eq_of_mod r (pidx π c) (pidx_lt π c) (supp_of_mul_dm h r c hne) with h3 | h3
  · exact h1 h3
  · exact h2 h3

private theorem plane_inj {σ : G6} {π : Fin 3 → Fin 3}
    (h : ∀ i, (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i =
      dm (π i) * (σ : Matrix (Fin 6) (Fin 6) (ZMod 2))) : Function.Injective π := by
  intro i i' hii
  apply dm_inj
  have hσ : ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc dm i = ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        ((σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i) := by
        rw [← Matrix.mul_assoc, hσ, Matrix.one_mul]
    _ = ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        ((σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i') := by rw [h i, h i', hii]
    _ = dm i' := by rw [← Matrix.mul_assoc, hσ, Matrix.one_mul]

private theorem mulVec_injective_units (σ : G6) {v w : Fin 6 → ZMod 2}
    (h : (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w) :
    v = w := by
  have := congrArg (fun x => ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x) h
  simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] using this

private theorem col_ne_zero (σ : G6) (c : Fin 6) :
    (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c) ≠ 0 := by
  intro h
  have h1 : (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single c 1 =
      (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ 0 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_zero]
    exact h
  have := congrFun (mulVec_injective_units σ h1) c
  simp at this

private theorem col_ne_col (σ : G6) {c c' : Fin 6} (hcc : c ≠ c') :
    (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c) ≠
      (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c') := by
  intro h
  have h1 : (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single c 1 =
      (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single c' 1 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    exact h
  have := congrFun (mulVec_injective_units σ h1) c
  simp [Pi.single_apply, hcc] at this

private theorem sp0_of_planes {σ : G6} {π : Fin 3 → Fin 3} (hinj : Function.Injective π)
    (h : ∀ i, (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i =
      dm (π i) * (σ : Matrix (Fin 6) (Fin 6) (ZMod 2))) : σ ∈ Sp0 := by
  show (σ : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 * (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0
  ext c c'
  rw [bf_apply, J0_eq_ite]
  by_cases hcc : c = c'
  · subst hcc
    simp [Bf_self]
  · by_cases h3 : c.val % 3 = c'.val % 3
    · have hp : pidx π c = pidx π c' := by simp [pidx, h3]
      rw [if_pos ⟨h3, hcc⟩]
      exact Bf_same (pidx_lt π c) (onPair_col h c) (hp ▸ onPair_col h c') (col_ne_zero σ c)
        (col_ne_zero σ c') (col_ne_col σ hcc)
    · rw [if_neg (fun h' => h3 h'.1)]
      have hp : pidx π c ≠ pidx π c' := by
        intro hp
        apply h3
        have := hinj (Fin.ext (by simpa [pidx] using congrArg Fin.val hp))
        have h4 := congrArg Fin.val this
        simpa using h4
      exact Bf_cross (pidx_lt π c) (pidx_lt π c') hp (onPair_col h c) (onPair_col h c')

private theorem mv_mul (A B : G6) (v : Fin 6 → ZMod 2) :
    ((A * B : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ((B : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem mv_inv_mul (g : G6) (v : Fin 6 → ZMod 2) :
    ((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem pl_fst (i : Fin 3) : (pl i).1 = ⟨i.val, by omega⟩ := by fin_cases i <;> rfl

private theorem pl_snd (i : Fin 3) : (pl i).2 = ⟨i.val, by omega⟩ + 3 := by fin_cases i <;> rfl

private theorem map_sig_of_planes {σ : G6} {π : Fin 3 → Fin 3} (hinj : Function.Injective π)
    (h : ∀ i, (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * dm i =
      dm (π i) * (σ : Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    Sig0.map (MulAut.conj σ).toMonoidHom = Sig (π 2) := by
  have hσ : σ ∈ Sp0 := sp0_of_planes hinj h
  have hx : OnPair (pidx π 2) (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 2) :=
    onPair_col h 2
  have hy : OnPair (pidx π 2) (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r 5) :=
    onPair_col h 5
  have hfix := fix_iff (pidx_lt π 2) hx hy (col_ne_zero σ 2) (col_ne_zero σ 5)
    (col_ne_col σ (by decide))
  have ha : pidx π 2 = ⟨(π 2).val, by omega⟩ := rfl
  have hcol : ∀ c : Fin 6, (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single c 1 =
      fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c := fun c => by
    rw [Matrix.mulVec_single_one]; rfl
  ext g
  constructor
  · rintro ⟨g0, hg0, rfl⟩
    obtain ⟨hg0S, hg2, hg5⟩ := hg0
    have e2 : (g0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single 2 1 = Pi.single 2 1 := hg2
    have e5 : (g0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single 5 1 = Pi.single 5 1 := hg5
    have hH : ∀ c : Fin 6, (g0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single c 1 = Pi.single c 1 →
        ((σ * g0 * σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          (fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c) =
        fun r => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) r c := by
      intro c hc
      rw [← hcol c, mv_mul, mv_mul, mv_inv_mul, hc]
    have hHx := hH 2 e2
    have hHy := hH 5 e5
    have := (hfix _).mp ⟨hHx, hHy⟩
    refine ⟨mul_mem (mul_mem hσ hg0S) (inv_mem hσ), ?_, ?_⟩
    · rw [pl_fst, ← ha]; exact this.1
    · rw [pl_snd, ← ha]; exact this.2
  · rintro ⟨hgS, hg1, hg2⟩
    rw [pl_fst, ← ha] at hg1
    rw [pl_snd, ← ha] at hg2
    have hgx := (hfix _).mpr ⟨hg1, hg2⟩
    refine ⟨σ⁻¹ * g * σ, ⟨mul_mem (mul_mem (inv_mem hσ) hgS) hσ, ?_, ?_⟩, ?_⟩
    · show ((σ⁻¹ * g * σ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (2 : Fin 6) 1 =
        Pi.single (2 : Fin 6) 1
      rw [mv_mul, mv_mul, hcol 2, hgx.1, ← hcol 2, mv_inv_mul]
    · show ((σ⁻¹ * g * σ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (5 : Fin 6) 1 =
        Pi.single (5 : Fin 6) 1
      rw [mv_mul, mv_mul, hcol 5, hgx.2, ← hcol 5, mv_inv_mul]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private theorem u0_sq_eq_inv : u0 ^ 2 = u0⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact u0_pow_three

theorem map_sig0_of_mem_normalizer {σ : G6} (hσ : σ ∈ Subgroup.normalizer (B3 : Set G6))
    (h1 : σ * u0 * σ⁻¹ ≠ u0) (h2 : σ * u0 * σ⁻¹ ≠ u0⁻¹) :
    Sig0.map (MulAut.conj σ).toMonoidHom = Sig 0 ∨
      Sig0.map (MulAut.conj σ).toMonoidHom = Sig 1 := by
  obtain ⟨π, k, hk, h⟩ := exists_plane_perm hσ
  have hdm := mul_dm hk h
  have hmap := map_sig_of_planes (plane_inj hdm) hdm
  have hπ2 : π 2 ≠ 2 := by
    intro hπ
    have e := h 2
    rw [hπ] at e
    rcases hk 2 with hk2 | hk2
    · rw [hk2, pow_one] at e
      exact h1 e
    · rw [hk2] at e
      exact h2 (e.trans u0_sq_eq_inv)
  rw [hmap]
  have : ∀ x : Fin 3, x ≠ 2 → x = 0 ∨ x = 1 := by decide
  rcases this _ hπ2 with h0 | h1'
  · rw [h0]; exact Or.inl rfl
  · rw [h1']; exact Or.inr rfl

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
