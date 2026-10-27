module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem exists_spMat_of_mem_H {x : X} (hx : x ∈ S.H) :
    ∃ (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3), IsSign s ∧ σ 0 = 0 ∧ s 0 = 1 ∧
      ∏ i : Fin 7, s i.succ = 1 ∧ S.ρ x = spMat σ s := by
  obtain ⟨σ, s, hs, ⟨hσ, hs0, hprod⟩, hA⟩ := (S.mem_H_iff x).1 hx
  exact ⟨σ, s, hs, hσ, hs0, hprod, hA⟩

private theorem p9uN7_isSign_ne_zero {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s)
    (i : Fin k) : s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

private theorem p9uN7_spMat_col {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3)
    (j : Fin k) : (fun i => spMat σ s i j) = Pi.single (σ j) (s j) := by
  funext i
  rw [spMat, Pi.single_apply]

private theorem p9uN7_single_eq_single_of_ne_zero {k : ℕ} {i j : Fin k} {a b : ZMod 3}
    (ha : a ≠ 0)
    (h : Pi.single (M := fun _ => ZMod 3) i a = Pi.single (M := fun _ => ZMod 3) j b) :
    i = j ∧ a = b := by
  have hi := congrFun h i
  rw [Pi.single_eq_same, Pi.single_apply] at hi
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl] at hi
    exact ⟨rfl, hi⟩
  · rw [if_neg hij] at hi
    exact absurd hi ha

private theorem p9uN7_spMat_inj {k : ℕ} {σ τ : Equiv.Perm (Fin k)} {s t : Fin k → ZMod 3}
    (hs : IsSign s) (ht : IsSign t) (h : spMat σ s = spMat τ t) : σ = τ ∧ s = t := by
  have hcol : ∀ j, Pi.single (M := fun _ => ZMod 3) (σ j) (s j) =
      Pi.single (M := fun _ => ZMod 3) (τ j) (t j) := by
    intro j
    rw [← p9uN7_spMat_col σ s j, ← p9uN7_spMat_col τ t j, h]
  constructor
  · apply Equiv.ext
    intro j
    exact (p9uN7_single_eq_single_of_ne_zero (p9uN7_isSign_ne_zero hs j) (hcol j)).1
  · funext j
    exact (p9uN7_single_eq_single_of_ne_zero (p9uN7_isSign_ne_zero hs j) (hcol j)).2

private theorem p9uN7_isSign_mul' {k : ℕ} {s t : Fin k → ZMod 3} (hs : IsSign s)
    (ht : IsSign t) (τ : Equiv.Perm (Fin k)) : IsSign (fun j => s (τ j) * t j) := by
  intro j
  change s (τ j) * t j = 1 ∨ s (τ j) * t j = -1
  rcases hs (τ j) with h1 | h1 <;> rcases ht j with h2 | h2
  · rw [h1, h2]; left; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; right; decide
  · rw [h1, h2]; left; decide

private theorem p9uN7_choose_spec (x : S.H) :
    ∃ s : Fin 8 → ZMod 3, IsSign s ∧ s 0 = 1 ∧ (∏ i : Fin 7, s i.succ = 1) ∧
      Classical.choose (S.exists_spMat_of_mem_H x.2) 0 = 0 ∧
      S.ρ (x : X) = spMat (Classical.choose (S.exists_spMat_of_mem_H x.2)) s := by
  obtain ⟨s, hs, hσ0, hs0, hprod, hA⟩ :=
    Classical.choose_spec (S.exists_spMat_of_mem_H x.2)
  exact ⟨s, hs, hs0, hprod, hσ0, hA⟩

noncomputable def permHom : S.H →* Equiv.Perm (Fin 8) where
  toFun x := Classical.choose (S.exists_spMat_of_mem_H x.2)
  map_one' := by
    obtain ⟨s, hs, -, -, hσ0, hA⟩ := p9uN7_choose_spec S (1 : S.H)
    have h1 : S.ρ (((1 : S.H) : X)) = 1 := by rw [Subgroup.coe_one, map_one]
    have heq : spMat (Classical.choose (S.exists_spMat_of_mem_H (1 : S.H).2)) s =
        spMat (1 : Equiv.Perm (Fin 8)) (fun _ => 1) := by
      rw [← hA, h1, spMat_one]
    exact (p9uN7_spMat_inj hs (fun _ => Or.inl rfl) heq).1
  map_mul' := by
    intro x y
    obtain ⟨sx, hsx, -, -, -, hAx⟩ := p9uN7_choose_spec S x
    obtain ⟨sy, hsy, -, -, -, hAy⟩ := p9uN7_choose_spec S y
    obtain ⟨sxy, hsxy, -, -, -, hAxy⟩ := p9uN7_choose_spec S (x * y)
    have hxy : S.ρ (((x * y : S.H) : X)) = S.ρ (x : X) * S.ρ (y : X) := by
      rw [Subgroup.coe_mul, map_mul]
    have heq : spMat (Classical.choose (S.exists_spMat_of_mem_H (x * y).2)) sxy =
        spMat (Classical.choose (S.exists_spMat_of_mem_H x.2) *
          Classical.choose (S.exists_spMat_of_mem_H y.2))
          (fun j => sx (Classical.choose (S.exists_spMat_of_mem_H y.2) j) * sy j) := by
      rw [← spMat_mul, ← hAxy, hxy, ← hAx, ← hAy]
    exact (p9uN7_spMat_inj hsxy
      (p9uN7_isSign_mul' hsx hsy (Classical.choose (S.exists_spMat_of_mem_H y.2))) heq).1

theorem permHom_spec (x : S.H) :
    ∃ s : Fin 8 → ZMod 3, IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 7, s i.succ = 1 ∧
      S.ρ x = spMat (S.permHom x) s := by
  obtain ⟨s, hs, hs0, hprod, -, hA⟩ := p9uN7_choose_spec S x
  exact ⟨s, hs, hs0, hprod, hA⟩

theorem permHom_zero (x : S.H) : S.permHom x 0 = 0 := by
  obtain ⟨-, -, -, -, hσ0, -⟩ := p9uN7_choose_spec S x
  exact hσ0

theorem exists_permHom_eq {σ : Equiv.Perm (Fin 8)} (h0 : σ 0 = 0) :
    ∃ x : S.H, S.permHom x = σ ∧ S.ρ x = spMat σ (fun _ => 1) := by
  have hM : spMat σ (fun _ => (1 : ZMod 3)) ∈ evenFix0 7 :=
    ⟨σ, fun _ => 1, fun _ => Or.inl rfl, ⟨h0, rfl, by simp⟩, rfl⟩
  obtain ⟨x, hxρ⟩ := S.surj_H (spMat σ (fun _ => 1)) hM
  have hxH : x ∈ S.H := (S.mem_H_iff x).2 (by rw [hxρ]; exact hM)
  refine ⟨⟨x, hxH⟩, ?_, ?_⟩
  · obtain ⟨s', hs', -, -, hA'⟩ := S.permHom_spec ⟨x, hxH⟩
    have heq : spMat (S.permHom ⟨x, hxH⟩) s' = spMat σ (fun _ => 1) := by
      rw [← hA', hxρ]
    exact (p9uN7_spMat_inj hs' (fun _ => Or.inl rfl) heq).1
  · exact hxρ

theorem permHom_eq_one_iff_mem_F1 (x : S.H) : S.permHom x = 1 ↔ (x : X) ∈ S.F1 := by
  constructor
  · intro h1
    obtain ⟨s, hs, hs0, hprod, hA⟩ := S.permHom_spec x
    let A : Finset (Fin 8) := Finset.univ.filter fun i => s i = -1
    have hsgn : s = fun i => if i ∈ A then (-1 : ZMod 3) else 1 := by
      funext i
      by_cases hi : s i = -1
      · have hmem : i ∈ A := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
        rw [if_pos hmem, hi]
      · have hmem : i ∉ A := fun h => hi (Finset.mem_filter.1 h).2
        rw [if_neg hmem]
        rcases hs i with h | h
        · exact h
        · exact absurd h hi
    have hprodA : (∏ i : Fin 8, s i) = (-1 : ZMod 3) ^ A.card := by
      rw [hsgn]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hprod_all : (∏ i : Fin 8, s i) = 1 := by
      rw [Fin.prod_univ_succ]
      rw [hs0, hprod, mul_one]
    have hAeven : Even A.card := by
      have hone : (-1 : ZMod 3) ^ A.card = 1 := by rw [← hprodA, hprod_all]
      exact (neg_one_pow_eq_one_iff_even (R := ZMod 3) (by decide)).1 hone
    have h0A : (0 : Fin 8) ∉ A := by
      intro h
      have hz : s 0 = -1 := (Finset.mem_filter.1 h).2
      rw [hs0] at hz
      exact absurd hz (by decide)
    have hρ : S.ρ x = sgn A := by
      rw [hA, h1, hsgn, q2nN7_sgn_eq_spMat]
    exact (S.mem_F1_iff x).2 ⟨A, h0A, hAeven, hρ⟩
  · intro hx
    obtain ⟨A, h0A, hAeven, hρA⟩ := (S.mem_F1_iff x).1 hx
    obtain ⟨s, hs, -, -, hA⟩ := S.permHom_spec x
    have hsign : IsSign (fun i => if i ∈ A then (-1 : ZMod 3) else 1) := by
      intro i
      by_cases hi : i ∈ A <;> simp [hi]
    have heq : spMat (S.permHom x) s =
        spMat (1 : Equiv.Perm (Fin 8)) (fun i => if i ∈ A then (-1 : ZMod 3) else 1) := by
      rw [← hA, hρA, q2nN7_sgn_eq_spMat]
    exact (p9uN7_spMat_inj hs hsign heq).1

theorem permHom_apply_eq_self_of_mulVec_single (x : S.H) {i : Fin 8}
    (h : S.ρ x *ᵥ Pi.single i 1 = Pi.single i 1) : S.permHom x i = i := by
  obtain ⟨s, hs, -, -, hA⟩ := S.permHom_spec x
  rw [hA, spMat_mulVec] at h
  have hσ := congrFun h (S.permHom x i)
  rw [Equiv.symm_apply_apply, Pi.single_eq_same, mul_one] at hσ
  by_cases hii : S.permHom x i = i
  · exact hii
  · rw [Pi.single_apply, if_neg hii] at hσ
    exact absurd hσ (p9uN7_isSign_ne_zero hs i)

theorem permHom_mem_iff_of_comm_sgn (x : S.H) {A : Finset (Fin 8)}
    (h : S.ρ x * sgn A = sgn A * S.ρ x) (l : Fin 8) : S.permHom x l ∈ A ↔ l ∈ A := by
  obtain ⟨s, hs, -, -, hA⟩ := S.permHom_spec x
  have hentry := congrFun (congrFun h (S.permHom x l)) l
  rw [hA, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, spMat_apply, if_pos rfl] at hentry
  have hcancel : (if S.permHom x l ∈ A then (-1 : ZMod 3) else 1) =
      (if l ∈ A then -1 else 1) := by
    have h2 : s l * (if l ∈ A then (-1 : ZMod 3) else 1) =
        s l * (if S.permHom x l ∈ A then -1 else 1) := by
      rw [hentry, mul_comm]
    exact (mul_left_cancel₀ (p9uN7_isSign_ne_zero hs l) h2).symm
  by_cases hl : l ∈ A <;> by_cases hsl : S.permHom x l ∈ A
  · exact iff_of_true hsl hl
  · rw [if_pos hl, if_neg hsl] at hcancel
    exact absurd hcancel.symm (by decide)
  · rw [if_neg hl, if_pos hsl] at hcancel
    exact absurd hcancel (by decide)
  · exact iff_of_false hsl hl

theorem exists_mem_F1_of_mem_F1set {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ F1set) :
    ∃ x : X, x ∈ S.F1 ∧ S.ρ x = M := by
  obtain ⟨A, h0A, hAeven, hMeq⟩ := hM
  subst hMeq
  obtain ⟨x, hx⟩ := S.surj_H (sgn A) (q2nN7_sgn_mem_evenFix0 h0A hAeven)
  exact ⟨x, (S.mem_F1_iff x).2 ⟨A, h0A, hAeven, hx⟩, hx⟩

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
