module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Matrix CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

private theorem k67uc_eq_diagonal_of_commute_diagonal {K : Type*} [Field K] {t : Fin 3 → K}
    (ht : Function.Injective t) {X : Matrix (Fin 3) (Fin 3) K}
    (h : X * diagonal t = diagonal t * X) : X = diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij]
    have hc := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
    have hne : t j - t i ≠ 0 := sub_ne_zero.mpr (fun h' => hij (ht h').symm)
    have h0 : X i j * (t j - t i) = 0 := by
      rw [mul_sub, hc, mul_comm (t i) (X i j), sub_self]
    exact (mul_eq_zero.mp h0).resolve_right hne

private theorem k67uc_conj_cancel {K : Type*} [Field K] {B B' G G' : Matrix (Fin 3) (Fin 3) K}
    (hBB' : B * B' = 1) (h : B' * G * B = B' * G' * B) : G = G' := by
  have h1 : B * (B' * G * B) * B' = G := by
    calc B * (B' * G * B) * B' = (B * B') * G * (B * B') := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
  have h2 : B * (B' * G' * B) * B' = G' := by
    calc B * (B' * G' * B) * B' = (B * B') * G' * (B * B') := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
  rw [← h1, ← h2, h]

private theorem k67uc_diagonal_data {K : Type} [Field K] (σ : K ≃+* K) {ω : K}
    (h3 : (3 : K) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0)
    {B B' M G : Matrix (Fin 3) (Fin 3) K}
    (hBB' : B * B' = 1) (hB'B : B' * B = 1)
    (hMB : M * B = B * diagonal ![ω, 1, ω ^ 2])
    (hBJ : conjTr σ B * antidiag 3 * B = antidiag 3)
    (hGM : G * M = M * G)
    (hGiso : conjTr σ G * antidiag 3 * G = antidiag 3)
    (hGdet : G.det = 1) :
    (B' * G * B = diagonal (fun i => (B' * G * B) i i)) ∧
      (σ ((B' * G * B) 0 0) * (B' * G * B) 2 2 = 1) ∧
      ((B' * G * B) 0 0 * (B' * G * B) 1 1 * (B' * G * B) 2 2 = 1) ∧
      ((B' * G * B) 0 0 ≠ 0) ∧ ((B' * G * B) 2 2 ≠ 0) := by
  set X : Matrix (Fin 3) (Fin 3) K := B' * G * B with hX
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω; simp at hω
  have hω1 : ω ≠ 1 := fun h => h3 (by rw [h] at hω; linear_combination hω)
  have hω2 : ω ^ 2 ≠ 1 := fun h => h3 (by
    linear_combination (-(ω - 2)) * hω + ((ω - 2) + 1) * h)
  have hωω : ω ≠ ω ^ 2 := fun h => hω1 (by
    have : ω * (ω - 1) = 0 := by linear_combination -h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)))
  have hDinj : Function.Injective (![ω, 1, ω ^ 2] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; exact absurd hij hω1
    · exfalso; exact absurd hij hωω
    · exfalso; exact absurd hij.symm hω1
    · rfl
    · exfalso; exact absurd hij.symm hω2
    · exfalso; exact absurd hij.symm hωω
    · exfalso; exact absurd hij hω2
    · rfl
  have hB'M : B' * M = diagonal ![ω, 1, ω ^ 2] * B' := by
    have h1 : (B' * M) * B = diagonal ![ω, 1, ω ^ 2] := by
      calc (B' * M) * B = B' * (M * B) := by rw [Matrix.mul_assoc]
        _ = B' * (B * diagonal ![ω, 1, ω ^ 2]) := by rw [hMB]
        _ = (B' * B) * diagonal ![ω, 1, ω ^ 2] := by rw [Matrix.mul_assoc]
        _ = diagonal ![ω, 1, ω ^ 2] := by rw [hB'B, Matrix.one_mul]
    calc B' * M = (B' * M) * 1 := (Matrix.mul_one _).symm
      _ = (B' * M) * (B * B') := by rw [hBB']
      _ = ((B' * M) * B) * B' := by simp only [Matrix.mul_assoc]
      _ = diagonal ![ω, 1, ω ^ 2] * B' := by rw [h1]
  have hB'iso : conjTr σ B' * antidiag 3 * B' = antidiag 3 := by
    calc conjTr σ B' * antidiag 3 * B'
        = conjTr σ B' * (conjTr σ B * antidiag 3 * B) * B' := by rw [hBJ]
      _ = (conjTr σ B' * conjTr σ B) * antidiag 3 * (B * B') := by
            simp only [Matrix.mul_assoc]
      _ = conjTr σ (B * B') * antidiag 3 * (B * B') := by rw [← conjTr_mul]
      _ = antidiag 3 := by rw [hBB', conjTr_one, Matrix.one_mul, Matrix.mul_one]
  have hcomm : X * diagonal ![ω, 1, ω ^ 2] = diagonal ![ω, 1, ω ^ 2] * X := by
    rw [hX]
    calc (B' * G * B) * diagonal ![ω, 1, ω ^ 2]
        = B' * G * (B * diagonal ![ω, 1, ω ^ 2]) := by rw [Matrix.mul_assoc]
      _ = B' * G * (M * B) := by rw [← hMB]
      _ = B' * (G * M) * B := by simp only [Matrix.mul_assoc]
      _ = B' * (M * G) * B := by rw [hGM]
      _ = (B' * M) * (G * B) := by simp only [Matrix.mul_assoc]
      _ = (diagonal ![ω, 1, ω ^ 2] * B') * (G * B) := by rw [hB'M]
      _ = diagonal ![ω, 1, ω ^ 2] * (B' * G * B) := by simp only [Matrix.mul_assoc]
      _ = diagonal ![ω, 1, ω ^ 2] * X := by rw [hX]
  have hXdiag : X = diagonal (fun i => X i i) :=
    k67uc_eq_diagonal_of_commute_diagonal hDinj hcomm
  have hXiso : conjTr σ X * antidiag 3 * X = antidiag 3 := by
    rw [hX]
    calc conjTr σ (B' * G * B) * antidiag 3 * (B' * G * B)
        = conjTr σ B * (conjTr σ G * (conjTr σ B' * antidiag 3 * B') * G) * B := by
            simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ B * (conjTr σ G * antidiag 3 * G) * B := by rw [hB'iso]
      _ = conjTr σ B * antidiag 3 * B := by rw [hGiso]
      _ = antidiag 3 := hBJ
  have hXdet : X.det = 1 := by
    rw [hX, Matrix.det_mul, Matrix.det_mul, hGdet, mul_one, ← Matrix.det_mul, hB'B,
      Matrix.det_one]
  have hE : σ (X 0 0) * X 2 2 = 1 := by
    have h := congrFun (congrFun hXiso 0) 2
    have hcd : conjTr σ (diagonal (fun i => X i i)) = diagonal (fun i => σ (X i i)) :=
      conjTr_diagonal σ (fun i => X i i)
    rw [hXdiag, hcd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h02 : (antidiag 3 : Matrix (Fin 3) (Fin 3) K) 0 2 = 1 := by
      simp [antidiag, Fin.rev]
    rw [h02, mul_one] at h
    simpa using h
  have hF : X 0 0 * X 1 1 * X 2 2 = 1 := by
    have h := hXdet
    rw [hXdiag, Matrix.det_diagonal, Fin.prod_univ_three] at h
    exact h
  have ha0 : X 0 0 ≠ 0 := by
    intro h0
    have h := hE
    rw [h0, map_zero, zero_mul] at h
    exact one_ne_zero h.symm
  have hc0 : X 2 2 ≠ 0 := by
    intro h0
    have h := hE
    rw [h0, mul_zero] at h
    exact one_ne_zero h.symm
  exact ⟨hXdiag, hE, hF, ha0, hc0⟩

theorem card_centralizer_su_three_le {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f) (hσσ : ∀ c : K, σ (σ c) = c)
    (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) {d : SU σ 3}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Nat.card (Subgroup.centralizer ({d} : Set (SU σ 3))) ≤ (p ^ f) ^ 2 - 1 := by
  classical
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_pow_mod_one hf hq
  obtain ⟨ω, hω, hωQ⟩ := exists_cube_root (F := K) hK hq
  have hσω : σ ω = ω := by rw [hσ]; exact hωQ
  have hnorm : ∀ c : K, σ c = c → c ≠ 0 → ∃ β : K, σ β * β = c := by
    intro c hc hc0
    obtain ⟨β, hβ⟩ := exists_norm_eq hK (by rw [← hσ]; exact hc) hc0
    exact ⟨β, by rw [hσ]; exact hβ⟩
  let M : Matrix (Fin 3) (Fin 3) K := ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  obtain ⟨hMcube0, hMdet0, hMiso0, hMns0⟩ := su_cube_facts σ hσ hq hd3 hd1
  have hMcube : M * M * M = 1 := by simpa [M] using hMcube0
  have hMdet : M.det = 1 := by simpa [M] using hMdet0
  have hMiso : conjTr σ M * antidiag 3 * M = antidiag 3 := by simpa [M] using hMiso0
  have hMns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by simpa [M] using hMns0
  obtain ⟨B, hBdet, hBJ, hMB⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm (antidiag 3)
    (conjTr_antidiag σ 3) det_antidiag_three M hMiso hMcube hMdet hMns
  obtain ⟨Bgl, hBgl⟩ : ∃ Bgl : GL (Fin 3) K, (Bgl : Matrix (Fin 3) (Fin 3) K) = B :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin 3) (Fin 3) K,
      B' = ((Bgl⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hBB' : B * B' = 1 := by
    rw [hB', ← hBgl, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB'B : B' * B = 1 := by
    rw [hB', ← hBgl, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let C : Subgroup ↥(SU σ 3) := Subgroup.centralizer ({d} : Set (SU σ 3))
  let Gmat : C → Matrix (Fin 3) (Fin 3) K := fun g =>
    B' * (((g : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B
  have key : ∀ g : C,
      (Gmat g = diagonal (fun i => Gmat g i i)) ∧
      (σ (Gmat g 0 0) * Gmat g 2 2 = 1) ∧
      (Gmat g 0 0 * Gmat g 1 1 * Gmat g 2 2 = 1) ∧
      Gmat g 0 0 ≠ 0 ∧ Gmat g 2 2 ≠ 0 := by
    intro g
    have hgcen : (g : ↥(SU σ 3)) ∈ Subgroup.centralizer ({d} : Set (SU σ 3)) := g.2
    have hc : d * (g : ↥(SU σ 3)) = (g : ↥(SU σ 3)) * d :=
      (Subgroup.mem_centralizer_iff.1 hgcen) d (by simp)
    obtain ⟨hGdet, hGiso⟩ := mem_SU.1 (g : ↥(SU σ 3)).2
    have hGM : (((g : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * (((g : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have h := congrArg (fun z : ↥(SU σ 3) =>
        (((z : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hc
      simpa [M] using h.symm
    have hdata := k67uc_diagonal_data (σ := σ) (ω := ω) h3 hω hBB' hB'B hMB hBJ hGM hGiso hGdet
    simpa only [Gmat] using hdata
  have hGmat0 : ∀ g : C, Gmat g 0 0 ≠ 0 := fun g => (key g).2.2.2.1
  let fmap : C → Kˣ := fun g => Units.mk0 (Gmat g 0 0) (hGmat0 g)
  have hfinj : Function.Injective fmap := by
    intro g₁ g₂ heq
    have haeq : Gmat g₁ 0 0 = Gmat g₂ 0 0 := by
      have h := congrArg (fun u : Kˣ => (u : K)) heq
      simpa [fmap] using h
    have hc1 : σ (Gmat g₁ 0 0) * Gmat g₁ 2 2 = 1 := (key g₁).2.1
    have hc2 : σ (Gmat g₂ 0 0) * Gmat g₂ 2 2 = 1 := (key g₂).2.1
    have hc0₁ : Gmat g₁ 2 2 ≠ 0 := (key g₁).2.2.2.2
    have hσa2 : σ (Gmat g₂ 0 0) ≠ 0 := by
      intro h0
      have h := hc2
      rw [h0, zero_mul] at h
      exact one_ne_zero h.symm
    have hceq : Gmat g₁ 2 2 = Gmat g₂ 2 2 := by
      refine mul_left_cancel₀ hσa2 ?_
      calc σ (Gmat g₂ 0 0) * Gmat g₁ 2 2
          = σ (Gmat g₁ 0 0) * Gmat g₁ 2 2 := by rw [← haeq]
        _ = 1 := hc1
        _ = σ (Gmat g₂ 0 0) * Gmat g₂ 2 2 := hc2.symm
    have hb1 : Gmat g₁ 0 0 * Gmat g₁ 1 1 * Gmat g₁ 2 2 = 1 := (key g₁).2.2.1
    have hb2 : Gmat g₂ 0 0 * Gmat g₂ 1 1 * Gmat g₂ 2 2 = 1 := (key g₂).2.2.1
    have hfac : Gmat g₁ 0 0 * Gmat g₁ 2 2 ≠ 0 := mul_ne_zero (hGmat0 g₁) hc0₁
    have hbeq : Gmat g₁ 1 1 = Gmat g₂ 1 1 := by
      refine mul_left_cancel₀ hfac ?_
      calc (Gmat g₁ 0 0 * Gmat g₁ 2 2) * Gmat g₁ 1 1
          = Gmat g₁ 0 0 * Gmat g₁ 1 1 * Gmat g₁ 2 2 := by ring
        _ = 1 := hb1
        _ = Gmat g₂ 0 0 * Gmat g₂ 1 1 * Gmat g₂ 2 2 := hb2.symm
        _ = (Gmat g₁ 0 0 * Gmat g₁ 2 2) * Gmat g₂ 1 1 := by rw [← haeq, ← hceq]; ring
    have hXeq : Gmat g₁ = Gmat g₂ := by
      rw [(key g₁).1, (key g₂).1]
      congr 1
      funext i
      fin_cases i
      · exact haeq
      · exact hbeq
      · exact hceq
    have hXeq' : B' * (((g₁ : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B =
        B' * (((g₂ : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B := hXeq
    have hG₁G₂ : (((g₁ : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((g₂ : ↥(SU σ 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      k67uc_conj_cancel hBB' hXeq'
    exact Subtype.ext (Subtype.ext (Units.ext hG₁G₂))
  have hcard : Nat.card C ≤ Nat.card Kˣ := Nat.card_le_card_of_injective fmap hfinj
  rw [Nat.card_units] at hcard
  rw [hK] at hcard
  change Nat.card C ≤ (p ^ f) ^ 2 - 1
  exact hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
