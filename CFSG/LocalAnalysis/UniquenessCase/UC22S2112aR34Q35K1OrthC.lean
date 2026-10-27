module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1OrthT
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1OrthO
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry
import TauCeti.LinearAlgebra.Matrix.Diagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

private def uc22s2112r34q35_signK {K : Type} [Field K] (b : Bool) : K :=
  if b then -1 else 1

private theorem uc22s2112r34q35_one_ne_neg_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    (1 : K) ≠ -1 := by
  intro h
  apply h2
  have h1 : (1 : K) - -1 = 0 := sub_eq_zero.mpr h
  have h2' : (1 : K) - -1 = 2 := by ring
  rw [h2'] at h1
  exact h1

private noncomputable def uc22s2112r34q35_signFlag {K : Type} [Field K] (x : K) : Bool := by
  classical
  exact if x = -1 then true else false

private theorem uc22s2112r34q35_signFlag_signK {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    (a : Bool) : uc22s2112r34q35_signFlag (uc22s2112r34q35_signK (K := K) a) = a := by
  classical
  cases a
  · simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
      uc22s2112r34q35_one_ne_neg_one h2]
  · simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]

private theorem uc22s2112r34q35_two_ne_zero {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) : (2 : K) ≠ 0 := by
  classical
  have hF : Fintype K := Fintype.ofFinite K
  intro h2
  have hdvd : ringChar K ∣ 2 := (ringChar.spec K 2).mp h2
  obtain ⟨n, hn⟩ := @FiniteField.card K _ hF (ringChar K) _
  have hrc : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hn.1 Nat.prime_two).mp hdvd
  have hmod : Fintype.card K % 2 = 0 := @FiniteField.even_card_of_char_two K _ hF hrc
  have hcard : Nat.card K = Fintype.card K := @Nat.card_eq_fintype_card K hF
  rw [hcard] at hK
  omega

private theorem uc22s2112r34q35_diagonal_of_commute
    {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    {E : Subgroup (GL (Fin 4 ⊕ κ) K)} {g : GL (Fin 4 ⊕ κ) K} (h2 : (2 : K) ≠ 0)
    (hsep : ∀ k l : Fin 4 ⊕ κ, k ≠ l → ∃ i j : Fin 4 ⊕ κ,
      CFSG.ClassicalGroups.Orthogonal.negCoordGL ({i, j} : Finset (Fin 4 ⊕ κ)) ∈ E ∧
        i ≠ j ∧ ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)))
    (hc : ∀ t ∈ E, g * t = t * g) :
    (g : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) =
      Matrix.diagonal (fun l => (g : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) l l) := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hkl]
    obtain ⟨i, j, hmem, hij, hiff⟩ := hsep k l hkl
    have hdiagz : ((CFSG.ClassicalGroups.Orthogonal.negCoordGL ({i, j} : Finset (Fin 4 ⊕ κ)) :
          GL (Fin 4 ⊕ κ) K) : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) =
        Matrix.diagonal
          (fun x : Fin 4 ⊕ κ => if x ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) then (-1 : K) else 1) := by
      rw [CFSG.ClassicalGroups.Orthogonal.negCoordGL, TauCeti.diagGL_coe]
      congr 1
      funext x
      by_cases hx : x ∈ ({i, j} : Finset (Fin 4 ⊕ κ))
      · simp [hx]
      · simp [hx]
    have hcomm : Commute
        (Matrix.diagonal
          (fun x : Fin 4 ⊕ κ => if x ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) then (-1 : K) else 1))
        (g : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) := by
      rw [Commute]
      have hval := congrArg
        (fun u : GL (Fin 4 ⊕ κ) K => (u : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K)) (hc _ hmem)
      simp only [Units.val_mul] at hval
      rw [hdiagz] at hval
      exact hval.symm
    have hne : (fun x : Fin 4 ⊕ κ =>
          if x ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) then (-1 : K) else 1) k ≠
        (fun x : Fin 4 ⊕ κ =>
          if x ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) then (-1 : K) else 1) l := by
      have hkiff : k ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) ↔
          ¬ (l ∈ ({i, j} : Finset (Fin 4 ⊕ κ))) := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hiff
      by_cases hk : k ∈ ({i, j} : Finset (Fin 4 ⊕ κ))
      · have hl : l ∉ ({i, j} : Finset (Fin 4 ⊕ κ)) := hkiff.mp hk
        simp only [hk, hl, if_true, if_false]
        exact fun h => uc22s2112r34q35_one_ne_neg_one h2 h.symm
      · have hl : l ∈ ({i, j} : Finset (Fin 4 ⊕ κ)) := by
          by_contra hl
          exact hk (hkiff.mpr hl)
        simp only [hk, hl, if_true, if_false]
        exact fun h => uc22s2112r34q35_one_ne_neg_one h2 h
    exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm hne

private theorem uc22s2112r34q35_pair_sep_seven :
    ∀ k l : Fin 4 ⊕ Fin 3, k ≠ l → ∃ i j : Fin 4 ⊕ Fin 3,
      i ≠ .inr 2 ∧ j ≠ .inr 2 ∧ i ≠ j ∧
        ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)) := by
  decide

private theorem uc22s2112r34q35_pair_sep_eight :
    ∀ k l : Fin 4 ⊕ Fin 4, k ≠ l → ∃ i j : Fin 4 ⊕ Fin 4,
      i ≠ .inr 3 ∧ j ≠ .inr 3 ∧ i ≠ j ∧
        ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)) := by
  decide

private theorem uc22s2112r34q35_diag_comp_eq {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {g : GL ι K} {d : ι → K} (hdg : (g : Matrix ι ι K) = Matrix.diagonal d)
    (σ : Equiv.Perm ι)
    (hcomm : g * TauCeti.permutationGL (k := K) σ =
      TauCeti.permutationGL (k := K) σ * g) :
    d ∘ σ = d := by
  funext i
  have hunit : (TauCeti.permutationGL (k := K) σ)⁻¹ * g *
      TauCeti.permutationGL (k := K) σ = g := by
    calc (TauCeti.permutationGL (k := K) σ)⁻¹ * g * TauCeti.permutationGL (k := K) σ
        = (TauCeti.permutationGL (k := K) σ)⁻¹ *
            (g * TauCeti.permutationGL (k := K) σ) := by rw [mul_assoc]
      _ = (TauCeti.permutationGL (k := K) σ)⁻¹ *
            (TauCeti.permutationGL (k := K) σ * g) := by rw [hcomm]
      _ = g := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : (g : Matrix ι ι K) (σ i) (σ i) = (g : Matrix ι ι K) i i := by
    rw [← TauCeti.coe_permutationGL_inv_mul_mul_permutationGL_apply (k := K) σ g i i, hunit]
  rw [hdg] at h1
  simpa [Matrix.diagonal_apply_eq] using h1

private theorem uc22s2112r34q35_Q7_single {K : Type} [Field K] (e : K)
    (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_Q7 e (Pi.single l (1 : K)) = if l = .inr 2 then e else 1 := by
  rcases l with i | i
  · fin_cases i <;> simp [uc22s2112r34q35_Q7, Pi.single_apply]
  · fin_cases i <;> simp [uc22s2112r34q35_Q7]

private theorem uc22s2112r34q35_Q7_single_mul {K : Type} [Field K] (e c : K)
    (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_Q7 e (Pi.single l c) =
      (if l = .inr 2 then e else 1) * c ^ 2 := by
  rcases l with i | i
  · fin_cases i <;> simp [uc22s2112r34q35_Q7, Pi.single_apply]
  · fin_cases i <;> simp [uc22s2112r34q35_Q7]

private theorem uc22s2112r34q35_Q8_single {K : Type} [Field K] (e : K)
    (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_Q8 e (Pi.single l (1 : K)) = if l = .inr 3 then e else 1 := by
  rcases l with i | i
  · fin_cases i <;> simp [uc22s2112r34q35_Q8, Pi.single_apply]
  · fin_cases i <;> simp [uc22s2112r34q35_Q8]

private theorem uc22s2112r34q35_Q8_single_mul {K : Type} [Field K] (e c : K)
    (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_Q8 e (Pi.single l c) =
      (if l = .inr 3 then e else 1) * c ^ 2 := by
  rcases l with i | i
  · fin_cases i <;> simp [uc22s2112r34q35_Q8, Pi.single_apply]
  · fin_cases i <;> simp [uc22s2112r34q35_Q8]

private theorem uc22s2112r34q35_Q7_elim_left {K : Type} [Field K] (e : K) (w : Fin 4 → K) :
    uc22s2112r34q35_Q7 e (Sum.elim w (0 : Fin 3 → K)) = ∑ i, w i ^ 2 := by
  simp [uc22s2112r34q35_Q7]

private theorem uc22s2112r34q35_Q7_elim_right {K : Type} [Field K] (e : K) (y : Fin 3 → K) :
    uc22s2112r34q35_Q7 e (Sum.elim (0 : Fin 4 → K) y) =
      y 0 ^ 2 + y 1 ^ 2 + e * y 2 ^ 2 := by
  simp [uc22s2112r34q35_Q7]

private theorem uc22s2112r34q35_Q8_elim_left {K : Type} [Field K] (e : K) (w : Fin 4 → K) :
    uc22s2112r34q35_Q8 e (Sum.elim w (0 : Fin 4 → K)) = ∑ i, w i ^ 2 := by
  simp [uc22s2112r34q35_Q8]

private theorem uc22s2112r34q35_Q8_elim_right {K : Type} [Field K] (e : K) (y : Fin 4 → K) :
    uc22s2112r34q35_Q8 e (Sum.elim (0 : Fin 4 → K) y) =
      y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + e * y 3 ^ 2 := by
  simp [uc22s2112r34q35_Q8]

private theorem uc22s2112r34q35_diagonal_mulVec_single_one {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → K) (l : ι) :
    Matrix.mulVec (Matrix.diagonal d) (Pi.single l (1 : K)) = Pi.single l (d l) := by
  funext x
  rw [Matrix.mulVec_diagonal, Pi.single_apply, Pi.single_apply]
  by_cases hx : x = l
  · subst hx
    simp
  · simp [hx]

private noncomputable abbrev uc22s2112r34q35_E7 {K : Type} [Field K] (e : K) :
    Subgroup (GL (Fin 4 ⊕ Fin 3) K) :=
  uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e)

private noncomputable abbrev uc22s2112r34q35_E8 {K : Type} [Field K] (e : K) :
    Subgroup (GL (Fin 4 ⊕ Fin 4) K) :=
  uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e)

private noncomputable def uc22s2112r34q35_centerFinset {K : Type} [Field K] [Finite K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (E : Subgroup (GL ι K)) : Finset (GL ι K) := by
  classical
  letI : Fintype (GL ι K) := Fintype.ofFinite _
  exact Finset.univ.filter (fun g => g ∈ E ∧ ∀ t ∈ E, g * t = t * g)

private theorem uc22s2112r34q35_mem_centerFinset {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : Subgroup (GL ι K)} {g : GL ι K} :
    g ∈ uc22s2112r34q35_centerFinset E ↔ g ∈ E ∧ ∀ t ∈ E, g * t = t * g := by
  classical
  unfold uc22s2112r34q35_centerFinset
  simp [Finset.mem_filter]

private noncomputable def uc22s2112r34q35_flagMap7 {K : Type} [Field K]
    (g : GL (Fin 4 ⊕ Fin 3) K) : Bool × Bool :=
  (uc22s2112r34q35_signFlag
      ((g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) (.inl 0) (.inl 0)),
    uc22s2112r34q35_signFlag
      ((g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) (.inr 0) (.inr 0)))

private noncomputable def uc22s2112r34q35_flagMap8 {K : Type} [Field K]
    (g : GL (Fin 4 ⊕ Fin 4) K) : Bool × Bool × Bool :=
  (uc22s2112r34q35_signFlag
      ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inl 0) (.inl 0)),
    uc22s2112r34q35_signFlag
      ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inr 0) (.inr 0)),
    uc22s2112r34q35_signFlag
      ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inr 2) (.inr 2)))

private theorem uc22s2112r34q35_structure_seven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0) {g : GL (Fin 4 ⊕ Fin 3) K}
    (hgE : g ∈ uc22s2112r34q35_E7 e)
    (hc : ∀ t ∈ uc22s2112r34q35_E7 e, g * t = t * g) :
    ∃ a b : Bool, (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) =
      Matrix.diagonal (Sum.elim (fun _ : Fin 4 => uc22s2112r34q35_signK a)
        (fun j : Fin 3 => if j = 2 then (1 : K) else uc22s2112r34q35_signK b)) := by
  classical
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  have hsep : ∀ k l : Fin 4 ⊕ Fin 3, k ≠ l → ∃ i j : Fin 4 ⊕ Fin 3,
      CFSG.ClassicalGroups.Orthogonal.negCoordGL ({i, j} : Finset (Fin 4 ⊕ Fin 3)) ∈
        uc22s2112r34q35_E7 e ∧ i ≠ j ∧
        ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)) := by
    intro k l hkl
    obtain ⟨i, j, hi, hj, hij, hiff⟩ := uc22s2112r34q35_pair_sep_seven k l hkl
    exact ⟨i, j, uc22s2112r34q35_negPair_mem_T7 e hi hj hij, hij, hiff⟩
  obtain ⟨d, hdg⟩ : ∃ d : Fin 4 ⊕ Fin 3 → K,
      (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) = Matrix.diagonal d :=
    ⟨_, uc22s2112r34q35_diagonal_of_commute (κ := Fin 3) (E := uc22s2112r34q35_E7 e)
      (g := g) h2 hsep hc⟩
  have hiso : ∀ v : Fin 4 ⊕ Fin 3 → K,
      uc22s2112r34q35_Q7 e
          (Matrix.mulVec (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) v) =
        uc22s2112r34q35_Q7 e v :=
    CFSG.PGLModel.mem_orthogonalGroup_iff.mp
      (uc22s2112r34q35_statedOmega_le (uc22s2112r34q35_Q7 e) hgE.2)
  have hsq : ∀ l : Fin 4 ⊕ Fin 3, d l ^ 2 = 1 := by
    intro l
    have h := hiso (Pi.single l (1 : K))
    rw [hdg, uc22s2112r34q35_diagonal_mulVec_single_one,
      uc22s2112r34q35_Q7_single_mul, uc22s2112r34q35_Q7_single] at h
    have hcoef : (if l = .inr 2 then e else 1) ≠ 0 := by
      by_cases hl : l = .inr 2
      · simp [hl, he]
      · simp [hl]
    have h' : (if l = .inr 2 then e else 1) * d l ^ 2 =
        (if l = .inr 2 then e else 1) * 1 := by
      simpa using h
    exact mul_left_cancel₀ hcoef h'
  have hdval : ∀ l : Fin 4 ⊕ Fin 3, d l = 1 ∨ d l = -1 := fun l =>
    sq_eq_one_iff.mp (hsq l)
  have hP0 : d ∘ uc22s2112r34q35_permTest (Fin 3) 0 1 0 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T7 e 0))
  have hP1 : d ∘ uc22s2112r34q35_permTest (Fin 3) 0 1 1 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T7 e 1))
  have hP2 : d ∘ uc22s2112r34q35_permTest (Fin 3) 0 1 2 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T7 e 2))
  have h01 : d (.inl 1) = d (.inl 0) := by
    have h := congrFun hP0 (.inl 0)
    have hσ : uc22s2112r34q35_permTest (Fin 3) 0 1 0 (.inl 0) = .inl 1 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have h20 : d (.inl 2) = d (.inl 0) := by
    have h := congrFun hP1 (.inl 0)
    have hσ : uc22s2112r34q35_permTest (Fin 3) 0 1 1 (.inl 0) = .inl 2 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have h31 : d (.inl 3) = d (.inl 1) := by
    have h := congrFun hP1 (.inl 1)
    have hσ : uc22s2112r34q35_permTest (Fin 3) 0 1 1 (.inl 1) = .inl 3 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have hκ : d (.inr 1) = d (.inr 0) := by
    have h := congrFun hP2 (.inr 0)
    have hσ : uc22s2112r34q35_permTest (Fin 3) 0 1 2 (.inr 0) = .inr 1 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have hfour : ∀ i : Fin 4, d (.inl i) = d (.inl 0) := by
    intro i
    fin_cases i
    · rfl
    · exact h01
    · exact h20
    · exact h31.trans h01
  have hdet : (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K).det = 1 :=
    uc22s2112r34q35_det_eq_one_of_mem_statedOmega hgE.2
  rw [hdg, Matrix.det_diagonal] at hdet
  have hprod4 : ∏ i : Fin 4, d (.inl i) = d (.inl 0) ^ 4 := by
    rw [show ∏ i : Fin 4, d (.inl i) = ∏ _ : Fin 4, d (.inl 0) from
      Finset.prod_congr rfl (fun i _ => hfour i)]
    exact Fin.prod_const 4 _
  rw [Fintype.prod_sum_type (f := d), hprod4, Fin.prod_univ_three, hκ] at hdet
  have ha2 : d (.inl 0) * d (.inl 0) = 1 := by
    have h := hsq (.inl 0)
    rwa [pow_two] at h
  have hb2 : d (.inr 0) * d (.inr 0) = 1 := by
    have h := hsq (.inr 0)
    rwa [pow_two] at h
  have hc1 : d (.inr 2) = 1 := by
    have ha4 : d (.inl 0) ^ 4 = 1 := by
      have h2' : d (.inl 0) ^ 2 = 1 := by rw [pow_two, ha2]
      calc d (.inl 0) ^ 4 = (d (.inl 0) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [h2', one_pow]
    have h := hdet
    rw [ha4, hb2] at h
    simpa using h
  have hsa : uc22s2112r34q35_signK (uc22s2112r34q35_signFlag (d (.inl 0))) =
      d (.inl 0) := by
    rcases hdval (.inl 0) with h | h
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
        uc22s2112r34q35_one_ne_neg_one h2]
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]
  have hsb : uc22s2112r34q35_signK (uc22s2112r34q35_signFlag (d (.inr 0))) =
      d (.inr 0) := by
    rcases hdval (.inr 0) with h | h
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
        uc22s2112r34q35_one_ne_neg_one h2]
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]
  refine ⟨uc22s2112r34q35_signFlag (d (.inl 0)),
    uc22s2112r34q35_signFlag (d (.inr 0)), ?_⟩
  rw [hdg, Matrix.diagonal_eq_diagonal_iff]
  intro l
  rcases l with i | j
  · rw [hfour i]
    exact hsa.symm
  · fin_cases j
    · simpa using hsb.symm
    · simpa [hκ] using hsb.symm
    · simpa using hc1

private theorem uc22s2112r34q35_structure_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0) {g : GL (Fin 4 ⊕ Fin 4) K}
    (hgE : g ∈ uc22s2112r34q35_E8 e)
    (hc : ∀ t ∈ uc22s2112r34q35_E8 e, g * t = t * g) :
    ∃ a b c : Bool, (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      Matrix.diagonal (Sum.elim (fun _ : Fin 4 => uc22s2112r34q35_signK a)
        (fun j : Fin 4 => if j = 0 ∨ j = 1 then uc22s2112r34q35_signK b
          else uc22s2112r34q35_signK c)) := by
  classical
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  have hsep : ∀ k l : Fin 4 ⊕ Fin 4, k ≠ l → ∃ i j : Fin 4 ⊕ Fin 4,
      CFSG.ClassicalGroups.Orthogonal.negCoordGL ({i, j} : Finset (Fin 4 ⊕ Fin 4)) ∈
        uc22s2112r34q35_E8 e ∧ i ≠ j ∧
        ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)) := by
    intro k l hkl
    obtain ⟨i, j, hi, hj, hij, hiff⟩ := uc22s2112r34q35_pair_sep_eight k l hkl
    exact ⟨i, j, uc22s2112r34q35_negPair_mem_T8 e hi hj hij, hij, hiff⟩
  obtain ⟨d, hdg⟩ : ∃ d : Fin 4 ⊕ Fin 4 → K,
      (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = Matrix.diagonal d :=
    ⟨_, uc22s2112r34q35_diagonal_of_commute (κ := Fin 4) (E := uc22s2112r34q35_E8 e)
      (g := g) h2 hsep hc⟩
  have hiso : ∀ v : Fin 4 ⊕ Fin 4 → K,
      uc22s2112r34q35_Q8 e
          (Matrix.mulVec (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) v) =
        uc22s2112r34q35_Q8 e v :=
    CFSG.PGLModel.mem_orthogonalGroup_iff.mp
      (uc22s2112r34q35_statedOmega_le (uc22s2112r34q35_Q8 e) hgE.2)
  have hsq : ∀ l : Fin 4 ⊕ Fin 4, d l ^ 2 = 1 := by
    intro l
    have h := hiso (Pi.single l (1 : K))
    rw [hdg, uc22s2112r34q35_diagonal_mulVec_single_one,
      uc22s2112r34q35_Q8_single_mul, uc22s2112r34q35_Q8_single] at h
    have hcoef : (if l = .inr 3 then e else 1) ≠ 0 := by
      by_cases hl : l = .inr 3
      · simp [hl, he]
      · simp [hl]
    have h' : (if l = .inr 3 then e else 1) * d l ^ 2 =
        (if l = .inr 3 then e else 1) * 1 := by
      simpa using h
    exact mul_left_cancel₀ hcoef h'
  have hdval : ∀ l : Fin 4 ⊕ Fin 4, d l = 1 ∨ d l = -1 := fun l =>
    sq_eq_one_iff.mp (hsq l)
  have hP0 : d ∘ uc22s2112r34q35_permTest (Fin 4) 0 1 0 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T8 e 0))
  have hP1 : d ∘ uc22s2112r34q35_permTest (Fin 4) 0 1 1 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T8 e 1))
  have hP2 : d ∘ uc22s2112r34q35_permTest (Fin 4) 0 1 2 = d :=
    uc22s2112r34q35_diag_comp_eq hdg _ (hc _ (uc22s2112r34q35_permTest_mem_T8 e 2))
  have h01 : d (.inl 1) = d (.inl 0) := by
    have h := congrFun hP0 (.inl 0)
    have hσ : uc22s2112r34q35_permTest (Fin 4) 0 1 0 (.inl 0) = .inl 1 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have h20 : d (.inl 2) = d (.inl 0) := by
    have h := congrFun hP1 (.inl 0)
    have hσ : uc22s2112r34q35_permTest (Fin 4) 0 1 1 (.inl 0) = .inl 2 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have h31 : d (.inl 3) = d (.inl 1) := by
    have h := congrFun hP1 (.inl 1)
    have hσ : uc22s2112r34q35_permTest (Fin 4) 0 1 1 (.inl 1) = .inl 3 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have hκ : d (.inr 1) = d (.inr 0) := by
    have h := congrFun hP2 (.inr 0)
    have hσ : uc22s2112r34q35_permTest (Fin 4) 0 1 2 (.inr 0) = .inr 1 := by decide
    simp only [Function.comp_apply] at h
    rwa [hσ] at h
  have hfour : ∀ i : Fin 4, d (.inl i) = d (.inl 0) := by
    intro i
    fin_cases i
    · rfl
    · exact h01
    · exact h20
    · exact h31.trans h01
  have hdet : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).det = 1 :=
    uc22s2112r34q35_det_eq_one_of_mem_statedOmega hgE.2
  rw [hdg, Matrix.det_diagonal] at hdet
  have hprod4 : ∏ i : Fin 4, d (.inl i) = d (.inl 0) ^ 4 := by
    rw [show ∏ i : Fin 4, d (.inl i) = ∏ _ : Fin 4, d (.inl 0) from
      Finset.prod_congr rfl (fun i _ => hfour i)]
    exact Fin.prod_const 4 _
  rw [Fintype.prod_sum_type (f := d), hprod4, Fin.prod_univ_four, hκ] at hdet
  have ha2 : d (.inl 0) * d (.inl 0) = 1 := by
    have h := hsq (.inl 0)
    rwa [pow_two] at h
  have hb2 : d (.inr 0) * d (.inr 0) = 1 := by
    have h := hsq (.inr 0)
    rwa [pow_two] at h
  have hc2 : d (.inr 2) * d (.inr 2) = 1 := by
    have h := hsq (.inr 2)
    rwa [pow_two] at h
  have hcc' : d (.inr 2) * d (.inr 3) = 1 := by
    have ha4 : d (.inl 0) ^ 4 = 1 := by
      have h2' : d (.inl 0) ^ 2 = 1 := by rw [pow_two, ha2]
      calc d (.inl 0) ^ 4 = (d (.inl 0) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [h2', one_pow]
    have h := hdet
    rw [ha4, hb2] at h
    simpa using h
  have hc'eq : d (.inr 3) = d (.inr 2) := by
    calc d (.inr 3) = 1 * d (.inr 3) := by rw [one_mul]
      _ = (d (.inr 2) * d (.inr 2)) * d (.inr 3) := by rw [hc2]
      _ = d (.inr 2) * (d (.inr 2) * d (.inr 3)) := by rw [mul_assoc]
      _ = d (.inr 2) * 1 := by rw [hcc']
      _ = d (.inr 2) := mul_one _
  have hsa : uc22s2112r34q35_signK (uc22s2112r34q35_signFlag (d (.inl 0))) =
      d (.inl 0) := by
    rcases hdval (.inl 0) with h | h
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
        uc22s2112r34q35_one_ne_neg_one h2]
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]
  have hsb : uc22s2112r34q35_signK (uc22s2112r34q35_signFlag (d (.inr 0))) =
      d (.inr 0) := by
    rcases hdval (.inr 0) with h | h
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
        uc22s2112r34q35_one_ne_neg_one h2]
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]
  have hsc : uc22s2112r34q35_signK (uc22s2112r34q35_signFlag (d (.inr 2))) =
      d (.inr 2) := by
    rcases hdval (.inr 2) with h | h
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK,
        uc22s2112r34q35_one_ne_neg_one h2]
    · rw [h]
      simp [uc22s2112r34q35_signFlag, uc22s2112r34q35_signK]
  refine ⟨uc22s2112r34q35_signFlag (d (.inl 0)),
    uc22s2112r34q35_signFlag (d (.inr 0)),
    uc22s2112r34q35_signFlag (d (.inr 2)), ?_⟩
  rw [hdg, Matrix.diagonal_eq_diagonal_iff]
  intro l
  rcases l with i | j
  · rw [hfour i]
    exact hsa.symm
  · fin_cases j
    · simpa using hsb.symm
    · simpa [hκ] using hsb.symm
    · simpa using hsc.symm
    · simpa [hc'eq] using hsc.symm

private theorem uc22s2112r34q35_z1_coe {κ : Type} [Fintype κ] [DecidableEq κ] {K : Type}
    [Field K] :
    ((uc22s2112r34q35_z1 κ K : GL (Fin 4 ⊕ κ) K) :
        Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) =
      Matrix.diagonal (Sum.elim (fun _ => (-1 : K)) (fun _ => 1)) := by
  rw [uc22s2112r34q35_z1, TauCeti.diagGL_coe, Matrix.diagonal_eq_diagonal_iff]
  intro l
  rcases l with i | j <;> simp

private theorem uc22s2112r34q35_neg_one_coe {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] :
    ((-1 : GL ι K) : Matrix ι ι K) = Matrix.diagonal (fun _ => (-1 : K)) := by
  rw [Units.val_neg, Units.val_one]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

private theorem uc22s2112r34q35_neg_one_mul {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (g : GL ι K) : (-1 : GL ι K) * g = g * (-1) := by
  refine Units.ext ?_
  simp only [Units.val_mul, Units.val_neg, Units.val_one]
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]

private theorem uc22s2112r34q35_conj_neg_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (h : GL ι K) : h⁻¹ * (-1) * h = -1 := by
  rw [mul_assoc, uc22s2112r34q35_neg_one_mul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem uc22s2112r34q35_fromBlocks_of_commute_z1 {κ : Type} [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {h : GL (Fin 4 ⊕ κ) K}
    (hcomm : h * uc22s2112r34q35_z1 κ K = uc22s2112r34q35_z1 κ K * h) :
    (h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) =
      Matrix.fromBlocks ((h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K).toBlocks₁₁) 0 0
        ((h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K).toBlocks₂₂) := by
  have hZ := uc22s2112r34q35_z1_coe (κ := κ) (K := K)
  have hval := congrArg (fun u : GL (Fin 4 ⊕ κ) K =>
    (u : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K)) hcomm
  simp only [Units.val_mul] at hval
  rw [hZ] at hval
  have hcomm' : Commute (Matrix.diagonal (Sum.elim (fun _ => (-1 : K)) (fun _ => 1)))
      (h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) := hval.symm
  have h12 : ∀ (i : Fin 4) (j : κ),
      (h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) (.inl i) (.inr j) = 0 := by
    intro i j
    refine TauCeti.apply_eq_zero_of_commute_diagonal hcomm' ?_
    simpa using (uc22s2112r34q35_one_ne_neg_one h2).symm
  have h21 : ∀ (j : κ) (i : Fin 4),
      (h : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) K) (.inr j) (.inl i) = 0 := by
    intro j i
    refine TauCeti.apply_eq_zero_of_commute_diagonal hcomm' ?_
    simpa using uc22s2112r34q35_one_ne_neg_one h2
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.toBlocks₁₁]
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact h12 i j
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    exact h21 i j
  · simp [Matrix.toBlocks₂₂]

private theorem uc22s2112r34q35_fromBlocks_pow {κ : Type} [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix κ κ K) (n : ℕ) :
    (Matrix.fromBlocks A 0 0 B) ^ n = Matrix.fromBlocks (A ^ n) 0 0 (B ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, Matrix.fromBlocks_one]
  | succ n ih =>
    rw [pow_succ', ih, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_zero, Matrix.zero_mul, pow_succ']

private theorem uc22s2112r34q35_fromBlocks_mulVec_left {κ : Type} [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] {A : Matrix (Fin 4) (Fin 4) K} {D : Matrix κ κ K} (v : Fin 4 → K) :
    Matrix.mulVec (Matrix.fromBlocks A 0 0 D) (Sum.elim v (0 : κ → K)) =
      Sum.elim (Matrix.mulVec A v) (0 : κ → K) := by
  rw [Matrix.fromBlocks_mulVec]
  ext l
  rcases l with i | j <;> simp

private theorem uc22s2112r34q35_fromBlocks_mulVec_right {κ : Type} [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] {A : Matrix (Fin 4) (Fin 4) K} {D : Matrix κ κ K} (v : κ → K) :
    Matrix.mulVec (Matrix.fromBlocks A 0 0 D) (Sum.elim (0 : Fin 4 → K) v) =
      Sum.elim (0 : Fin 4 → K) (Matrix.mulVec D v) := by
  rw [Matrix.fromBlocks_mulVec]
  ext l
  rcases l with i | j <;> simp

private theorem uc22s2112r34q35_flagMap7_of_structure {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {g : GL (Fin 4 ⊕ Fin 3) K} {a b : Bool}
    (hm : (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) =
      Matrix.diagonal (Sum.elim (fun _ : Fin 4 => uc22s2112r34q35_signK a)
        (fun j : Fin 3 => if j = 2 then (1 : K) else uc22s2112r34q35_signK b))) :
    uc22s2112r34q35_flagMap7 g = (a, b) := by
  unfold uc22s2112r34q35_flagMap7
  have h1 : (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) (.inl 0) (.inl 0) =
      uc22s2112r34q35_signK a := by
    rw [hm, Matrix.diagonal_apply_eq]
    simp
  have h2' : (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) (.inr 0) (.inr 0) =
      uc22s2112r34q35_signK b := by
    rw [hm, Matrix.diagonal_apply_eq]
    simp
  rw [h1, h2', uc22s2112r34q35_signFlag_signK h2, uc22s2112r34q35_signFlag_signK h2]

private theorem uc22s2112r34q35_flagMap8_of_structure {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {g : GL (Fin 4 ⊕ Fin 4) K} {a b c : Bool}
    (hm : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      Matrix.diagonal (Sum.elim (fun _ : Fin 4 => uc22s2112r34q35_signK a)
        (fun j : Fin 4 => if j = 0 ∨ j = 1 then uc22s2112r34q35_signK b
          else uc22s2112r34q35_signK c))) :
    uc22s2112r34q35_flagMap8 g = (a, b, c) := by
  unfold uc22s2112r34q35_flagMap8
  have h1 : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inl 0) (.inl 0) =
      uc22s2112r34q35_signK a := by
    rw [hm, Matrix.diagonal_apply_eq]
    simp
  have h2' : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inr 0) (.inr 0) =
      uc22s2112r34q35_signK b := by
    rw [hm, Matrix.diagonal_apply_eq]
    simp
  have h3 : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (.inr 2) (.inr 2) =
      uc22s2112r34q35_signK c := by
    rw [hm, Matrix.diagonal_apply_eq]
    simp
  rw [h1, h2', h3, uc22s2112r34q35_signFlag_signK h2, uc22s2112r34q35_signFlag_signK h2,
    uc22s2112r34q35_signFlag_signK h2]

private theorem uc22s2112r34q35_flagMap7_inj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0)
    {g g' : GL (Fin 4 ⊕ Fin 3) K}
    (hg : g ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E7 e))
    (hg' : g' ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E7 e))
    (hflag : uc22s2112r34q35_flagMap7 g = uc22s2112r34q35_flagMap7 g') : g = g' := by
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  obtain ⟨hgE, hgcen⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mp hg
  obtain ⟨hgE', hgcen'⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mp hg'
  obtain ⟨a, b, hm⟩ := uc22s2112r34q35_structure_seven hK he hgE hgcen
  obtain ⟨a', b', hm'⟩ := uc22s2112r34q35_structure_seven hK he hgE' hgcen'
  have hpair : (a, b) = (a', b') := by
    rw [← uc22s2112r34q35_flagMap7_of_structure h2 hm,
      ← uc22s2112r34q35_flagMap7_of_structure h2 hm']
    exact hflag
  obtain ⟨haa, hbb⟩ := (Prod.mk.injEq a b a' b').mp hpair
  subst haa
  subst hbb
  exact Units.ext (hm.trans hm'.symm)

private theorem uc22s2112r34q35_flagMap7_eq_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0)
    {g : GL (Fin 4 ⊕ Fin 3) K}
    (hg : g ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E7 e))
    (hflag : uc22s2112r34q35_flagMap7 g = (false, false)) : g = 1 := by
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  obtain ⟨hgE, hgcen⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mp hg
  obtain ⟨a, b, hm⟩ := uc22s2112r34q35_structure_seven hK he hgE hgcen
  have hpair : (a, b) = (false, false) := by
    rw [← uc22s2112r34q35_flagMap7_of_structure h2 hm]
    exact hflag
  obtain ⟨ha, hb⟩ := (Prod.mk.injEq a b false false).mp hpair
  have hmat : (g : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) = 1 := by
    rw [hm, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    intro l
    rcases l with i | j
    · simp [ha, uc22s2112r34q35_signK]
    · fin_cases j <;> simp [hb, uc22s2112r34q35_signK]
  exact Units.ext hmat

private theorem uc22s2112r34q35_flagMap8_inj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0)
    {g g' : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e))
    (hg' : g' ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e))
    (hflag : uc22s2112r34q35_flagMap8 g = uc22s2112r34q35_flagMap8 g') : g = g' := by
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  obtain ⟨hgE, hgcen⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mp hg
  obtain ⟨hgE', hgcen'⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mp hg'
  obtain ⟨a, b, c, hm⟩ := uc22s2112r34q35_structure_eight hK he hgE hgcen
  obtain ⟨a', b', c', hm'⟩ := uc22s2112r34q35_structure_eight hK he hgE' hgcen'
  have htriple : (a, b, c) = (a', b', c') := by
    rw [← uc22s2112r34q35_flagMap8_of_structure h2 hm,
      ← uc22s2112r34q35_flagMap8_of_structure h2 hm']
    exact hflag
  have hab : (a, b) = (a', b') := by
    have := congrArg (fun p : Bool × Bool × Bool => (p.1, p.2.1)) htriple
    simpa using this
  have hcc : c = c' := by
    have := congrArg (fun p : Bool × Bool × Bool => p.2.2) htriple
    simpa using this
  obtain ⟨haa, hbb⟩ := (Prod.mk.injEq a b a' b').mp hab
  subst haa
  subst hbb
  subst hcc
  exact Units.ext (hm.trans hm'.symm)

private theorem uc22s2112r34q35_flagMap8_eq_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0)
    {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e))
    (hflag : uc22s2112r34q35_flagMap8 g = (false, false, false)) : g = 1 := by
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  obtain ⟨hgE, hgcen⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mp hg
  obtain ⟨a, b, c, hm⟩ := uc22s2112r34q35_structure_eight hK he hgE hgcen
  have htriple : (a, b, c) = (false, false, false) := by
    rw [← uc22s2112r34q35_flagMap8_of_structure h2 hm]
    exact hflag
  have habc : a = false ∧ b = false ∧ c = false := by
    simpa using htriple
  have hmat : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = 1 := by
    rw [hm, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    intro l
    rcases l with i | j
    · simp [habc.1, uc22s2112r34q35_signK]
    · fin_cases j <;> simp [habc.2.1, habc.2.2, uc22s2112r34q35_signK]
  exact Units.ext hmat

private theorem uc22s2112r34q35_flagMap8_eq_neg_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0)
    {g : GL (Fin 4 ⊕ Fin 4) K}
    (hg : g ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e))
    (hflag : uc22s2112r34q35_flagMap8 g = (true, true, true)) : g = -1 := by
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  obtain ⟨hgE, hgcen⟩ :=
    (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mp hg
  obtain ⟨a, b, c, hm⟩ := uc22s2112r34q35_structure_eight hK he hgE hgcen
  have htriple : (a, b, c) = (true, true, true) := by
    rw [← uc22s2112r34q35_flagMap8_of_structure h2 hm]
    exact hflag
  have habc : a = true ∧ b = true ∧ c = true := by
    simpa using htriple
  have hmat : (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      ((-1 : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
    rw [hm, uc22s2112r34q35_neg_one_coe, Matrix.diagonal_eq_diagonal_iff]
    intro l
    rcases l with i | j
    · simp [habc.1, uc22s2112r34q35_signK]
    · fin_cases j <;> simp [habc.2.1, habc.2.2, uc22s2112r34q35_signK]
  exact Units.ext hmat

theorem uc22s2112r34q35_eq_one_of_normalizes_T7 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0) {s : ℕ} (hs : s.Prime)
    (hs7 : 7 ≤ s) (hs13 : s ≠ 13) {h : GL (Fin 4 ⊕ Fin 3) K}
    (hΩ : h ∈ StatedOmega (uc22s2112r34q35_Q7 e)) (hh : h ^ s = 1)
    (hN : ∀ g ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e),
      h * g * h⁻¹ ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e))
    (hN' : ∀ g ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e),
      h⁻¹ * g * h ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e)) :
    h = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  set C : Finset (GL (Fin 4 ⊕ Fin 3) K) :=
    (uc22s2112r34q35_centerFinset (uc22s2112r34q35_E7 e)).filter
      (fun g => g ≠ 1 ∧ g ≠ -1) with hC
  have hCmem : ∀ a ∈ C, a ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E7 e) ∧
      a ≠ 1 ∧ a ≠ -1 := by
    intro a ha
    rw [hC, Finset.mem_filter] at ha
    exact ha
  have hCcard : C.card ≤ 3 := by
    have hinj : Set.InjOn (uc22s2112r34q35_flagMap7)
        (↑C : Set (GL (Fin 4 ⊕ Fin 3) K)) := by
      intro g hg g' hg' hflag
      exact uc22s2112r34q35_flagMap7_inj hK he (hCmem g hg).1 (hCmem g' hg').1 hflag
    have hsub : C.image uc22s2112r34q35_flagMap7 ⊆
        (Finset.univ.erase (false, false) : Finset (Bool × Bool)) := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_erase.mpr ⟨fun hflag =>
        (hCmem g hg).2.1
          (uc22s2112r34q35_flagMap7_eq_one hK he (hCmem g hg).1 hflag), Finset.mem_univ _⟩
    have hle : C.card ≤ ((Finset.univ.erase (false, false) : Finset (Bool × Bool))).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have h3 : ((Finset.univ.erase (false, false) : Finset (Bool × Bool))).card = 3 := by decide
    omega
  have hmap : ∀ a ∈ C, h * a * h⁻¹ ∈ C := by
    intro a ha
    obtain ⟨hacenter, hane1, haneneg⟩ := hCmem a ha
    obtain ⟨haE, hacent⟩ :=
      (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mp hacenter
    have hconjE : h * a * h⁻¹ ∈ uc22s2112r34q35_E7 e := hN a haE
    have hcentral : ∀ t ∈ uc22s2112r34q35_E7 e,
        (h * a * h⁻¹) * t = t * (h * a * h⁻¹) := by
      intro t ht
      have hct := hacent _ (hN' t ht)
      calc (h * a * h⁻¹) * t = h * (a * (h⁻¹ * t * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * t * h) * a) * h⁻¹ := by rw [hct]
        _ = t * (h * a * h⁻¹) := by group
    have hconj1 : h * a * h⁻¹ ≠ 1 := by
      intro h1
      apply hane1
      have h2' : h⁻¹ * (h * a * h⁻¹) * h = a := by group
      have h3 := congrArg (fun u : GL (Fin 4 ⊕ Fin 3) K => h⁻¹ * u * h) h1
      rw [h2'] at h3
      simpa using h3
    have hconjneg : h * a * h⁻¹ ≠ -1 := by
      intro h1
      apply haneneg
      have h2' : h⁻¹ * (h * a * h⁻¹) * h = a := by group
      have h3 := congrArg (fun u : GL (Fin 4 ⊕ Fin 3) K => h⁻¹ * u * h) h1
      rw [h2', uc22s2112r34q35_conj_neg_one] at h3
      exact h3
    rw [hC, Finset.mem_filter]
    exact ⟨(uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mpr
      ⟨hconjE, hcentral⟩, hconj1, hconjneg⟩
  have hCcard' : C.card < s := by omega
  have hcommC : ∀ a ∈ C, h * a = a * h :=
    uc22s2112r34q35_commute_of_forall_conj_mem hs hh C hCcard' hmap
  have hz1C : uc22s2112r34q35_z1 (Fin 3) K ∈ C := by
    rw [hC, Finset.mem_filter]
    refine ⟨(uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E7 e)).mpr
      ⟨uc22s2112r34q35_z1_mem_T7 e, ?_⟩, ?_, ?_⟩
    · intro t ht
      exact (uc22s2112r34q35_commute_z1 ht.1).symm
    · intro h1
      have hmat : ((uc22s2112r34q35_z1 (Fin 3) K : GL (Fin 4 ⊕ Fin 3) K) :
          Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) = 1 := by rw [h1]; rfl
      rw [uc22s2112r34q35_z1_coe] at hmat
      have hentry : (-1 : K) = 1 := by
        simpa [Matrix.diagonal_apply_eq] using
          (congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 0))
      exact uc22s2112r34q35_one_ne_neg_one h2 hentry.symm
    · intro h1
      have hmat : ((uc22s2112r34q35_z1 (Fin 3) K : GL (Fin 4 ⊕ Fin 3) K) :
          Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) = (-1 : GL (Fin 4 ⊕ Fin 3) K) := by
        rw [h1]
      rw [uc22s2112r34q35_z1_coe, uc22s2112r34q35_neg_one_coe] at hmat
      have hentry : (1 : K) = -1 := by
        simpa [Matrix.diagonal_apply_eq] using
          (congrFun (congrFun hmat (Sum.inr 0)) (Sum.inr 0))
      exact uc22s2112r34q35_one_ne_neg_one h2 hentry
  have hz1comm : h * uc22s2112r34q35_z1 (Fin 3) K =
      uc22s2112r34q35_z1 (Fin 3) K * h := hcommC _ hz1C
  obtain ⟨A, B, hAB⟩ : ∃ A : Matrix (Fin 4) (Fin 4) K, ∃ B : Matrix (Fin 3) (Fin 3) K,
      (h : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) = Matrix.fromBlocks A 0 0 B :=
    ⟨_, _, uc22s2112r34q35_fromBlocks_of_commute_z1 h2 hz1comm⟩
  have hMs : (h : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) ^ s = 1 := by
    rw [← Units.val_pow_eq_pow_val, hh]
    rfl
  have hblocks : Matrix.fromBlocks (A ^ s) 0 0 (B ^ s) =
      Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) K) 0 0
        (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← uc22s2112r34q35_fromBlocks_pow A B s, ← hAB, hMs, Matrix.fromBlocks_one]
  have hAs : A ^ s = 1 := (Matrix.fromBlocks_inj.mp hblocks).1
  have hBs : B ^ s = 1 := (Matrix.fromBlocks_inj.mp hblocks).2.2.2
  have hiso : ∀ v : Fin 4 ⊕ Fin 3 → K,
      uc22s2112r34q35_Q7 e (Matrix.mulVec (h : Matrix (Fin 4 ⊕ Fin 3) (Fin 4 ⊕ Fin 3) K) v) =
        uc22s2112r34q35_Q7 e v :=
    CFSG.PGLModel.mem_orthogonalGroup_iff.mp
      (uc22s2112r34q35_statedOmega_le (uc22s2112r34q35_Q7 e) hΩ)
  have hA : ∀ v : Fin 4 → K,
      ∑ i, (fun _ : Fin 4 => (1 : K)) i * (Matrix.mulVec A v) i ^ 2 =
        ∑ i, (fun _ : Fin 4 => (1 : K)) i * v i ^ 2 := by
    intro v
    have hv := hiso (Sum.elim v 0)
    rw [hAB, uc22s2112r34q35_fromBlocks_mulVec_left (D := B)] at hv
    rw [uc22s2112r34q35_Q7_elim_left, uc22s2112r34q35_Q7_elim_left] at hv
    simpa using hv
  have hB : ∀ v : Fin 3 → K,
      ∑ i, (fun i : Fin 3 => if i = 2 then e else 1) i * (Matrix.mulVec B v) i ^ 2 =
        ∑ i, (fun i : Fin 3 => if i = 2 then e else 1) i * v i ^ 2 := by
    intro v
    have hv := hiso (Sum.elim 0 v)
    rw [hAB, uc22s2112r34q35_fromBlocks_mulVec_right (A := A) (D := B)] at hv
    rw [uc22s2112r34q35_Q7_elim_right, uc22s2112r34q35_Q7_elim_right] at hv
    simpa [Fin.sum_univ_three] using hv
  have hAeq : A = 1 :=
    uc22s2112r34q35_eq_one_of_isometry_four hK (c := fun _ : Fin 4 => (1 : K))
      (fun _ => one_ne_zero) hA hs hs7 hs13 hAs
  have hBeq : B = 1 :=
    uc22s2112r34q35_eq_one_of_isometry_three hK
      (c := fun i : Fin 3 => if i = 2 then e else 1)
      (by intro i; fin_cases i <;> simp [he]) hB hs hs7 hBs
  refine Units.ext ?_
  rw [hAB, hAeq, hBeq, Matrix.fromBlocks_one]
  rfl

theorem uc22s2112r34q35_eq_one_of_normalizes_T8 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) {e : K} (he : e ≠ 0) {s : ℕ} (hs : s.Prime)
    (hs7 : 7 ≤ s) (hs13 : s ≠ 13) {h : GL (Fin 4 ⊕ Fin 4) K}
    (hΩ : h ∈ StatedOmega (uc22s2112r34q35_Q8 e)) (hh : h ^ s = 1)
    (hN : ∀ g ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e),
      h * g * h⁻¹ ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e))
    (hN' : ∀ g ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e),
      h⁻¹ * g * h ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e)) :
    h = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := uc22s2112r34q35_two_ne_zero hK
  set C : Finset (GL (Fin 4 ⊕ Fin 4) K) :=
    (uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e)).filter
      (fun g => g ≠ 1 ∧ g ≠ -1) with hC
  have hCmem : ∀ a ∈ C, a ∈ uc22s2112r34q35_centerFinset (uc22s2112r34q35_E8 e) ∧
      a ≠ 1 ∧ a ≠ -1 := by
    intro a ha
    rw [hC, Finset.mem_filter] at ha
    exact ha
  have hCcard : C.card ≤ 6 := by
    have hinj : Set.InjOn (uc22s2112r34q35_flagMap8)
        (↑C : Set (GL (Fin 4 ⊕ Fin 4) K)) := by
      intro g hg g' hg' hflag
      exact uc22s2112r34q35_flagMap8_inj hK he (hCmem g hg).1 (hCmem g' hg').1 hflag
    have hsub : C.image uc22s2112r34q35_flagMap8 ⊆
        ((Finset.univ.erase (false, false, false)).erase (true, true, true) :
          Finset (Bool × Bool × Bool)) := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
      refine Finset.mem_erase.mpr ⟨fun hflag =>
        (hCmem g hg).2.2
          (uc22s2112r34q35_flagMap8_eq_neg_one hK he (hCmem g hg).1 hflag),
        Finset.mem_erase.mpr ⟨fun hflag =>
          (hCmem g hg).2.1
            (uc22s2112r34q35_flagMap8_eq_one hK he (hCmem g hg).1 hflag), Finset.mem_univ _⟩⟩
    have hle : C.card ≤ ((Finset.univ.erase (false, false, false)).erase (true, true, true) :
        Finset (Bool × Bool × Bool)).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have h6 : ((Finset.univ.erase (false, false, false)).erase (true, true, true) :
        Finset (Bool × Bool × Bool)).card = 6 := by decide
    omega
  have hmap : ∀ a ∈ C, h * a * h⁻¹ ∈ C := by
    intro a ha
    obtain ⟨hacenter, hane1, haneneg⟩ := hCmem a ha
    obtain ⟨haE, hacent⟩ :=
      (uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mp hacenter
    have hconjE : h * a * h⁻¹ ∈ uc22s2112r34q35_E8 e := hN a haE
    have hcentral : ∀ t ∈ uc22s2112r34q35_E8 e,
        (h * a * h⁻¹) * t = t * (h * a * h⁻¹) := by
      intro t ht
      have hct := hacent _ (hN' t ht)
      calc (h * a * h⁻¹) * t = h * (a * (h⁻¹ * t * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * t * h) * a) * h⁻¹ := by rw [hct]
        _ = t * (h * a * h⁻¹) := by group
    have hconj1 : h * a * h⁻¹ ≠ 1 := by
      intro h1
      apply hane1
      have h2' : h⁻¹ * (h * a * h⁻¹) * h = a := by group
      have h3 := congrArg (fun u : GL (Fin 4 ⊕ Fin 4) K => h⁻¹ * u * h) h1
      rw [h2'] at h3
      simpa using h3
    have hconjneg : h * a * h⁻¹ ≠ -1 := by
      intro h1
      apply haneneg
      have h2' : h⁻¹ * (h * a * h⁻¹) * h = a := by group
      have h3 := congrArg (fun u : GL (Fin 4 ⊕ Fin 4) K => h⁻¹ * u * h) h1
      rw [h2', uc22s2112r34q35_conj_neg_one] at h3
      exact h3
    rw [hC, Finset.mem_filter]
    exact ⟨(uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mpr
      ⟨hconjE, hcentral⟩, hconj1, hconjneg⟩
  have hCcard' : C.card < s := by omega
  have hcommC : ∀ a ∈ C, h * a = a * h :=
    uc22s2112r34q35_commute_of_forall_conj_mem hs hh C hCcard' hmap
  have hz1C : uc22s2112r34q35_z1 (Fin 4) K ∈ C := by
    rw [hC, Finset.mem_filter]
    refine ⟨(uc22s2112r34q35_mem_centerFinset (E := uc22s2112r34q35_E8 e)).mpr
      ⟨uc22s2112r34q35_z1_mem_T8 e, ?_⟩, ?_, ?_⟩
    · intro t ht
      exact (uc22s2112r34q35_commute_z1 ht.1).symm
    · intro h1
      have hmat : ((uc22s2112r34q35_z1 (Fin 4) K : GL (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = 1 := by rw [h1]; rfl
      rw [uc22s2112r34q35_z1_coe] at hmat
      have hentry : (-1 : K) = 1 := by
        simpa [Matrix.diagonal_apply_eq] using
          (congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 0))
      exact uc22s2112r34q35_one_ne_neg_one h2 hentry.symm
    · intro h1
      have hmat : ((uc22s2112r34q35_z1 (Fin 4) K : GL (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = (-1 : GL (Fin 4 ⊕ Fin 4) K) := by
        rw [h1]
      rw [uc22s2112r34q35_z1_coe, uc22s2112r34q35_neg_one_coe] at hmat
      have hentry : (1 : K) = -1 := by
        simpa [Matrix.diagonal_apply_eq] using
          (congrFun (congrFun hmat (Sum.inr 0)) (Sum.inr 0))
      exact uc22s2112r34q35_one_ne_neg_one h2 hentry
  have hz1comm : h * uc22s2112r34q35_z1 (Fin 4) K =
      uc22s2112r34q35_z1 (Fin 4) K * h := hcommC _ hz1C
  obtain ⟨A, B, hAB⟩ : ∃ A : Matrix (Fin 4) (Fin 4) K, ∃ B : Matrix (Fin 4) (Fin 4) K,
      (h : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = Matrix.fromBlocks A 0 0 B :=
    ⟨_, _, uc22s2112r34q35_fromBlocks_of_commute_z1 h2 hz1comm⟩
  have hMs : (h : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) ^ s = 1 := by
    rw [← Units.val_pow_eq_pow_val, hh]
    rfl
  have hblocks : Matrix.fromBlocks (A ^ s) 0 0 (B ^ s) =
      Matrix.fromBlocks (1 : Matrix (Fin 4) (Fin 4) K) 0 0
        (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [← uc22s2112r34q35_fromBlocks_pow A B s, ← hAB, hMs, Matrix.fromBlocks_one]
  have hAs : A ^ s = 1 := (Matrix.fromBlocks_inj.mp hblocks).1
  have hBs : B ^ s = 1 := (Matrix.fromBlocks_inj.mp hblocks).2.2.2
  have hiso : ∀ v : Fin 4 ⊕ Fin 4 → K,
      uc22s2112r34q35_Q8 e (Matrix.mulVec (h : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) v) =
        uc22s2112r34q35_Q8 e v :=
    CFSG.PGLModel.mem_orthogonalGroup_iff.mp
      (uc22s2112r34q35_statedOmega_le (uc22s2112r34q35_Q8 e) hΩ)
  have hA : ∀ v : Fin 4 → K,
      ∑ i, (fun _ : Fin 4 => (1 : K)) i * (Matrix.mulVec A v) i ^ 2 =
        ∑ i, (fun _ : Fin 4 => (1 : K)) i * v i ^ 2 := by
    intro v
    have hv := hiso (Sum.elim v 0)
    rw [hAB, uc22s2112r34q35_fromBlocks_mulVec_left (D := B)] at hv
    rw [uc22s2112r34q35_Q8_elim_left, uc22s2112r34q35_Q8_elim_left] at hv
    simpa using hv
  have hB : ∀ v : Fin 4 → K,
      ∑ i, (fun i : Fin 4 => if i = 3 then e else 1) i * (Matrix.mulVec B v) i ^ 2 =
        ∑ i, (fun i : Fin 4 => if i = 3 then e else 1) i * v i ^ 2 := by
    intro v
    have hv := hiso (Sum.elim 0 v)
    rw [hAB, uc22s2112r34q35_fromBlocks_mulVec_right (A := A) (D := B)] at hv
    rw [uc22s2112r34q35_Q8_elim_right, uc22s2112r34q35_Q8_elim_right] at hv
    simpa [Fin.sum_univ_four] using hv
  have hAeq : A = 1 :=
    uc22s2112r34q35_eq_one_of_isometry_four hK (c := fun _ : Fin 4 => (1 : K))
      (fun _ => one_ne_zero) hA hs hs7 hs13 hAs
  have hBeq : B = 1 :=
    uc22s2112r34q35_eq_one_of_isometry_four hK
      (c := fun i : Fin 4 => if i = 3 then e else 1)
      (by intro i; fin_cases i <;> simp [he]) hB hs hs7 hs13 hBs
  refine Units.ext ?_
  rw [hAB, hAeq, hBeq, Matrix.fromBlocks_one]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
