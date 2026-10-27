module

public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks
public import CFSG.LocalAnalysis.StandardType.CommutingOrderThreeDiag
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightGram
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightCount
public import CFSG.LocalAnalysis.StandardType.UnitaryCoreFibres

public section

namespace CFSG.StandardType

namespace UnitaryCore

open Matrix SpBlocks UnitaryWeight

variable {Γ : Type*} [Group Γ] [Finite Γ] {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type}
  [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

lemma pow_mul_eq_mul_diagonal_pow {X P : Matrix ι ι Ω} {w : ι → Ω}
    (h : X * P = P * diagonal w) (n : ℕ) :
    X ^ n * P = P * diagonal (w ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        Matrix.diagonal_mul_diagonal, pow_succ]
      rfl

lemma mul_pow_mul_eq_mul_diagonal {A B P : Matrix ι ι Ω} {a b : ι → Ω}
    (hAP : A * P = P * diagonal a) (hBP : B * P = P * diagonal b) (i j : ℕ) :
    (A ^ i * B ^ j) * P = P * diagonal (a ^ i * b ^ j) := by
  rw [Matrix.mul_assoc, pow_mul_eq_mul_diagonal_pow hBP j,
    ← Matrix.mul_assoc, pow_mul_eq_mul_diagonal_pow hAP i, Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal]
  rfl

theorem eq_one_of_commute_even (h5 : HasOrderFiveData Γ) (h7 : HasOrderSevenData Γ) (σ : Ω ≃+* Ω)
    (hσ3 : ∀ η : Ω, η ^ 3 = 1 → σ η = η) (hι : Fintype.card ι ≤ 9) {G : Matrix ι ι Ω}
    (hG : IsUnit G) (ρ : Γ →* Matrix ι ι Ω) (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G)
    {A B : Matrix ι ι Ω} (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hAB : A * B = B * A)
    (hAG : Aᵀ * G * A.map σ = G) (hBG : Bᵀ * G * B.map σ = G) (hAc : ∀ g, ρ g * A = A * ρ g)
    (hBc : ∀ g, ρ g * B = B * ρ g)
    (hnc : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → ∀ c : Ω, A ^ i * B ^ j ≠ c • 1) (g : Γ) :
    ρ g = 1 := by
  classical
  let X : Fin 2 → Matrix ι ι Ω := fun i => if i = 0 then A else B
  have hX0 : X 0 = A := by simp [X]
  have hX1 : X 1 = B := by simp [X]
  have h3X : ∀ i, X i ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [X, hA3, hB3]
  have hcommX : ∀ i j, X i * X j = X j * X i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [X, hAB]
  obtain ⟨P, w, hw3, hP⟩ := exists_diagonalizing_basis X hcommX h3X
  let a : ι → Ω := w 0
  let b : ι → Ω := w 1
  have ha3 : ∀ α, a α ^ 3 = 1 := fun α => hw3 0 α
  have hb3 : ∀ α, b α ^ 3 = 1 := fun α => hw3 1 α
  let Pm : Matrix ι ι Ω := (P : Matrix ι ι Ω)
  have hAP : A * Pm = Pm * diagonal a := by
    have h := hP 0
    rw [hX0] at h
    simpa [Pm, a] using h
  have hBP : B * Pm = Pm * diagonal b := by
    have h := hP 1
    rw [hX1] at h
    simpa [Pm, b] using h
  let Q : Matrix ι ι Ω := (P⁻¹ : GL ι Ω)
  have hPQ : Pm * Q = 1 := by
    show (P : Matrix ι ι Ω) * ((P⁻¹ : GL ι Ω) : Matrix ι ι Ω) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : Q * Pm = 1 := by
    show ((P⁻¹ : GL ι Ω) : Matrix ι ι Ω) * (P : Matrix ι ι Ω) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let H : Matrix ι ι Ω := Pmᵀ * G * Pm.map σ
  have hHu : IsUnit H :=
    isUnit_gram_weight (σ := σ) (P := Pm) (G := G) (show IsUnit Pm from P.isUnit) hG
  have hA' : Aᵀ * G * A.map σ = (1 : Ω) • G := by rw [one_smul]; exact hAG
  have hB' : Bᵀ * G * B.map σ = (1 : Ω) • G := by rw [one_smul]; exact hBG
  have hgram : ∀ {α β : ι}, H α β ≠ 0 → a α * σ (a β) = 1 ∧ b α * σ (b β) = 1 := by
    intro α β h
    have hAa := gram_weight_entry (σ := σ) (P := Pm) (X := A) (w := a) (s := 1) hA' hAP
      (by simpa [H] using h)
    have hAb := gram_weight_entry (σ := σ) (P := Pm) (X := B) (w := b) (s := 1) hB' hBP
      (by simpa [H] using h)
    exact ⟨hAa, hAb⟩
  have hpair : ∀ {α β : ι}, H α β ≠ 0 → a α * a β = 1 ∧ b α * b β = 1 := by
    intro α β h
    obtain ⟨h1, h2⟩ := hgram h
    rw [hσ3 (a β) (ha3 β)] at h1
    rw [hσ3 (b β) (hb3 β)] at h2
    exact ⟨h1, h2⟩
  let R : Γ →* Matrix ι ι Ω := conjHom hPQ hQP ρ
  have hRapply : ∀ g : Γ, R g = Q * ρ g * Pm := fun g => conjHom_apply hPQ hQP ρ g
  have hRa : ∀ g : Γ, R g * diagonal a = diagonal a * R g := by
    intro g
    have h := commute_diagonal_conj (P := Pm) (Q := Q) (X := A) (R := ρ g) (w := a) hPQ hQP hAP
      (hAc g)
    rw [hRapply g]
    exact h
  have hRb : ∀ g : Γ, R g * diagonal b = diagonal b * R g := by
    intro g
    have h := commute_diagonal_conj (P := Pm) (Q := Q) (X := B) (R := ρ g) (w := b) hPQ hQP hBP
      (hBc g)
    rw [hRapply g]
    exact h
  let c : ι → Ω × Ω := fun α => (a α, b α)
  have hc : ∀ α β, (∀ i : Fin 2, w i α = w i β) → c α = c β := by
    intro α β h
    exact Prod.ext (h 0) (h 1)
  have hMdiag : ∀ (g : Γ) (i : Fin 2), R g * diagonal (w i) = diagonal (w i) * R g := by
    intro g i
    fin_cases i
    · simpa [a] using hRa g
    · simpa [b] using hRb g
  have hQs : ∀ g k, Splits (Finset.univ.filter fun α => c α = k) (R g) := by
    intro g k
    exact splits_fibre_of_commute_diagonal (w := w) (M := R g) (hMdiag g) c hc k
  have hform : ∀ g : Γ, (R g)ᵀ * H * (R g).map σ = H := by
    intro g
    have h := transport_form (σ := σ) (P := Pm) (Q := Q) (R := ρ g) (G := G) hPQ hQP (hρ g)
    rw [hRapply g]
    simpa [H] using h
  have hHone : ∀ {α β : ι}, H α β ≠ 0 →
      (a α = 1 ∧ b α = 1 ↔ a β = 1 ∧ b β = 1) := by
    intro α β h
    obtain ⟨h1, h2⟩ := hpair h
    constructor
    · intro ⟨ha, hb⟩
      exact ⟨by rw [← h1, ha, one_mul], by rw [← h2, hb, one_mul]⟩
    · intro ⟨ha, hb⟩
      exact ⟨by rw [← h1, ha, mul_one], by rw [← h2, hb, mul_one]⟩
  let I : Ω → Ω → Finset ι := fun u v => Finset.univ.filter fun α => a α = u ∧ b α = v
  have hfilter : ∀ u v : Ω, (Finset.univ.filter fun α => c α = (u, v)) = I u v := by
    intro u v
    ext α
    simp [I, c]
  have hHsplitI : Splits (I 1 1) H := by
    intro x y hxy
    by_contra hne
    have hiff := hHone hne
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    rw [hiff] at hxy
    tauto
  have hsupp : ∀ u v : Ω, (I u v).card ≤ (I u⁻¹ v⁻¹).card := by
    intro u v
    apply card_le_card_of_isUnit_support hHu (I := I u v) (I' := I u⁻¹ v⁻¹)
    intro α hα β hβ
    by_contra hne
    have hβ' : β ∈ I u⁻¹ v⁻¹ := by
      obtain ⟨h1, h2⟩ := hpair hne
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
      exact ⟨by rw [eq_inv_of_mul_eq_one_right h1, hα.1],
        by rw [eq_inv_of_mul_eq_one_right h2, hα.2]⟩
    exact hβ hβ'
  have hsymI : ∀ u v : Ω, (I u v).card = (I u⁻¹ v⁻¹).card := by
    intro u v
    apply le_antisymm
    · exact hsupp u v
    · have h := hsupp u⁻¹ v⁻¹
      simpa [inv_inv] using h
  have hspan : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) →
      ∃ α β, a α ^ i * b α ^ j ≠ a β ^ i * b β ^ j := by
    intro i j hij
    by_contra h
    simp only [not_exists, not_not] at h
    have hne : Nonempty ι := by
      by_contra hempty
      haveI : IsEmpty ι := ⟨fun x => hempty ⟨x⟩⟩
      have hA1 : A = 1 := by
        ext x
        exact (hempty ⟨x⟩).elim
      have hbad := hnc 1 0 (by decide) 1
      exact hbad (by rw [pow_one, pow_zero, mul_one, one_smul, hA1])
    obtain ⟨α0⟩ := hne
    let c0 : Ω := a α0 ^ i * b α0 ^ j
    have hconst : (fun α => a α ^ i * b α ^ j) = fun _ => c0 := by
      funext α
      exact h α α0
    have hdiag : diagonal (fun α => a α ^ i * b α ^ j) = c0 • (1 : Matrix ι ι Ω) := by
      rw [hconst, diagonal_const_eq_smul_one]
    have hprod := mul_pow_mul_eq_mul_diagonal hAP hBP i j
    have hfun : (a ^ i * b ^ j) = (fun α => a α ^ i * b α ^ j) := rfl
    rw [hfun, hdiag, Matrix.mul_smul, Matrix.mul_one] at hprod
    have hfinal : A ^ i * B ^ j = c0 • (1 : Matrix ι ι Ω) := by
      have h := congrArg (fun M : Matrix ι ι Ω => M * Q) hprod
      simpa [Matrix.mul_assoc, hPQ, Matrix.mul_one, Matrix.smul_mul] using h
    exact hnc i j hij c0 hfinal
  obtain ⟨hbounds0, hbounds⟩ := card_fiber_bounds a b ha3 hb3 hspan hsymI
  have h11 : (I 1 1).card ≤ 5 := by
    simp only [I]
    omega
  have hother : ∀ u v : Ω, (u ≠ 1 ∨ v ≠ 1) → (I u v).card ≤ 3 := by
    intro u v huv
    have h := hbounds u v huv
    simp only [I] at h ⊢
    omega
  have hsmall : ∀ k : Ω × Ω, (Finset.univ.filter fun α => c α = k).card ≤ 3 ∨
      ((Finset.univ.filter fun α => c α = k).card ≤ 5 ∧
        Splits (Finset.univ.filter fun α => c α = k) H) := by
    rintro ⟨u, v⟩
    rw [hfilter u v]
    by_cases huv : u = 1 ∧ v = 1
    · obtain ⟨rfl, rfl⟩ := huv
      exact Or.inr ⟨h11, hHsplitI⟩
    · exact Or.inl (hother u v (not_and_or.mp huv))
  have hRone : R g = 1 := eq_one_of_fibres h5 h7 σ c hHu R hQs hform hsmall g
  exact eq_one_of_conjHom hPQ hQP ρ g hRone

end UnitaryCore

end CFSG.StandardType
