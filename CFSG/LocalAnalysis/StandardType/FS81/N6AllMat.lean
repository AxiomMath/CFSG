module

public import CFSG.LocalAnalysis.StandardType.FS81.N6Fix

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section LineSign

variable {n : ℕ}

@[expose] def lineSign (k : Fin (n + 1)) : Fin (n + 1) → ZMod 3 := fun i => if i = k then 1 else -1

theorem lineSign_isSign (k : Fin (n + 1)) : IsSign (lineSign k) := fun i => by
  by_cases hi : i = k
  · exact Or.inl (by simp [lineSign, hi])
  · exact Or.inr (by show (if i = k then (1 : ZMod 3) else -1) = -1; rw [if_neg hi])

theorem diagonal_lineSign_mul_self (k : Fin (n + 1)) :
    Matrix.diagonal (lineSign k) * Matrix.diagonal (lineSign k) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases lineSign_isSign k i with h | h <;> rw [h] <;> decide

theorem diagonal_eq_spMat_one (s : Fin (n + 1) → ZMod 3) : Matrix.diagonal s = spMat 1 s := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [spMat_apply]
  · simp [spMat_apply, Matrix.diagonal_apply_ne _ h, h]

theorem diagonal_lineSign_mem_evenAll0 (hn : Even n) (k : Fin (n + 1)) :
    Matrix.diagonal (lineSign k) ∈ evenAll0 n := by
  refine ⟨1, lineSign k, lineSign_isSign k, ⟨rfl, ?_⟩, diagonal_eq_spMat_one _⟩
  have hrest : ∀ i ∈ Finset.univ.erase k, lineSign k i = -1 := fun i hi => by
    show (if i = k then (1 : ZMod 3) else -1) = -1
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  calc ∏ i, lineSign k i = lineSign k k * ∏ i ∈ Finset.univ.erase k, lineSign k i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
    _ = 1 * (-1) ^ n := by
        rw [Finset.prod_congr rfl hrest, Finset.prod_const, Finset.card_erase_of_mem
          (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
        simp [lineSign]
    _ = 1 := by rw [hn.neg_one_pow, one_mul]

theorem diagonal_lineSign_mulVec_eq_self_iff (k : Fin (n + 1)) (v : Fin (n + 1) → ZMod 3) :
    Matrix.diagonal (lineSign k) *ᵥ v = v ↔ ∀ i, i ≠ k → v i = 0 := by
  constructor
  · intro h i hi
    have e := congrFun h i
    simp only [Matrix.mulVec_diagonal, lineSign, if_neg hi, neg_one_mul] at e
    exact eq_zero_of_neg_eq_self e
  · intro h
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases hi : i = k
    · subst hi
      simp [lineSign]
    · rw [h i hi, mul_zero]

theorem diagonal_lineSign_mulVec_of_eq_zero (k : Fin (n + 1)) {v : Fin (n + 1) → ZMod 3}
    (hv : v k = 0) : Matrix.diagonal (lineSign k) *ᵥ v = -v := by
  funext i
  rw [Matrix.mulVec_diagonal, Pi.neg_apply]
  by_cases hi : i = k
  · subst hi
    simp [hv]
  · simp [lineSign, hi]

theorem commute_tau_of_mem_evenAll0 {S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hS : S ∈ evenAll0 n) : S * Matrix.diagonal (tauSign n) = Matrix.diagonal (tauSign n) * S := by
  obtain ⟨σ, s, -, ⟨hσ0, -⟩, rfl⟩ := hS
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, spMat_apply]
  by_cases h : i = σ j
  · subst h
    rw [if_pos rfl]
    have : tauSign n (σ j) = tauSign n j := by
      simp only [tauSign]
      by_cases hj : j = 0
      · subst hj
        rw [hσ0]
      · have : σ j ≠ 0 := fun e => hj (σ.injective (e.trans hσ0.symm))
        rw [if_neg this, if_neg hj]
    rw [this, mul_comm]
  · rw [if_neg h, zero_mul, mul_zero]

theorem eq_diagonal_lineSign_of_mem_evenAll0 (hn : Even n)
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hS : S ∈ evenAll0 n) (h2 : S * S = 1)
    {w : Fin (n + 1) → ZMod 3} (hw0 : w ≠ 0) (hw : S *ᵥ w = w)
    (hfix : ∀ v, S *ᵥ v = v → ∃ c : ZMod 3, v = c • w) :
    ∃ k, S = Matrix.diagonal (lineSign k) := by
  obtain ⟨σ, s, hs, ⟨-, hprod⟩, rfl⟩ := hS
  have hcol : ∀ j c, spMat σ s *ᵥ Pi.single j c = Pi.single (σ j) (s j * c) := by
    intro j c
    funext i
    rw [spMat_mulVec]
    by_cases h : i = σ j
    · subst h
      simp
    · have hne : σ.symm i ≠ j := fun e => h (by rw [← e, Equiv.apply_symm_apply])
      simp [Pi.single_apply, hne, h]
  have hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1 := by
    intro j
    have e := congrFun (congrFun h2 (σ (σ j))) j
    rw [spMat_mul, spMat_apply, Equiv.Perm.mul_apply, if_pos rfl, Matrix.one_apply] at e
    have hne : s (σ j) * s j ≠ 0 := by
      rcases hs (σ j) with h1 | h1 <;> rcases hs j with h3 | h3 <;> rw [h1, h3] <;> decide
    by_cases hj : σ (σ j) = j
    · rw [if_pos hj] at e
      exact ⟨hj, e⟩
    · rw [if_neg hj] at e
      exact absurd e hne
  have hsep : ∀ v₁ v₂ : Fin (n + 1) → ZMod 3, spMat σ s *ᵥ v₁ = v₁ → spMat σ s *ᵥ v₂ = v₂ →
      v₂ ≠ 0 → ∀ i, v₁ i ≠ 0 → v₂ i = 0 → False := by
    intro v₁ v₂ h1 h1' hne i hi1 hi2
    obtain ⟨c₁, rfl⟩ := hfix v₁ h1
    obtain ⟨c₂, rfl⟩ := hfix v₂ h1'
    have hwi : w i ≠ 0 := fun h => hi1 (by simp [h])
    have hc₂ : c₂ = 0 := by
      have : c₂ * w i = 0 := by simpa using hi2
      exact (mul_eq_zero.mp this).resolve_right hwi
    exact hne (by rw [hc₂, zero_smul])
  have hpair : ∀ i, spMat σ s *ᵥ (Pi.single i 1 + Pi.single (σ i) (s i)) =
      Pi.single i 1 + Pi.single (σ i) (s i) := by
    intro i
    obtain ⟨hii, hsi⟩ := hsq i
    rw [Matrix.mulVec_add, hcol, hcol, hii, hsi, mul_one]
    exact add_comm _ _
  by_cases hσ : ∀ i, σ i = i
  ·
    have hσ1 : σ = 1 := Equiv.ext hσ
    subst hσ1
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (funext h)
    have hsk : s k = 1 := by
      have e := congrFun hw k
      rw [← diagonal_eq_spMat_one, Matrix.mulVec_diagonal] at e
      exact mul_right_cancel₀ hk (e.trans (one_mul _).symm)
    refine ⟨k, ?_⟩
    rw [← diagonal_eq_spMat_one]
    congr 1
    funext i
    by_cases hi : i = k
    · subst hi
      simp [lineSign, hsk]
    · rcases hs i with h1 | h1
      · exfalso
        refine hsep (Pi.single i 1) (Pi.single k 1) ?_ ?_ ?_ i (by simp) ?_
        · rw [hcol, Equiv.Perm.one_apply, h1, mul_one]
        · rw [hcol, Equiv.Perm.one_apply, hsk, mul_one]
        · intro h
          have := congrFun h k
          simp at this
        · simp [Pi.single_apply, hi]
      · show s i = if i = k then 1 else -1
        rw [if_neg hi]
        exact h1
  ·
    exfalso
    push Not at hσ
    obtain ⟨i, hi⟩ := hσ
    obtain ⟨hii, hsi⟩ := hsq i
    have hv1 := hpair i
    have hv1i : (Pi.single i 1 + Pi.single (σ i) (s i) : Fin (n + 1) → ZMod 3) i ≠ 0 := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi), add_zero]
      exact one_ne_zero
    have hrest : ∀ k, k ≠ i → k ≠ σ i → s k = -1 := by
      intro k hki hkj
      by_cases hσk : σ k = k
      · rcases hs k with h1 | h1
        · exfalso
          refine hsep _ (Pi.single k 1) hv1 ?_ ?_ i hv1i ?_
          · rw [hcol, hσk, h1, mul_one]
          · intro h
            have := congrFun h k
            simp at this
          · simp [Pi.single_apply, Ne.symm hki]
        · exact h1
      · exfalso
        have hσki : σ k ≠ i := fun e => hkj (by rw [← e, (hsq k).1])
        refine hsep _ (Pi.single k 1 + Pi.single (σ k) (s k)) hv1 (hpair k) ?_ i hv1i ?_
        · intro h
          have := congrFun h k
          rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hσk), add_zero] at this
          exact one_ne_zero this
        · rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hki), Pi.single_eq_of_ne (Ne.symm hσki),
            add_zero]
    have hσi : σ i ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
    have hcard : ((Finset.univ.erase i).erase (σ i)).card = n - 1 := by
      rw [Finset.card_erase_of_mem hσi, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      omega
    have hn1 : 1 ≤ n := by
      by_contra h
      have : n = 0 := by omega
      subst this
      exact hi (Fin.ext (by have := i.isLt; have := (σ i).isLt; omega))
    have hodd : Odd (n - 1) := by
      obtain ⟨m, hm⟩ := hn
      exact ⟨m - 1, by omega⟩
    have hp : ∏ k, s k = -1 := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ hσi]
      have : ∀ k ∈ (Finset.univ.erase i).erase (σ i), s k = -1 := fun k hk =>
        hrest k (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk))
          (Finset.ne_of_mem_erase hk)
      rw [Finset.prod_congr rfl this, Finset.prod_const, hcard, hodd.neg_one_pow,
        ← mul_assoc, mul_comm (s i), hsi, one_mul]
    rw [hp] at hprod
    exact absurd hprod (by decide)

end LineSign

section Count

theorem card_spSet_fix_le (n : ℕ) (p : Equiv.Perm (Fin (n + 1)) → (Fin (n + 1) → ZMod 3) → Prop) :
    Nat.card ↥(spSet fun σ s => σ 0 = 0 ∧ p σ s) ≤ 2 ^ (n + 1) * n.factorial := by
  classical
  let T : Set (Fin (n + 1) → ZMod 3) := {s | IsSign s}
  have hT : Nat.card ↥T ≤ 2 ^ (n + 1) := by
    have hinj : Function.Injective
        (fun s : ↥T => fun i => decide ((s : Fin (n + 1) → ZMod 3) i = 1)) := by
      rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
      apply Subtype.ext
      funext i
      have hi := congrFun h i
      revert hi
      show decide (s i = 1) = decide (s' i = 1) → s i = s' i
      rcases hs i with h1 | h1 <;> rcases hs' i with h2 | h2 <;> rw [h1, h2] <;> decide
    calc Nat.card ↥T ≤ Nat.card (Fin (n + 1) → Bool) := Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ (n + 1) := by simp
  let P := {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = 0}
  have hP : Nat.card P = n.factorial := by
    have e1 : P ≃ {f : Equiv.Perm (Fin (n + 1)) // ∀ a, ¬ (a ≠ 0) → f a = a} :=
      Equiv.subtypeEquivRight fun f => ⟨fun h a ha => by
        rw [not_not] at ha
        subst ha
        exact h, fun h => h 0 (by simp)⟩
    rw [Nat.card_congr (e1.trans (Equiv.Perm.subtypeEquivSubtypePerm
      (fun a : Fin (n + 1) => a ≠ 0)).symm), Nat.card_perm]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_subtype_eq, Nat.add_sub_cancel]
  let F : P × ↥T → Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) := fun q => spMat q.1.1 q.2
  have hsub : (spSet fun σ s => σ 0 = 0 ∧ p σ s) ⊆ Set.range F := by
    rintro _ ⟨σ, s, hs, ⟨hσ0, -⟩, rfl⟩
    exact ⟨(⟨σ, hσ0⟩, ⟨s, hs⟩), rfl⟩
  calc Nat.card ↥(spSet fun σ s => σ 0 = 0 ∧ p σ s) ≤ Nat.card ↥(Set.range F) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (P × ↥T) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization F) Set.rangeFactorization_surjective
    _ = n.factorial * Nat.card ↥T := by rw [Nat.card_prod, hP]
    _ ≤ 2 ^ (n + 1) * n.factorial := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hT

theorem dvd_card_of_classes {α : Type*} [Fintype α] (r : α → α → Prop) (hr : Equivalence r)
    (k : ℕ) (hk : ∀ a, Nat.card {b // r a b} = k) : k ∣ Fintype.card α := by
  classical
  let s : Setoid α := ⟨r, hr⟩
  have h : Fintype.card α = ∑ q : Quotient s, Fintype.card {a // Quotient.mk s a = q} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv _).symm
  have h2 : ∀ q : Quotient s, Fintype.card {a // Quotient.mk s a = q} = k := by
    intro q
    induction q using Quotient.inductionOn with
    | h a₀ =>
      rw [← hk a₀, Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
        rw [Quotient.eq]
        exact ⟨fun h => hr.symm h, fun h => hr.symm h⟩)
  rw [h, Finset.sum_congr rfl (fun q _ => h2 q), Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

end Count

section Seven

@[expose] noncomputable def dGL (k : Fin 7) : GL (Fin 7) (ZMod 3) :=
  ⟨Matrix.diagonal (lineSign k), Matrix.diagonal (lineSign k), diagonal_lineSign_mul_self k,
    diagonal_lineSign_mul_self k⟩

theorem coe_dGL (k : Fin 7) :
    ((dGL k : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) =
      Matrix.diagonal (lineSign k) :=
  rfl

theorem dGL_injective : Function.Injective dGL := by
  intro k l h
  by_contra hkl
  have e := congrArg (fun A : GL (Fin 7) (ZMod 3) => (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) k k) h
  simp only [coe_dGL, Matrix.diagonal_apply_eq, lineSign, if_pos rfl, if_neg hkl] at e
  exact absurd e (by decide)

theorem dGL_mul_self (k : Fin 7) : dGL k * dGL k = 1 := Units.ext (diagonal_lineSign_mul_self k)

theorem dGL_commute (k l : Fin 7) : dGL k * dGL l = dGL l * dGL k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dGL, coe_dGL, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

@[expose] noncomputable def diagU (s : Fin 7 → ZMod 3) : GL (Fin 7) (ZMod 3) :=
  if h : ∀ i, s i * s i = 1 then
    ⟨Matrix.diagonal s, Matrix.diagonal s,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact h i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact h i⟩
  else 1

theorem coe_diagU {s : Fin 7 → ZMod 3} (hs : IsSign s) :
    ((diagU s : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) = Matrix.diagonal s := by
  have h : ∀ i, s i * s i = 1 := fun i => by rcases hs i with h | h <;> rw [h] <;> decide
  rw [diagU, dif_pos h]

theorem diagU_mul_self {s : Fin 7 → ZMod 3} (hs : IsSign s) : diagU s * diagU s = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_diagU hs, Units.val_one, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hs i with h | h <;> rw [h] <;> decide

theorem diagU_inv {s : Fin 7 → ZMod 3} (hs : IsSign s) : (diagU s)⁻¹ = diagU s :=
  inv_eq_of_mul_eq_one_right (diagU_mul_self hs)

theorem spMat_mul_diagonal {k : ℕ} (σ : Equiv.Perm (Fin k)) (s t : Fin k → ZMod 3) :
    spMat σ s * Matrix.diagonal t = Matrix.diagonal (fun i => t (σ.symm i)) * spMat σ s := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, spMat_apply]
  by_cases h : i = σ j
  · subst h
    simp [mul_comm]
  · simp [h]

theorem card_even_signs :
    (Finset.univ.filter (fun s : Fin 7 → ZMod 3 => (∀ i, s i = 1 ∨ s i = -1) ∧ ∏ i, s i = 1)).card =
      64 := by
  decide +kernel

theorem false_of_evenAll0_six (Xg : Subgroup (GL (Fin 7) (ZMod 3)))
    (hN : ∀ A ∈ Xg, (∀ i : Fin 7, i ≠ 0 → (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 = 0) →
      (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenAll0 6)
    (hsub : ∀ M ∈ evenAll0 6, ∃ A ∈ Xg, (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) = M)
    (hodd : ∀ N : Subgroup ↥Xg, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmove : ∃ A ∈ Xg, ∃ i : Fin 7, i ≠ 0 ∧ (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 ≠ 0)
    (hcard : 2 ^ 7 * Nat.factorial 7 < Nat.card Xg) : False := by
  classical
  have hmat : ∀ A : GL (Fin 7) (ZMod 3), (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenAll0 6 →
      A ∈ Xg := by
    intro A hA
    obtain ⟨B, hB, hBA⟩ := hsub _ hA
    have : B = A := Units.ext hBA
    exact this ▸ hB
  have hd : ∀ k, dGL k ∈ Xg := fun k => hmat _ (diagonal_lineSign_mem_evenAll0 ⟨3, rfl⟩ k)
  set τ : GL (Fin 7) (ZMod 3) := dGL 0 with hτ
  have hτ2 : τ * τ = 1 := dGL_mul_self 0
  have hcol0 : ∀ A : GL (Fin 7) (ZMod 3), A * τ = τ * A →
      ∀ i : Fin 7, i ≠ 0 → (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 = 0 := by
    intro A h i hi
    have e : (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) * (τ : Matrix (Fin 7) (Fin 7) (ZMod 3)) =
        (τ : Matrix (Fin 7) (Fin 7) (ZMod 3)) * A := by
      have := congrArg (fun B : GL (Fin 7) (ZMod 3) => (B : Matrix (Fin 7) (Fin 7) (ZMod 3))) h
      simpa only [Units.val_mul] using this
    exact apply_zero_eq_zero_of_commute_tau (n := 6) e hi
  have hCmem : ∀ A ∈ Xg, A * τ = τ * A → (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenAll0 6 :=
    fun A hA h => hN A hA (hcol0 A h)
  have hτC : ∀ A : GL (Fin 7) (ZMod 3), (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenAll0 6 →
      A * τ = τ * A := fun A hA =>
    Units.ext (by rw [Units.val_mul, Units.val_mul]; exact commute_tau_of_mem_evenAll0 hA)
  have hgg : ∀ g : GL (Fin 7) (ZMod 3), (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *
      ((g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := fun g => by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ∀ g : GL (Fin 7) (ZMod 3), ((g⁻¹ : GL (Fin 7) (ZMod 3)) :
      Matrix (Fin 7) (Fin 7) (ZMod 3)) * (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := fun g => by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcolv : ∀ (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) (i : Fin 7),
      (A *ᵥ Pi.single 0 1) i = A i 0 := fun A i => by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  have hfixτ : ∀ u : Fin 7 → ZMod 3, (τ : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ u = u ↔
      u = u 0 • Pi.single 0 1 := by
    intro u
    rw [hτ, coe_dGL, diagonal_lineSign_mulVec_eq_self_iff]
    constructor
    · intro h
      funext i
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [h i hi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    · intro h i hi
      rw [h, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
  have hconj_fix : ∀ (g : GL (Fin 7) (ZMod 3)) (v : Fin 7 → ZMod 3),
      ((g * τ * g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ v = v ↔
        ∃ c : ZMod 3, v = c • ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    intro g v
    constructor
    · intro hv
      set u := ((g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ v with hu
      have hτu : (τ : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ u = u := by
        have e := congrArg
          (fun x => ((g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ x) hv
        simp only [Units.val_mul, Matrix.mulVec_mulVec] at e
        rw [hu, Matrix.mulVec_mulVec, ← e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg',
          Matrix.one_mul]
      refine ⟨u 0, ?_⟩
      have hu0 := (hfixτ u).mp hτu
      calc v = (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ u := by
            rw [hu, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
        _ = (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ (u 0 • Pi.single 0 1) := by rw [← hu0]
        _ = u 0 • ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) :=
            Matrix.mulVec_smul _ _ _
    · rintro ⟨c, rfl⟩
      have hτe : (τ : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
        (hfixτ _).mpr (by simp)
      rw [Matrix.mulVec_smul, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
        Matrix.mul_assoc, hgg', Matrix.mul_one, ← Matrix.mulVec_mulVec, hτe]
  have hconj_mem : ∀ g ∈ Xg, g * τ * g⁻¹ ∈ Xg := fun g hg =>
    Xg.mul_mem (Xg.mul_mem hg (hd 0)) (Xg.inv_mem hg)
  have hconj_sq : ∀ g : GL (Fin 7) (ZMod 3), (g * τ * g⁻¹) * (g * τ * g⁻¹) = 1 := fun g => by
    rw [show g * τ * g⁻¹ * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ by group, hτ2, mul_one,
      mul_inv_cancel]
  have hge0 : ∀ g : GL (Fin 7) (ZMod 3),
      (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 ≠ 0 := by
    intro g h
    have e : (Pi.single 0 1 : Fin 7 → ZMod 3) = 0 := by
      calc (Pi.single 0 1 : Fin 7 → ZMod 3) =
          ((g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
            ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) := by
            rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
        _ = 0 := by rw [h, Matrix.mulVec_zero]
    have := congrFun e 0
    simp at this
  have hclass : ∀ g ∈ Xg, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → ∃ k, g * τ * g⁻¹ = dGL k := by
    intro g hg hc
    have hS := hCmem _ (hconj_mem g hg) hc
    have h2 : ((g * τ * g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *
        ((g * τ * g⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, hconj_sq, Units.val_one]
    obtain ⟨k, hk⟩ := eq_diagonal_lineSign_of_mem_evenAll0 (n := 6) ⟨3, rfl⟩ hS h2 (hge0 g)
      ((hconj_fix g _).mpr ⟨1, (one_smul _ _).symm⟩) (fun v hv => (hconj_fix g v).mp hv)
    exact ⟨k, Units.ext hk⟩
  have hsame : ∀ g ∈ Xg, ∀ h ∈ Xg, ∀ c : ZMod 3,
      (h : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) →
      h * τ * h⁻¹ = g * τ * g⁻¹ := by
    intro g hg h hh c hc
    have hA : g⁻¹ * h ∈ Xg := Xg.mul_mem (Xg.inv_mem hg) hh
    have hcolA : ∀ i : Fin 7, i ≠ 0 →
        ((g⁻¹ * h : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 = 0 := by
      intro i hi
      have hv : ((g⁻¹ * h : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
          Pi.single 0 1 = c • Pi.single 0 1 := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
          hgg', Matrix.one_mulVec]
      rw [← hcolv ((g⁻¹ * h : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) i, hv,
        Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    have hcomm := hτC _ (hN _ hA hcolA)
    calc h * τ * h⁻¹ = g * ((g⁻¹ * h) * τ) * (g⁻¹ * h)⁻¹ * g⁻¹ := by group
      _ = g * (τ * (g⁻¹ * h)) * (g⁻¹ * h)⁻¹ * g⁻¹ := by rw [hcomm]
      _ = g * τ * g⁻¹ := by group
  by_cases hB : ∃ g ∈ Xg, ∃ k : Fin 7, k ≠ 0 ∧ g * τ * g⁻¹ = dGL k
  swap
  ·
    push Not at hB
    have : Fintype ↥Xg := Fintype.ofFinite _
    set τ' : ↥Xg := ⟨τ, hd 0⟩ with hτ'
    have hτ1 : τ' ≠ 1 := by
      intro h
      have e := congrArg (fun x : ↥Xg =>
        ((x : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) 1 1) h
      simp only [hτ', hτ, coe_dGL, Matrix.diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
        Matrix.one_apply_eq, lineSign] at e
      exact absurd e (by decide)
    have hτ2' : τ' * τ' = 1 := Subtype.ext hτ2
    have hiso : ∀ g : ↥Xg, (g * τ' * g⁻¹) * τ' = τ' * (g * τ' * g⁻¹) → g * τ' * g⁻¹ = τ' := by
      intro g hc
      have hc' : ((g : GL (Fin 7) (ZMod 3)) * τ * (g : GL (Fin 7) (ZMod 3))⁻¹) * τ =
          τ * ((g : GL (Fin 7) (ZMod 3)) * τ * (g : GL (Fin 7) (ZMod 3))⁻¹) := by
        have := congrArg Subtype.val hc
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
      obtain ⟨k, hk⟩ := hclass g g.2 hc'
      by_cases hk0 : k = 0
      · subst hk0
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hk
      · exact absurd hk (hB g g.2 k hk0)
    obtain ⟨N, hNn, hNodd, hNτ⟩ := CFSG.ZStar.glauberman_zStar ↥Xg τ' hτ1 hτ2' hiso
    have hN0 := hodd N hNn hNodd
    obtain ⟨A, hA, i, hi, hAi⟩ := hmove
    apply hAi
    have h1 := hNτ ⟨A, hA⟩
    rw [hN0, Subgroup.mem_bot, mul_inv_eq_one] at h1
    have h1' : A * τ * A⁻¹ = τ := by
      have := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hcomm : A * τ = τ * A := by
      calc A * τ = A * τ * A⁻¹ * A := by group
        _ = τ * A := by rw [h1']
    exact hcol0 A hcomm i hi
  obtain ⟨g₁, hg₁, k₁, hk₁, hg₁k⟩ := hB
  have hperm : ∀ a b : Fin 7, a ≠ 0 → b ≠ 0 → ∃ P ∈ Xg, P * dGL a * P⁻¹ = dGL b := by
    intro a b ha hb
    have hπ0 : Equiv.swap a b 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)
    have hPmem : spMat (Equiv.swap a b) (fun _ => 1) ∈ evenAll0 6 :=
      ⟨Equiv.swap a b, fun _ => 1, fun _ => Or.inl rfl, ⟨hπ0, by simp⟩, rfl⟩
    have hPP : spMat (Equiv.swap a b) (fun _ => (1 : ZMod 3)) * spMat (Equiv.swap a b) (fun _ => 1) =
        1 := spMat_mul_self _ _ (Equiv.swap_mul_self a b) (fun _ => by simp)
    obtain ⟨P, hP, hPM⟩ := hsub _ hPmem
    refine ⟨P, hP, Units.ext ?_⟩
    have hPinv : P⁻¹ = P :=
      inv_eq_of_mul_eq_one_right (Units.ext (by rw [Units.val_mul, hPM, hPP, Units.val_one]))
    rw [Units.val_mul, Units.val_mul, hPinv, hPM, coe_dGL, coe_dGL, spMat_mul_diagonal,
      Matrix.mul_assoc, hPP, Matrix.mul_one]
    congr 1
    funext i
    simp only [lineSign, Equiv.symm_swap, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  have hconjd : ∀ j : Fin 7, ∃ g ∈ Xg, g * τ * g⁻¹ = dGL j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      exact ⟨1, Xg.one_mem, by rw [hτ]; group⟩
    · obtain ⟨P, hP, hPd⟩ := hperm k₁ j hk₁ hj
      exact ⟨P * g₁, Xg.mul_mem hP hg₁, by rw [← hPd, ← hg₁k]; group⟩
  obtain ⟨D, hD⟩ : ∃ D : Finset (GL (Fin 7) (ZMod 3)), D = Finset.univ.image dGL := ⟨_, rfl⟩
  have hmemD : ∀ x, x ∈ D ↔ ∃ k, dGL k = x := fun x => by
    rw [hD, Finset.mem_image]
    simp
  have hdD : ∀ k, dGL k ∈ D := fun k => (hmemD _).mpr ⟨k, rfl⟩
  have hDcard : D.card = 7 := by
    rw [hD, Finset.card_image_of_injective _ dGL_injective, Finset.card_univ, Fintype.card_fin]
  have hconj_inj : ∀ y : GL (Fin 7) (ZMod 3), Function.Injective (fun x => y * x * y⁻¹) :=
    fun y a b hab => by simpa using hab
  have hmemimg : ∀ (y x : GL (Fin 7) (ZMod 3)), x ∈ D.image (fun x => y * x * y⁻¹) ↔
      ∃ k, y * dGL k * y⁻¹ = x := fun y x => by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨d, hd', rfl⟩
      obtain ⟨k, rfl⟩ := (hmemD d).mp hd'
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨dGL k, hdD k, rfl⟩
  have hframe : ∀ (j : Fin 7) (y : GL (Fin 7) (ZMod 3)), y ∈ Xg → y * τ * y⁻¹ = dGL j →
      D.image (fun x => y * x * y⁻¹) = D ∧
        ∀ h ∈ Xg, (h * τ * h⁻¹) * dGL j = dGL j * (h * τ * h⁻¹) → h * τ * h⁻¹ ∈ D := by
    intro j y hy hyj
    have hin : ∀ h ∈ Xg, (h * τ * h⁻¹) * dGL j = dGL j * (h * τ * h⁻¹) →
        h * τ * h⁻¹ ∈ D.image (fun x => y * x * y⁻¹) := by
      intro h hh hch
      rw [← hyj] at hch
      have hc' : ((y⁻¹ * h) * τ * (y⁻¹ * h)⁻¹) * τ = τ * ((y⁻¹ * h) * τ * (y⁻¹ * h)⁻¹) := by
        calc ((y⁻¹ * h) * τ * (y⁻¹ * h)⁻¹) * τ =
            y⁻¹ * ((h * τ * h⁻¹) * (y * τ * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * τ * y⁻¹) * (h * τ * h⁻¹)) * y := by rw [hch]
          _ = τ * ((y⁻¹ * h) * τ * (y⁻¹ * h)⁻¹) := by group
      obtain ⟨k, hk⟩ := hclass _ (Xg.mul_mem (Xg.inv_mem hy) hh) hc'
      refine (hmemimg y _).mpr ⟨k, ?_⟩
      rw [← hk]
      group
    have hsubD : D ⊆ D.image (fun x => y * x * y⁻¹) := by
      intro x hx
      obtain ⟨k, rfl⟩ := (hmemD x).mp hx
      obtain ⟨h, hh, hhk⟩ := hconjd k
      rw [← hhk]
      exact hin h hh (by rw [hhk]; exact dGL_commute k j)
    have heq : D = D.image (fun x => y * x * y⁻¹) :=
      Finset.eq_of_subset_of_card_le hsubD (by rw [Finset.card_image_of_injective _ (hconj_inj y)])
    exact ⟨heq.symm, fun h hh hch => heq ▸ hin h hh hch⟩
  have hfull : ∀ g ∈ Xg, g * τ * g⁻¹ ∉ D →
      ∀ k : Fin 7, ((g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1) k ≠ 0 := by
    intro g hg hnD k hk
    apply hnD
    obtain ⟨y, hy, hyk⟩ := hconjd k
    refine (hframe k y hy hyk).2 g hg ?_
    have hA : g⁻¹ * dGL k * g ∈ Xg := Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hg) (hd k)) hg
    have hcolA : ∀ i : Fin 7, i ≠ 0 →
        ((g⁻¹ * dGL k * g : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) i 0 = 0 := by
      intro i hi
      have hv : ((g⁻¹ * dGL k * g : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
          Pi.single 0 1 = -Pi.single 0 1 := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, coe_dGL,
          diagonal_lineSign_mulVec_of_eq_zero k hk, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hgg',
          Matrix.one_mulVec]
      rw [← hcolv ((g⁻¹ * dGL k * g : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) i, hv,
        Pi.neg_apply, Pi.single_eq_of_ne hi, neg_zero]
    have hcomm := hτC _ (hN _ hA hcolA)
    calc (g * τ * g⁻¹) * dGL k = g * (τ * (g⁻¹ * dGL k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * dGL k * g) * τ) * g⁻¹ := by rw [hcomm]
      _ = dGL k * (g * τ * g⁻¹) := by group
  have : Fintype ↥Xg := Fintype.ofFinite _
  obtain ⟨Cl, hCl⟩ : ∃ Cl : Finset (GL (Fin 7) (ZMod 3)),
      Cl = Finset.univ.filter (fun σ => ∃ g ∈ Xg, σ = g * τ * g⁻¹) := ⟨_, rfl⟩
  have hmemCl : ∀ σ, σ ∈ Cl ↔ ∃ g ∈ Xg, σ = g * τ * g⁻¹ := fun σ => by
    rw [hCl, Finset.mem_filter]
    simp
  have hDCl : D ⊆ Cl := by
    intro x hx
    obtain ⟨k, rfl⟩ := (hmemD x).mp hx
    obtain ⟨g, hg, hgk⟩ := hconjd k
    exact (hmemCl _).mpr ⟨g, hg, hgk.symm⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ↥Xg, τ' = ⟨τ, hd 0⟩ := ⟨_, rfl⟩
  have hτ'v : (τ' : GL (Fin 7) (ZMod 3)) = τ := by rw [hτ']
  have hcls := MulAction.card_conjClass_mul_card_centralizer τ'
  have horb : Nat.card (MulAction.orbit (ConjAct ↥Xg) τ') = Cl.card := by
    rw [← Nat.card_eq_finsetCard]
    have hmem1 : ∀ x : ↥(MulAction.orbit (ConjAct ↥Xg) τ'),
        ((x : ↥Xg) : GL (Fin 7) (ZMod 3)) ∈ Cl := by
      intro x
      obtain ⟨c, hc⟩ := x.2
      have hc' : c • τ' = (x : ↥Xg) := hc
      refine (hmemCl _).mpr ⟨((ConjAct.ofConjAct c : ↥Xg) : GL (Fin 7) (ZMod 3)),
        (ConjAct.ofConjAct c).2, ?_⟩
      rw [← hc', ConjAct.smul_def]
      simp [hτ'v]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨((x : ↥Xg) : GL (Fin 7) (ZMod 3)), hmem1 x⟩)
      ⟨?_, ?_⟩)
    · intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    · rintro ⟨σ, hσ⟩
      obtain ⟨g, hg, rfl⟩ := (hmemCl σ).mp hσ
      refine ⟨⟨⟨g * τ * g⁻¹, hconj_mem g hg⟩, ⟨ConjAct.toConjAct (⟨g, hg⟩ : ↥Xg), ?_⟩⟩, rfl⟩
      show ConjAct.toConjAct (⟨g, hg⟩ : ↥Xg) • τ' = _
      rw [ConjAct.smul_def]
      apply Subtype.ext
      simp [hτ'v]
  have hcent : Nat.card ↥(Subgroup.centralizer ({τ'} : Set ↥Xg)) ≤ 2 ^ 7 * Nat.factorial 6 := by
    have hmemE : ∀ x : ↥(Subgroup.centralizer ({τ'} : Set ↥Xg)),
        (((x : ↥Xg) : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) ∈ evenAll0 6 := by
      intro x
      have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
      have hx' : ((x : ↥Xg) : GL (Fin 7) (ZMod 3)) * τ = τ * ((x : ↥Xg) : GL (Fin 7) (ZMod 3)) := by
        have := congrArg Subtype.val hx
        simpa [hτ'v] using this
      exact hCmem _ (x : ↥Xg).2 hx'
    have hinj : Function.Injective (fun x : ↥(Subgroup.centralizer ({τ'} : Set ↥Xg)) =>
        (⟨(((x : ↥Xg) : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)), hmemE x⟩ :
          ↥(evenAll0 6))) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (Units.ext (congrArg Subtype.val hxy)))
    exact (Nat.card_le_card_of_injective _ hinj).trans (card_spSet_fix_le 6 _)
  have hW : (Cl \ D).card = 0 ∨ (Cl \ D).card = 64 := by
    by_cases hW0 : (Cl \ D) = ∅
    · left
      rw [hW0, Finset.card_empty]
    right
    obtain ⟨σ₀, hσ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hW0
    obtain ⟨hσ₀Cl, hσ₀D⟩ := Finset.mem_sdiff.mp hσ₀
    obtain ⟨g₀, hg₀, rfl⟩ := (hmemCl _).mp hσ₀Cl
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin 7 → ZMod 3,
        w₀ = (g₀ : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 := ⟨_, rfl⟩
    have hw₀f : ∀ i, w₀ i ≠ 0 := fun i => by rw [hw₀]; exact hfull g₀ hg₀ hσ₀D i
    have hsq1 : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
    have hw₀s : ∀ i, w₀ i * w₀ i = 1 := fun i => hsq1 _ (hw₀f i)
    obtain ⟨SV, hSV⟩ : ∃ SV : Finset (Fin 7 → ZMod 3), SV = Finset.univ.filter
        (fun s : Fin 7 → ZMod 3 => (∀ i, s i = 1 ∨ s i = -1) ∧ ∏ i, s i = 1) := ⟨_, rfl⟩
    have hmemSV : ∀ s, s ∈ SV ↔ (∀ i, s i = 1 ∨ s i = -1) ∧ ∏ i, s i = 1 := fun s => by
      rw [hSV, Finset.mem_filter]
      simp
    have hSVcard : SV.card = 64 := by rw [hSV]; exact card_even_signs
    have hSVmem : ∀ s ∈ SV, IsSign s ∧ diagU s ∈ Xg := by
      intro s hs
      obtain ⟨hsgn, hprod⟩ := (hmemSV s).mp hs
      refine ⟨hsgn, hmat _ ?_⟩
      rw [coe_diagU hsgn, diagonal_eq_spMat_one]
      exact ⟨1, s, hsgn, ⟨rfl, hprod⟩, rfl⟩
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 7 → ZMod 3) → GL (Fin 7) (ZMod 3),
        Φ = fun s => (diagU s * g₀) * τ * (diagU s * g₀)⁻¹ := ⟨_, rfl⟩
    have hΦapp : ∀ s, Φ s = (diagU s * g₀) * τ * (diagU s * g₀)⁻¹ := fun s => by rw [hΦ]
    have hΦvec : ∀ s ∈ SV, ((diagU s * g₀ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
        Pi.single 0 1 = fun i => s i * w₀ i := by
      intro s hs
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, coe_diagU (hSVmem s hs).1, ← hw₀]
      funext i
      rw [Matrix.mulVec_diagonal]
    have hΦmem : ∀ s ∈ SV, Φ s ∈ Cl \ D := by
      intro s hs
      have hmemX : diagU s * g₀ ∈ Xg := Xg.mul_mem (hSVmem s hs).2 hg₀
      refine Finset.mem_sdiff.mpr ⟨(hmemCl _).mpr ⟨_, hmemX, hΦapp s⟩, ?_⟩
      intro hΦD
      apply hσ₀D
      obtain ⟨k, hk⟩ := (hmemD _).mp hΦD
      have hfd : diagU s * dGL k = dGL k * diagU s := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_diagU (hSVmem s hs).1, coe_dGL,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
      have : g₀ * τ * g₀⁻¹ = dGL k := by
        calc g₀ * τ * g₀⁻¹ = (diagU s)⁻¹ * Φ s * diagU s := by rw [hΦapp]; group
          _ = (diagU s)⁻¹ * dGL k * diagU s := by rw [← hk]
          _ = (diagU s)⁻¹ * (diagU s * dGL k) := by rw [mul_assoc, hfd]
          _ = dGL k := by group
      rw [this]
      exact hdD k
    have hΦinj : Set.InjOn Φ SV := by
      intro s hs t ht hst
      have hs' := hSVmem s hs
      have ht' := hSVmem t ht
      have hrc : ((diagU t)⁻¹ * diagU s) * (g₀ * τ * g₀⁻¹) =
          (g₀ * τ * g₀⁻¹) * ((diagU t)⁻¹ * diagU s) := by
        have e : (diagU s * g₀) * τ * (diagU s * g₀)⁻¹ = (diagU t * g₀) * τ * (diagU t * g₀)⁻¹ := by
          rw [← hΦapp, ← hΦapp]
          exact hst
        calc ((diagU t)⁻¹ * diagU s) * (g₀ * τ * g₀⁻¹) =
            (diagU t)⁻¹ * ((diagU s * g₀) * τ * (diagU s * g₀)⁻¹) * diagU s := by group
          _ = (diagU t)⁻¹ * ((diagU t * g₀) * τ * (diagU t * g₀)⁻¹) * diagU s := by rw [e]
          _ = (g₀ * τ * g₀⁻¹) * ((diagU t)⁻¹ * diagU s) := by group
      have hrfix : ((g₀ * τ * g₀⁻¹ : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ
          ((((diagU t)⁻¹ * diagU s : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ w₀) =
          (((diagU t)⁻¹ * diagU s : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ w₀ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hrc, Units.val_mul, ← Matrix.mulVec_mulVec, hw₀,
          (hconj_fix g₀ _).mpr ⟨1, (one_smul _ _).symm⟩]
      obtain ⟨c, hc⟩ := (hconj_fix g₀ _).mp hrfix
      have htinv : (diagU t)⁻¹ = diagU t := diagU_inv ht'.1
      have hrmat : (((diagU t)⁻¹ * diagU s : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) =
          Matrix.diagonal (fun i => t i * s i) := by
        rw [htinv, Units.val_mul, coe_diagU ht'.1, coe_diagU hs'.1, Matrix.diagonal_mul_diagonal]
      have hts : ∀ i, t i * s i = c := by
        intro i
        have e := congrFun hc i
        rw [hrmat, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ← hw₀] at e
        exact mul_right_cancel₀ (hw₀f i) e
      have hc1 : c = 1 := by
        have hps := ((hmemSV s).mp hs).2
        have hpt := ((hmemSV t).mp ht).2
        have hprod : ∏ i, (t i * s i) = 1 := by rw [Finset.prod_mul_distrib, hps, hpt, one_mul]
        rw [Finset.prod_congr rfl (fun i _ => hts i), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at hprod
        have hc3 : c = 1 ∨ c = -1 := by
          rw [← hts 0]
          rcases ht'.1 0 with h | h <;> rcases hs'.1 0 with h' | h' <;> rw [h, h'] <;> decide
        rcases hc3 with h | h
        · exact h
        · rw [h] at hprod
          exact absurd hprod (by decide)
      funext i
      have e := hts i
      rw [hc1] at e
      rcases ht'.1 i with h | h <;> rcases hs'.1 i with h' | h' <;> rw [h, h'] at e ⊢ <;>
        first | rfl | exact absurd e (by decide)
    have hΦsurj : Cl \ D ⊆ SV.image Φ := by
      intro σ hσ
      obtain ⟨hσCl, hσD⟩ := Finset.mem_sdiff.mp hσ
      obtain ⟨g, hg, rfl⟩ := (hmemCl _).mp hσCl
      obtain ⟨w, hw⟩ : ∃ w : Fin 7 → ZMod 3,
          w = (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ Pi.single 0 1 := ⟨_, rfl⟩
      have hwf : ∀ i, w i ≠ 0 := fun i => by rw [hw]; exact hfull g hg hσD i
      have hsgn1 : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
      have hww : ∀ i, w i * w₀ i = 1 ∨ w i * w₀ i = -1 := fun i =>
        hsgn1 _ (mul_ne_zero (hwf i) (hw₀f i))
      obtain ⟨c, hcdef⟩ : ∃ c : ZMod 3, c = ∏ i, (w i * w₀ i) := ⟨_, rfl⟩
      have hc : c = 1 ∨ c = -1 := by
        have key : ∀ S : Finset (Fin 7),
            (∏ i ∈ S, (w i * w₀ i)) = 1 ∨ (∏ i ∈ S, (w i * w₀ i)) = -1 := by
          intro S
          induction S using Finset.induction_on with
          | empty => exact Or.inl Finset.prod_empty
          | insert a S ha ih =>
            rw [Finset.prod_insert ha]
            rcases hww a with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> decide
        rw [hcdef]
        exact key Finset.univ
      have hsSV : (fun i => c * (w i * w₀ i)) ∈ SV := by
        refine (hmemSV _).mpr ⟨fun i => ?_, ?_⟩
        · rcases hc with h | h <;> rcases hww i with h' | h' <;> simp only [h, h'] <;> decide
        · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← hcdef]
          rcases hc with h | h <;> rw [h] <;> decide
      refine Finset.mem_image.mpr ⟨_, hsSV, ?_⟩
      rw [hΦapp]
      apply hsame g hg _ (Xg.mul_mem (hSVmem _ hsSV).2 hg₀) c
      rw [hΦvec _ hsSV, ← hw]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_assoc, hw₀s i, mul_one]
    have : Cl \ D = SV.image Φ :=
      Finset.Subset.antisymm hΦsurj (fun x hx => by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
        exact hΦmem s hs)
    rw [this, Finset.card_image_of_injOn hΦinj, hSVcard]
  have hDimgCl : ∀ g ∈ Xg, D.image (fun x => g * x * g⁻¹) ⊆ Cl := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := (hmemimg g x).mp hx
    obtain ⟨y, hy, hyk⟩ := hconjd k
    refine (hmemCl _).mpr ⟨g * y, Xg.mul_mem hg hy, ?_⟩
    rw [← hyk]
    group
  have hclassD : ∀ g ∈ Xg, ∀ σ' ∈ Cl, (g * τ * g⁻¹) * σ' = σ' * (g * τ * g⁻¹) ↔
      σ' ∈ D.image (fun x => g * x * g⁻¹) := by
    intro g hg σ' hσ'
    obtain ⟨h, hh, rfl⟩ := (hmemCl _).mp hσ'
    constructor
    · intro hc
      have hc' : ((g⁻¹ * h) * τ * (g⁻¹ * h)⁻¹) * τ = τ * ((g⁻¹ * h) * τ * (g⁻¹ * h)⁻¹) := by
        calc ((g⁻¹ * h) * τ * (g⁻¹ * h)⁻¹) * τ =
            g⁻¹ * ((h * τ * h⁻¹) * (g * τ * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * τ * g⁻¹) * (h * τ * h⁻¹)) * g := by rw [hc]
          _ = τ * ((g⁻¹ * h) * τ * (g⁻¹ * h)⁻¹) := by group
      obtain ⟨k, hk⟩ := hclass _ (Xg.mul_mem (Xg.inv_mem hg) hh) hc'
      refine (hmemimg g _).mpr ⟨k, ?_⟩
      rw [← hk]
      group
    · intro hmem
      obtain ⟨k, hk⟩ := (hmemimg g _).mp hmem
      rw [← hk]
      calc (g * τ * g⁻¹) * (g * dGL k * g⁻¹) = g * (τ * dGL k) * g⁻¹ := by group
        _ = g * (dGL k * τ) * g⁻¹ := by rw [hτ, dGL_commute]
        _ = (g * dGL k * g⁻¹) * (g * τ * g⁻¹) := by group
  have h7 : 7 ∣ Cl.card := by
    rw [← Fintype.card_coe]
    have hcls' : ∀ σ : ↥Cl, ∃ g ∈ Xg, (σ : GL (Fin 7) (ZMod 3)) = g * τ * g⁻¹ :=
      fun σ => (hmemCl _).mp σ.2
    refine dvd_card_of_classes (fun σ σ' : ↥Cl => (σ : GL (Fin 7) (ZMod 3)) * σ' = σ' * σ)
      ⟨fun _ => rfl, fun h => h.symm, ?_⟩ 7 ?_
    · intro σ σ' σ'' h1 h2
      obtain ⟨g, hg, hσ⟩ := hcls' σ
      have h1' := (hclassD g hg σ' σ'.2).mp (by rw [← hσ]; exact h1)
      obtain ⟨k, hk⟩ := (hmemimg g _).mp h1'
      obtain ⟨y, hy, hyk⟩ := hconjd k
      have hσ' : (σ' : GL (Fin 7) (ZMod 3)) = (g * y) * τ * (g * y)⁻¹ := by
        rw [← hk, ← hyk]
        group
      have h2' := (hclassD (g * y) (Xg.mul_mem hg hy) σ'' σ''.2).mp (by rw [← hσ']; exact h2)
      have himg : D.image (fun x => (g * y) * x * (g * y)⁻¹) =
          D.image (fun x => g * x * g⁻¹) := by
        have hD' := (hframe k y hy hyk).1
        conv_rhs => rw [← hD']
        rw [Finset.image_image]
        refine congrArg (fun f => Finset.image f D) (funext fun x => ?_)
        simp only [Function.comp_apply]
        group
      rw [himg] at h2'
      show (σ : GL (Fin 7) (ZMod 3)) * σ'' = σ'' * σ
      rw [hσ]
      exact (hclassD g hg σ'' σ''.2).mpr h2'
    · intro σ
      obtain ⟨g, hg, hσ⟩ := hcls' σ
      have e : {b : ↥Cl // (σ : GL (Fin 7) (ZMod 3)) * b = b * σ} ≃
          {x // x ∈ D.image (fun x => g * x * g⁻¹)} :=
        { toFun := fun b => ⟨b.1.1, (hclassD g hg b.1.1 b.1.2).mp (by rw [← hσ]; exact b.2)⟩
          invFun := fun x => ⟨⟨x.1, hDimgCl g hg x.2⟩, by
            rw [hσ]
            exact (hclassD g hg x.1 (hDimgCl g hg x.2)).mpr x.2⟩
          left_inv := fun b => rfl
          right_inv := fun x => rfl }
      rw [Nat.card_congr e, Nat.card_eq_finsetCard, Finset.card_image_of_injective _ (hconj_inj g),
        hDcard]
  have hClD : Cl.card = D.card + (Cl \ D).card := by
    rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hDCl]
  rw [hDcard] at hClD
  rcases hW with h0 | h64
  · rw [h0, add_zero] at hClD
    have : Nat.card ↥Xg ≤ 2 ^ 7 * Nat.factorial 7 := by
      rw [Nat.card_eq_fintype_card, ← hcls, horb, hClD]
      calc 7 * Nat.card ↥(Subgroup.centralizer ({τ'} : Set ↥Xg)) ≤ 7 * (2 ^ 7 * Nat.factorial 6) :=
            Nat.mul_le_mul_left _ hcent
        _ = 2 ^ 7 * Nat.factorial 7 := by decide
    omega
  · rw [h64] at hClD
    rw [hClD] at h7
    exact absurd h7 (by decide)

end Seven

end CFSG.StandardType.FrameRoute.FS81

end
