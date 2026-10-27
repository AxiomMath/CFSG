module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDefs
import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] noncomputable def fixCount (M : Matrix (Fin 8) (Fin 8) (ZMod 3)) : ℕ :=
  Nat.card {v : Fin 8 → ZMod 3 // M *ᵥ v = v}

theorem fixCount_conj {g g' M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (h₁ : g * g' = 1)
    (h₂ : g' * g = 1) : fixCount (g * M * g') = fixCount M := by
  have fwd : ∀ w : Fin 8 → ZMod 3, (g * M * g') *ᵥ w = w → M *ᵥ (g' *ᵥ w) = g' *ᵥ w := by
    intro w e
    have h := congrArg (fun x => g' *ᵥ x) e
    rw [Matrix.mulVec_mulVec] at h
    have hprod : g' * (g * M * g') = (g' * g) * (M * g') := by simp only [mul_assoc]
    rw [hprod, h₂, one_mul] at h
    rw [Matrix.mulVec_mulVec]
    exact h
  have bwd : ∀ w : Fin 8 → ZMod 3, M *ᵥ w = w → (g * M * g') *ᵥ (g *ᵥ w) = g *ᵥ w := by
    intro w e
    rw [Matrix.mulVec_mulVec]
    have hprod : (g * M * g') * g = g * M := by
      calc (g * M * g') * g = g * (M * (g' * g)) := by simp only [mul_assoc]
        _ = g * M := by rw [h₂, mul_one]
    rw [hprod, ← Matrix.mulVec_mulVec, e]
  unfold fixCount
  exact Nat.card_congr
    { toFun := fun v => ⟨g' *ᵥ v.1, fwd v.1 v.2⟩
      invFun := fun v => ⟨g *ᵥ v.1, bwd v.1 v.2⟩
      left_inv := fun v => Subtype.ext (by
        show g *ᵥ (g' *ᵥ v.1) = v.1
        rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec])
      right_inv := fun v => Subtype.ext (by
        show g' *ᵥ (g *ᵥ v.1) = v.1
        rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]) }

private theorem q2nN7_sgn_mulVec_eq_self_iff (S : Finset (Fin 8)) (v : Fin 8 → ZMod 3) :
    sgn S *ᵥ v = v ↔ ∀ i ∈ S, v i = 0 := by
  have hsgn : sgn S = spMat 1 (sgnOn S) := by
    rw [q2nN7_sgn_eq_spMat]
    rfl
  constructor
  · intro h i hi
    exact eq_zero_of_mulVec_sgnOn (v := v) (T := S) (by rw [← hsgn]; exact h) hi
  · intro h
    funext i
    rw [q2nN7_sgn_mulVec]
    dsimp only
    by_cases hi : i ∈ S
    · rw [if_pos hi, h i hi]
      decide
    · rw [if_neg hi]

private def q2nN7_vanishingEquiv (S : Finset (Fin 8)) :
    {v : Fin 8 → ZMod 3 // ∀ i ∈ S, v i = 0} ≃ ({i : Fin 8 // i ∉ S} → ZMod 3) where
  toFun v := fun i => v.1 i.1
  invFun w := ⟨fun i => if h : i ∈ S then 0 else w ⟨i, h⟩, by
    intro i hi
    simpa only [dif_pos hi]⟩
  left_inv := by
    intro v
    refine Subtype.ext ?_
    funext i
    dsimp only
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
      exact (v.2 i hi).symm
    · rw [dif_neg hi]
  right_inv := by
    intro w
    funext i
    cases i with
    | mk i hi => simp only [dif_neg hi]

theorem q2nN7_fixCount_sgn (S : Finset (Fin 8)) : fixCount (sgn S) = 3 ^ (8 - S.card) := by
  have hcard : Fintype.card {i : Fin 8 // i ∉ S} = 8 - S.card := by
    rw [Fintype.card_subtype_compl (fun i => i ∈ S), Fintype.card_fin]
    exact congrArg (fun n => 8 - n) (Fintype.card_coe S)
  unfold fixCount
  rw [Nat.card_congr ((Equiv.subtypeEquivRight fun v =>
    q2nN7_sgn_mulVec_eq_self_iff S v).trans (q2nN7_vanishingEquiv S))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcard]

theorem fixCount_of_mem_E6set {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ E6set) :
    fixCount M = 9 := by
  obtain ⟨S, -, hS, rfl⟩ := hM
  rw [q2nN7_fixCount_sgn, hS]
  norm_num

private def q2nN7_goodVec (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) (j : Fin 8) :
    Fin 8 → ZMod 3 :=
  Pi.single j 1 + if σ j = j then 0 else Pi.single (σ j) (s j)

private theorem q2nN7_goodVec_self (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (j : Fin 8) : q2nN7_goodVec σ s j j = 1 := by
  simp only [q2nN7_goodVec, Pi.add_apply, Pi.single_eq_same]
  by_cases h : σ j = j
  · simp only [h, if_true, Pi.zero_apply, add_zero]
  · simp only [h, if_false, Pi.single_eq_of_ne (Ne.symm h), add_zero]

private theorem q2nN7_goodVec_eq_zero (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3)
    (j k : Fin 8) (hjk : k ≠ j) (hσjk : k ≠ σ j) : q2nN7_goodVec σ s j k = 0 := by
  simp only [q2nN7_goodVec, Pi.add_apply, Pi.single_eq_of_ne hjk, Pi.zero_apply]
  by_cases h : σ j = j
  · simp only [h, if_true, Pi.zero_apply, zero_add]
  · simp only [h, if_false, Pi.single_eq_of_ne hσjk, add_zero]

private def q2nN7_comb (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) (i i' : Fin 8)
    (c : Fin 3 → ZMod 3) : Fin 8 → ZMod 3 :=
  c 0 • e0 + c 1 • q2nN7_goodVec σ s i + c 2 • q2nN7_goodVec σ s i'

private theorem q2nN7_spMat_mulVec_e0 {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ0 : σ 0 = 0) (hs0 : s 0 = 1) : spMat σ s *ᵥ e0 = e0 := by
  simpa only [e0] using spMat_mulVec_e0 (n := 7) hσ0 hs0

private theorem q2nN7_spMat_mulVec_goodVec {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1) {j : Fin 8}
    (hgj : σ j ≠ j ∨ s j = 1) :
    spMat σ s *ᵥ q2nN7_goodVec σ s j = q2nN7_goodVec σ s j := by
  by_cases hfix : σ j = j
  · have hs1 : s j = 1 := by
      rcases hgj with h | h
      · exact absurd hfix h
      · exact h
    simp only [q2nN7_goodVec, hfix, if_true, Matrix.mulVec_add, Matrix.mulVec_zero, add_zero,
      spMat_mulVec_single, hs1, mul_one]
  · have hif : (if σ j = j then (0 : Fin 8 → ZMod 3) else Pi.single (σ j) (s j))
        = Pi.single (σ j) (s j) := if_neg hfix
    simp only [q2nN7_goodVec, hif, Matrix.mulVec_add, spMat_mulVec_single]
    obtain ⟨hσj, hsj⟩ := hsq j
    rw [hσj, hsj, mul_one]
    exact add_comm _ _

private theorem q2nN7_comb_fixed {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    {i i' : Fin 8} (hσ0 : σ 0 = 0) (hs0 : s 0 = 1)
    (hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1)
    (hgi : σ i ≠ i ∨ s i = 1) (hgi' : σ i' ≠ i' ∨ s i' = 1) (c : Fin 3 → ZMod 3) :
    spMat σ s *ᵥ q2nN7_comb σ s i i' c = q2nN7_comb σ s i i' c := by
  simp only [q2nN7_comb, Matrix.mulVec_add, Matrix.mulVec_smul,
    q2nN7_spMat_mulVec_e0 hσ0 hs0,
    q2nN7_spMat_mulVec_goodVec hsq hgi,
    q2nN7_spMat_mulVec_goodVec hsq hgi']

theorem q2nN7_fixCount_ge_27 {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hσ0 : σ 0 = 0)
    (hs0 : s 0 = 1) (hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1) {i i' : Fin 8} (hi : i ≠ 0)
    (hi' : i' ≠ 0) (hgi : σ i ≠ i ∨ s i = 1) (hgi' : σ i' ≠ i' ∨ s i' = 1) (h1 : i' ≠ i)
    (h2 : i' ≠ σ i) : 27 ≤ fixCount (spMat σ s) := by
  have hσi0 : σ i ≠ 0 := by
    intro h
    have h' : i = σ (σ i) := (hsq i).1.symm
    rw [h, hσ0] at h'
    exact hi h'
  have hσi'0 : σ i' ≠ 0 := by
    intro h
    have h' : i' = σ (σ i') := (hsq i').1.symm
    rw [h, hσ0] at h'
    exact hi' h'
  have hiσi' : i ≠ σ i' := by
    intro h
    apply h2
    calc i' = σ (σ i') := (hsq i').1.symm
      _ = σ i := by rw [← h]
  have hfi0 : q2nN7_goodVec σ s i 0 = 0 :=
    q2nN7_goodVec_eq_zero σ s i 0 (Ne.symm hi) (Ne.symm hσi0)
  have hfi'0 : q2nN7_goodVec σ s i' 0 = 0 :=
    q2nN7_goodVec_eq_zero σ s i' 0 (Ne.symm hi') (Ne.symm hσi'0)
  have hfii : q2nN7_goodVec σ s i i = 1 := q2nN7_goodVec_self σ s i
  have hfi'i : q2nN7_goodVec σ s i' i = 0 :=
    q2nN7_goodVec_eq_zero σ s i' i (Ne.symm h1) hiσi'
  have hfii' : q2nN7_goodVec σ s i i' = 0 :=
    q2nN7_goodVec_eq_zero σ s i i' h1 h2
  have hfi'i' : q2nN7_goodVec σ s i' i' = 1 := q2nN7_goodVec_self σ s i'
  have he00 : e0 0 = 1 := by simp only [e0, Pi.single_eq_same]
  have he0i : e0 i = 0 := by
    simp only [e0, Pi.single_eq_of_ne hi, Pi.zero_apply]
  have he0i' : e0 i' = 0 := by
    simp only [e0, Pi.single_eq_of_ne hi', Pi.zero_apply]
  have hφinj : Function.Injective
      (fun c : Fin 3 → ZMod 3 =>
        (⟨q2nN7_comb σ s i i' c, q2nN7_comb_fixed hσ0 hs0 hsq hgi hgi' c⟩ :
          {v : Fin 8 → ZMod 3 // spMat σ s *ᵥ v = v})) := by
    intro c c' hc
    have hval : q2nN7_comb σ s i i' c = q2nN7_comb σ s i i' c' :=
      congrArg Subtype.val hc
    have h0 : c 0 = c' 0 := by
      have h := congrFun hval 0
      simp only [q2nN7_comb, Pi.add_apply, Pi.smul_apply, he00, hfi0, hfi'0,
        smul_zero, smul_eq_mul, mul_one, mul_zero, add_zero] at h
      exact h
    have h1' : c 1 = c' 1 := by
      have h := congrFun hval i
      simp only [q2nN7_comb, Pi.add_apply, Pi.smul_apply, he0i, hfii, hfi'i,
        smul_zero, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h
      exact h
    have h2' : c 2 = c' 2 := by
      have h := congrFun hval i'
      simp only [q2nN7_comb, Pi.add_apply, Pi.smul_apply, he0i', hfii', hfi'i',
        smul_zero, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h
      exact h
    funext k
    fin_cases k
    · exact h0
    · exact h1'
    · exact h2'
  have hcard : Nat.card (Fin 3 → ZMod 3) = 27 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  unfold fixCount
  calc 27 = Nat.card (Fin 3 → ZMod 3) := hcard.symm
    _ ≤ Nat.card {v : Fin 8 → ZMod 3 // spMat σ s *ᵥ v = v} :=
        Nat.card_le_card_of_injective _ hφinj

end CFSG.StandardType.FrameRoute.FS81

end
