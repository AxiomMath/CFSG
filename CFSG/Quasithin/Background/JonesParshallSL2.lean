module

public import CFSG.Quasithin.Background.JonesParshallNatural

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix

section Sqrt

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

@[expose] def sqrtF (x : F) : F := (frobeniusEquiv F 2).symm x

theorem sqrtF_sq (x : F) : sqrtF x ^ 2 = x := by
  have h := (frobeniusEquiv F 2).apply_symm_apply x
  rwa [frobeniusEquiv_apply, frobenius_def] at h

theorem sq_inj {x y : F} (h : x ^ 2 = y ^ 2) : x = y := by
  apply (frobeniusEquiv F 2).injective
  rwa [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def]

theorem sqrtF_add (x y : F) : sqrtF (x + y) = sqrtF x + sqrtF y := map_add _ x y

theorem sqrtF_mul (x y : F) : sqrtF (x * y) = sqrtF x * sqrtF y := map_mul _ x y

theorem sqrtF_zero : sqrtF (0 : F) = 0 := map_zero _

theorem sqrtF_one : sqrtF (1 : F) = 1 := map_one _

theorem sqrtF_of_sq (x : F) : sqrtF (x ^ 2) = x := sq_inj (by rw [sqrtF_sq])

omit [Fintype F] in
theorem add_self_F (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

omit [Fintype F] in
theorem add_sq_F (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := CharTwo.add_sq x y

end Sqrt

variable {F : Type} [Field F]

abbrev SL2 (F : Type) [Field F] : Type := SpecialLinearGroup (Fin 2) F

@[expose] def mu2 : SL2 F →* AddMonoid.End (Fin 2 → F) := DistribMulAction.toAddMonoidEnd _ _

theorem mu2_apply (g : SL2 F) (v : Fin 2 → F) :
    mu2 g v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v := rfl

theorem mulVec_two_zero (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_two_one (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def uMat (x : F) : SL2 F := ⟨!![1, x; 0, 1], by simp [det_fin_two]⟩

@[expose] def tMat (c : F) (hc : c ≠ 0) : SL2 F := ⟨!![c, 0; 0, c⁻¹], by simp [det_fin_two, hc]⟩

theorem uMat_coe (x : F) : ((uMat x : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem tMat_coe (c : F) (hc : c ≠ 0) :
    ((tMat c hc : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![c, 0; 0, c⁻¹] := rfl

theorem uMat_mul (x y : F) : uMat x * uMat y = uMat (x + y) := by
  apply Subtype.ext
  change !![(1 : F), x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1]
  rw [mul_fin_two]
  simp [add_comm]

theorem uMat_zero : uMat (0 : F) = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0; 0, 1] = 1
  exact (one_fin_two).symm

theorem tMat_conj (c : F) (hc : c ≠ 0) (x : F) :
    tMat c hc * uMat x * (tMat c hc)⁻¹ = uMat (c ^ 2 * x) := by
  apply Subtype.ext
  change !![c, 0; 0, c⁻¹] * !![(1 : F), x; 0, 1] * adjugate !![c, 0; 0, c⁻¹] =
    !![1, c ^ 2 * x; 0, 1]
  rw [adjugate_fin_two, mul_fin_two, mul_fin_two]
  have h1 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have h2 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2]
  ring

variable [Fintype F] [CharP F 2]

@[expose] def f0 (g : SL2 F) : Fin 2 → F :=
  ![sqrtF ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1),
    sqrtF ((g : Matrix (Fin 2) (Fin 2) F) 1 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1)]

theorem f0_mem : f0 ∈ Z1A (mu2 (F := F)) := by
  intro g h
  have hdet : (h : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (h : Matrix (Fin 2) (Fin 2) F) 0 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := h.2
    rwa [det_fin_two] at this
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hgh : ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) := rfl
  set G := (g : Matrix (Fin 2) (Fin 2) F)
  set H := (h : Matrix (Fin 2) (Fin 2) F)
  funext i
  rw [mu2_apply, Pi.add_apply]
  fin_cases i
  · change sqrtF (((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 *
      ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1) = sqrtF (G 0 0 * G 0 1) + (G *ᵥ f0 h) 0
    rw [mulVec_two_zero, hgh]
    apply sq_inj
    rw [sqrtF_sq, add_sq_F, add_sq_F, sqrtF_sq, mul_pow, mul_pow]
    change (G * H) 0 0 * (G * H) 0 1 = G 0 0 * G 0 1 + (G 0 0 ^ 2 * sqrtF (H 0 0 * H 0 1) ^ 2 +
      G 0 1 ^ 2 * sqrtF (H 1 0 * H 1 1) ^ 2)
    rw [sqrtF_sq, sqrtF_sq]
    simp only [mul_apply, Fin.sum_univ_two]
    linear_combination (G 0 0 * G 0 1) * hdet + (G 0 0 * G 0 1 * H 0 1 * H 1 0) * h2
  · change sqrtF (((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 *
      ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1) = sqrtF (G 1 0 * G 1 1) + (G *ᵥ f0 h) 1
    rw [mulVec_two_one, hgh]
    apply sq_inj
    rw [sqrtF_sq, add_sq_F, add_sq_F, sqrtF_sq, mul_pow, mul_pow]
    change (G * H) 1 0 * (G * H) 1 1 = G 1 0 * G 1 1 + (G 1 0 ^ 2 * sqrtF (H 0 0 * H 0 1) ^ 2 +
      G 1 1 ^ 2 * sqrtF (H 1 0 * H 1 1) ^ 2)
    rw [sqrtF_sq, sqrtF_sq]
    simp only [mul_apply, Fin.sum_univ_two]
    linear_combination (G 1 0 * G 1 1) * hdet + (G 1 0 * G 1 1 * H 0 1 * H 1 0) * h2

theorem smul_f0_mem (B : F) : B • f0 ∈ Z1A (mu2 (F := F)) := by
  intro g h
  rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, f0_mem g h, smul_add, mu2_apply, mu2_apply,
    mulVec_smul]

theorem f0_uMat (x : F) : f0 (uMat x) = ![sqrtF x, 0] := by
  funext i
  fin_cases i
  · change sqrtF (1 * x) = sqrtF x
    rw [one_mul]
  · change sqrtF (0 * 1) = 0
    rw [zero_mul, sqrtF_zero]

theorem alpha_eq {α : F → F} (h0 : α 0 = 0)
    (hrel : ∀ c : F, c ≠ 0 → ∃ κ : F, ∀ x, α (c ^ 2 * x) = c * α x + κ * x)
    {c₀ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1) (x : F) :
    α x = (c₀ * α 1 - α (c₀ ^ 2)) / (c₀ - c₀ ^ 2) * x +
      (α (c₀ ^ 2) - c₀ ^ 2 * α 1) / (c₀ - c₀ ^ 2) * sqrtF x := by
  have hden : c₀ - c₀ ^ 2 ≠ 0 := by
    have : c₀ - c₀ ^ 2 = c₀ * (1 - c₀) := by ring
    rw [this]
    exact mul_ne_zero hc₀ (sub_ne_zero.mpr (Ne.symm hc₁))
  obtain ⟨κ₀, hκ₀⟩ := hrel c₀ hc₀
  have hκ₀' : κ₀ = α (c₀ ^ 2) - c₀ * α 1 := by
    have h1 := hκ₀ 1
    rw [mul_one, mul_one] at h1
    linear_combination -h1
  obtain ⟨d, rfl⟩ : ∃ d, x = d ^ 2 := ⟨sqrtF x, (sqrtF_sq x).symm⟩
  rw [sqrtF_of_sq]
  by_cases hd0 : d = 0
  · subst hd0
    simp [h0]
  obtain ⟨κ, hκ⟩ := hrel d hd0
  have hκ' : κ = α (d ^ 2) - d * α 1 := by
    have h1 := hκ 1
    rw [mul_one, mul_one] at h1
    linear_combination -h1
  have e1 := hκ₀ (d ^ 2)
  have e2 := hκ (c₀ ^ 2)
  rw [mul_comm (d ^ 2) (c₀ ^ 2)] at e2
  rw [hκ₀'] at e1
  rw [hκ'] at e2
  field_simp
  linear_combination e2 - e1

theorem exists_sub_mem_B1A {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {f : SL2 F → (Fin 2 → F)} (hf : f ∈ Z1A (mu2 (F := F))) :
    ∃ B : F, f - B • f0 ∈ B1A (mu2 (F := F)) := by
  classical
  set α : F → F := fun x => f (uMat x) 0 with hα_def
  have hcoc : ∀ x y, f (uMat (x + y)) = f (uMat x) + mu2 (uMat x) (f (uMat y)) := fun x y => by
    rw [← uMat_mul, hf]
  have hf1 : f 1 = 0 := Z1A_one hf
  have hβ : ∀ x, f (uMat x) 1 = 0 := fun x => by
    have h := congrFun (hcoc x x) 0
    rw [add_self_F, uMat_zero, hf1, Pi.add_apply, mu2_apply, mulVec_two_zero, uMat_coe] at h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      one_mul, Pi.zero_apply] at h
    have h' : x * f (uMat x) 1 = 0 := by
      have := add_self_F (f (uMat x) 0)
      linear_combination -h - this
    rcases mul_eq_zero.mp h' with hx | hx
    · rw [hx, uMat_zero, hf1, Pi.zero_apply]
    · exact hx
  have hα0 : α 0 = 0 := by
    change f (uMat 0) 0 = 0
    rw [uMat_zero, hf1, Pi.zero_apply]
  have hrel : ∀ c : F, c ≠ 0 → ∃ κ : F, ∀ x, α (c ^ 2 * x) = c * α x + κ * x := by
    intro c hc
    refine ⟨-(c ^ 2 * f (tMat c hc) 1), fun x => ?_⟩
    have h := congrFun (Z1A_conj hf (tMat c hc) (uMat x)) 0
    rw [tMat_conj] at h
    change f (uMat (c ^ 2 * x)) 0 = c * f (uMat x) 0 + -(c ^ 2 * f (tMat c hc) 1) * x
    rw [h, Pi.sub_apply, Pi.add_apply, mu2_apply, mu2_apply, mulVec_two_zero, mulVec_two_zero,
      tMat_coe, uMat_coe, hβ]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      one_mul, mul_zero, add_zero]
    ring
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ, hF]
      calc ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
        _ < 2 ^ a := by
          calc 2 = 2 ^ 1 := by norm_num
            _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₀
  set A := (c₀ * α 1 - α (c₀ ^ 2)) / (c₀ - c₀ ^ 2)
  set B := (α (c₀ ^ 2) - c₀ ^ 2 * α 1) / (c₀ - c₀ ^ 2)
  have hαeq : ∀ x, α x = A * x + B * sqrtF x := alpha_eq hα0 hrel hc₀.1 hc₀.2
  refine ⟨B, ?_⟩
  set f' := f - B • f0 - coboundaryA (mu2 (F := F)) ![0, A] with hf'_def
  have hf' : f' ∈ Z1A (mu2 (F := F)) :=
    sub_mem (sub_mem hf (smul_f0_mem B)) (B1A_le_Z1A _ ⟨_, rfl⟩)
  have hvan : ∀ x, f' (uMat x) = 0 := fun x => by
    funext i
    simp only [hf'_def, Pi.sub_apply, Pi.smul_apply, coboundaryA_apply, f0_uMat, mu2_apply,
      uMat_coe]
    fin_cases i
    · change f (uMat x) 0 - B • sqrtF x - ((!![1, x; 0, 1] *ᵥ ![0, A]) 0 - 0) = 0
      rw [mulVec_two_zero]
      have := hαeq x
      simp only [hα_def] at this
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        mul_zero, zero_add, smul_eq_mul, sub_zero]
      rw [this]
      ring
    · change f (uMat x) 1 - B • 0 - ((!![1, x; 0, 1] *ᵥ ![0, A]) 1 - A) = 0
      rw [mulVec_two_one, hβ]
      simp
  set e₁ : Fin 2 → F := ![1, 0]
  set H := MulAction.stabilizer (SL2 F) e₁
  have hH : ∀ g ∈ H, f' g = 0 := fun g hg => by
    have hg' : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ e₁ = e₁ := hg
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      have := congrFun hg' 0
      rw [mulVec_two_zero] at this
      simpa [e₁] using this
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have := congrFun hg' 1
      rw [mulVec_two_one] at this
      simpa [e₁] using this
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have := g.2
      rw [det_fin_two, h00, h10] at this
      simpa using this
    have hgu : g = uMat ((g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uMat_coe, h00, h10, h11]
    rw [hgu]
    exact hvan _
  have horbit : MulAction.orbit (SL2 F) e₁ = {v | v ≠ 0} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩ h0
      have : e₁ = g⁻¹ • (g • e₁) := (inv_smul_smul g e₁).symm
      rw [h0, smul_zero] at this
      exact absurd (congrFun this 0) (by simp [e₁])
    · intro hv
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
        refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, funext fun i => ?_⟩
        fin_cases i
        · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 0 = v 0
          rw [mulVec_two_zero]
          simp [e₁, h0]
        · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 1 = v 1
          rw [mulVec_two_one]
          simp [e₁]
      · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, funext fun i => ?_⟩
        fin_cases i
        · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 0 = v 0
          rw [mulVec_two_zero]
          simp [e₁]
        · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 1 = v 1
          rw [mulVec_two_one]
          simp [e₁]
  have hindex : H.index = 2 ^ (2 * a) - 1 := by
    rw [MulAction.index_stabilizer, horbit]
    have hc : ({v : Fin 2 → F | v ≠ 0} : Set (Fin 2 → F)) = {0}ᶜ := by
      ext v
      simp
    rw [hc, Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin, hF, ← pow_mul, mul_comm]
  have hodd : Odd H.index := by
    rw [hindex]
    have hpos : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
    obtain ⟨k, hk⟩ : ∃ k, 2 * a = k + 1 := ⟨2 * a - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
  have h2 : ∀ m : Fin 2 → F, m + m = 0 := fun m => funext fun i => add_self_F (m i)
  have hB := mem_B1A_of_vanish h2 hodd hf' hH
  have := add_mem hB (⟨![0, A], rfl⟩ : coboundaryA (mu2 (F := F)) ![0, A] ∈ B1A _)
  rwa [hf'_def, sub_add_cancel] at this

theorem eq_zero_of_smul_f0_mem_B1A (hcard : 2 < Fintype.card F) {B : F}
    (h : B • f0 ∈ B1A (mu2 (F := F))) : B = 0 := by
  classical
  obtain ⟨v, hv⟩ := h
  have hx : ∀ x, x * v 1 = B * sqrtF x := fun x => by
    have h := congrFun (congrFun hv (uMat x)) 0
    rw [coboundaryA_apply, Pi.smul_apply, f0_uMat, Pi.sub_apply, mu2_apply, mulVec_two_zero,
      uMat_coe] at h
    simpa using h
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt Finset.card_le_two hcard)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₀
  have h1 := hx 1
  rw [one_mul, sqrtF_one, mul_one] at h1
  have h2 := hx (c₀ ^ 2)
  rw [sqrtF_of_sq, h1] at h2
  have : B * (c₀ * (c₀ - 1)) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with hB | hc
  · exact hB
  · rcases mul_eq_zero.mp hc with hc | hc
    · exact absurd hc hc₀.1
    · exact absurd (sub_eq_zero.mp hc) hc₀.2

theorem card_Z1A_mu2 {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) :
    Nat.card (Z1A (mu2 (F := F))) = Fintype.card F * Nat.card (B1A (mu2 (F := F))) := by
  have hcard : 2 < Fintype.card F := by
    rw [hF]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha
  let Φ : F × B1A (mu2 (F := F)) → Z1A (mu2 (F := F)) := fun p =>
    ⟨p.1 • f0 + (p.2 : SL2 F → (Fin 2 → F)), add_mem (smul_f0_mem p.1) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨B, b⟩ ⟨B', b'⟩ h
      have h' : B • f0 (F := F) + (b : SL2 F → (Fin 2 → F)) = B' • f0 (F := F) + b' := by
        simpa [Φ] using congrArg Subtype.val h
      have hBB : (B - B') • (f0 : SL2 F → (Fin 2 → F)) ∈ B1A (mu2 (F := F)) := by
        have : (B - B') • (f0 : SL2 F → (Fin 2 → F)) = (b' : SL2 F → (Fin 2 → F)) - b := by
          calc (B - B') • (f0 : SL2 F → (Fin 2 → F)) =
              (B • f0 (F := F) + (b : SL2 F → (Fin 2 → F))) - (B' • f0 (F := F) + b) := by
                rw [sub_smul]
                abel
            _ = (B' • f0 (F := F) + b') - (B' • f0 (F := F) + b) := by rw [h']
            _ = b' - b := by abel
        rw [this]
        exact sub_mem b'.2 b.2
      have hB : B = B' := sub_eq_zero.mp (eq_zero_of_smul_f0_mem_B1A hcard hBB)
      subst hB
      have hb : (b : SL2 F → (Fin 2 → F)) = b' := add_left_cancel h'
      exact Prod.ext rfl (Subtype.ext hb)
    · rintro ⟨f, hf⟩
      obtain ⟨B, hB⟩ := exists_sub_mem_B1A hF ha hf
      exact ⟨(B, ⟨_, hB⟩), Subtype.ext (by simp [Φ])⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_eq_fintype_card]

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_SL2 {ρ : Representation (ZMod 2) Γ W} {a : ℕ} (hF : Fintype.card F = 2 ^ a)
    (ha : 1 < a) (h : Explicit.BinaryNaturalSL ρ 2 F .natural) :
    Module.finrank (ZMod 2) (H1 ρ) = a := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSL.intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = mu2 (θ γ) (β w) := hβ
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (card_Z1A_mu2 hF ha), hF]

end CFSG.Quasithin.JonesParshall
