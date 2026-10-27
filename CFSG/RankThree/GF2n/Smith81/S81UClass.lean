module

public import CFSG.RankThree.GF2n.Smith81.S81NComm
public import CFSG.ClassicalGroups.Unitary.InvolutionTransvection
public import CFSG.RankThree.GF2n.Smith81.S81UTrans

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] def IsHypPairs (σ : F ≃+* F) {j : ℕ} (a b : Fin j → (Fin 6 → F)) : Prop :=
  (∀ i l, herm σ (a i) (a l) = 0) ∧ (∀ i l, herm σ (b i) (b l) = 0) ∧
    ∀ i l, herm σ (a i) (b l) = if i = l then 1 else 0

@[expose] def OrthPairs (σ : F ≃+* F) {j : ℕ} (a b : Fin j → (Fin 6 → F)) (y : Fin 6 → F) : Prop :=
  ∀ i, herm σ (a i) y = 0 ∧ herm σ (b i) y = 0

private theorem h63_herm_sum_right {j : ℕ} (x : Fin 6 → F) (f : Fin j → (Fin 6 → F)) :
    herm σ x (∑ i, f i) = ∑ i, herm σ x (f i) := by
  simpa only [hermL_apply] using map_sum (CFSG.ClassicalGroups.Unitary.hermL σ x) f Finset.univ

private theorem h63_herm_ba (hσ : IsUnitaryInvolution σ) {j : ℕ} {a b : Fin j → (Fin 6 → F)}
    (hab : IsHypPairs σ a b) (i l : Fin j) : herm σ (b l) (a i) = if i = l then 1 else 0 := by
  unfold IsHypPairs at hab
  rw [herm_conj σ hσ.invol, hab.2.2 i l]
  split_ifs <;> simp

private theorem h63_proj {j : ℕ} (a b : Fin j → (Fin 6 → F)) :
    ∃ P : (Fin 6 → F) →ₗ[F] (Fin 6 → F), ∀ y,
      P y = y - ∑ i, (herm σ (b i) y • a i + herm σ (a i) y • b i) :=
  ⟨LinearMap.id - ∑ i, ((CFSG.ClassicalGroups.Unitary.hermL σ (b i)).smulRight (a i) + (CFSG.ClassicalGroups.Unitary.hermL σ (a i)).smulRight (b i)),
    fun y => by simp [LinearMap.sum_apply]⟩

private theorem h63_proj_orth (hσ : IsUnitaryInvolution σ) {j : ℕ} {a b : Fin j → (Fin 6 → F)}
    (hab : IsHypPairs σ a b) (y : Fin 6 → F) :
    OrthPairs σ a b (y - ∑ i, (herm σ (b i) y • a i + herm σ (a i) y • b i)) := by
  have hD := h63_herm_ba hσ hab
  unfold IsHypPairs at hab
  obtain ⟨hA, hB, hC⟩ := hab
  intro l
  constructor
  · rw [herm_sub_right, h63_herm_sum_right]
    simp [herm_add_right, herm_smul_right, hA, hC, mul_ite]
  · rw [herm_sub_right, h63_herm_sum_right]
    simp [herm_add_right, herm_smul_right, hB, hD, mul_ite]

private theorem h63_sum_mem {S : Set (Fin 6 → F)} {j : ℕ} {a b : Fin j → (Fin 6 → F)}
    (ha : ∀ i, a i ∈ Submodule.span F S) (hb : ∀ i, b i ∈ Submodule.span F S) (y : Fin 6 → F) :
    ∑ i, (herm σ (b i) y • a i + herm σ (a i) y • b i) ∈ Submodule.span F S :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ (ha i)) (Submodule.smul_mem _ _ (hb i))

private theorem h63_orth_smul {j : ℕ} {a b : Fin j → (Fin 6 → F)} {v : Fin 6 → F}
    (hv : OrthPairs σ a b v) (c : F) : OrthPairs σ a b (c • v) := by
  intro i
  exact ⟨by rw [herm_smul_right, (hv i).1, mul_zero], by rw [herm_smul_right, (hv i).2, mul_zero]⟩

theorem exists_hyp_pair_perp (hσ : IsUnitaryInvolution σ) {j : ℕ} (hj : j ≤ 2) {a b : Fin j → (Fin 6 → F)}
    (hab : IsHypPairs σ a b) :
    ∃ a' b' : Fin 6 → F, herm σ a' a' = 0 ∧ herm σ b' b' = 0 ∧ herm σ a' b' = 1 ∧
      OrthPairs σ a b a' ∧ OrthPairs σ a b b' := by
  obtain ⟨P, hPy⟩ := h63_proj (σ := σ) a b
  have hPorth : ∀ y, OrthPairs σ a b (P y) := fun y => by
    rw [hPy]
    exact h63_proj_orth hσ hab y
  have hPs1 : ∀ y (k : Fin (j + j)), herm σ (Fin.append a b k) (P y) = 0 := by
    intro y k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact (hPorth y i).1
    · rw [Fin.append_right]
      exact (hPorth y i).2
  have hP1 : ∀ y, y - P y ∈ Submodule.span F (Set.range (Fin.append a b)) := by
    intro y
    rw [hPy, sub_sub_cancel]
    exact h63_sum_mem (S := Set.range (Fin.append a b))
      (fun i => Submodule.subset_span ⟨Fin.castAdd j i, Fin.append_left _ _ i⟩)
      (fun i => Submodule.subset_span ⟨Fin.natAdd j i, Fin.append_right _ _ i⟩) y
  obtain ⟨y₀, hy₀⟩ := exists_aniso_of_lt hσ (k := j + j) (by omega) (Fin.append a b) P hP1 hPs1
  obtain ⟨c₁, hc₁⟩ := exists_smul_norm_one hσ hy₀
  obtain ⟨u₁, hu₁, hu₁n⟩ : ∃ u : Fin 6 → F, OrthPairs σ a b u ∧ herm σ u u = 1 :=
    ⟨c₁ • P y₀, h63_orth_smul (hPorth y₀) c₁, hc₁⟩
  obtain ⟨P₂, hP₂⟩ : ∃ Q : (Fin 6 → F) →ₗ[F] (Fin 6 → F),
      ∀ y, Q y = P y - herm σ u₁ (P y) • u₁ :=
    ⟨P - ((CFSG.ClassicalGroups.Unitary.hermL σ u₁).comp P).smulRight u₁, fun y => by simp⟩
  have hPorth2 : ∀ y, OrthPairs σ a b (P₂ y) := by
    intro y i
    rw [hP₂ y]
    exact ⟨by rw [herm_sub_right, herm_smul_right, (hPorth y i).1, (hu₁ i).1, mul_zero, sub_zero],
      by rw [herm_sub_right, herm_smul_right, (hPorth y i).2, (hu₁ i).2, mul_zero, sub_zero]⟩
  have hu₁P2 : ∀ y, herm σ u₁ (P₂ y) = 0 := by
    intro y
    rw [hP₂ y, herm_sub_right, herm_smul_right, hu₁n, mul_one, sub_self]
  have hPs2 : ∀ y (k : Fin (j + j + 1)),
      herm σ (Fin.append (Fin.append a b) ![u₁] k) (P₂ y) = 0 := by
    intro y k
    refine Fin.addCases (fun k' => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
      · rw [Fin.append_left]
        exact (hPorth2 y i).1
      · rw [Fin.append_right]
        exact (hPorth2 y i).2
    · rw [Fin.append_right]
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [Matrix.cons_val_zero]
      exact hu₁P2 y
  have hP2 : ∀ y,
      y - P₂ y ∈ Submodule.span F (Set.range (Fin.append (Fin.append a b) ![u₁])) := by
    have hA2 : ∀ i, a i ∈ Submodule.span F (Set.range (Fin.append (Fin.append a b) ![u₁])) :=
      fun i => Submodule.subset_span ⟨Fin.castAdd 1 (Fin.castAdd j i), by
        rw [Fin.append_left, Fin.append_left]⟩
    have hB2 : ∀ i, b i ∈ Submodule.span F (Set.range (Fin.append (Fin.append a b) ![u₁])) :=
      fun i => Submodule.subset_span ⟨Fin.castAdd 1 (Fin.natAdd j i), by
        rw [Fin.append_left, Fin.append_right]⟩
    have hU2 : u₁ ∈ Submodule.span F (Set.range (Fin.append (Fin.append a b) ![u₁])) :=
      Submodule.subset_span ⟨Fin.natAdd (j + j) 0, by simp⟩
    intro y
    have e : y - P₂ y = (y - P y) + herm σ u₁ (P y) • u₁ := by
      rw [hP₂ y]
      abel
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hU2)
    rw [hPy, sub_sub_cancel]
    exact h63_sum_mem hA2 hB2 y
  obtain ⟨y₁, hy₁⟩ := exists_aniso_of_lt hσ (k := j + j + 1) (by omega)
    (Fin.append (Fin.append a b) ![u₁]) P₂ hP2 hPs2
  obtain ⟨c₂, hc₂⟩ := exists_smul_norm_one hσ hy₁
  obtain ⟨u₂, hu₂, hu₂n, hu₁u₂⟩ : ∃ u : Fin 6 → F, OrthPairs σ a b u ∧ herm σ u u = 1 ∧
      herm σ u₁ u = 0 :=
    ⟨c₂ • P₂ y₁, h63_orth_smul (hPorth2 y₁) c₂, hc₂, by rw [herm_smul_right, hu₁P2, mul_zero]⟩
  have hu₂u₁ : herm σ u₂ u₁ = 0 := herm_eq_zero_comm σ hσ.invol hu₁u₂
  obtain ⟨τ, hτ⟩ := hσ.norm_surj 1 (map_one σ) one_ne_zero
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hzz : herm σ (u₁ + τ • u₂) (u₁ + τ • u₂) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu₁n, hu₁u₂,
      hu₂u₁, hu₂n]
    linear_combination hτ + h2
  have hz0 : u₁ + τ • u₂ ≠ 0 := by
    intro h
    have h1 : herm σ u₁ (u₁ + τ • u₂) = 1 := by
      rw [herm_add_right, herm_smul_right, hu₁n, hu₁u₂, mul_zero, add_zero]
    rw [h, herm_zero_right] at h1
    exact zero_ne_one h1
  have hzo : OrthPairs σ a b (u₁ + τ • u₂) := by
    intro i
    exact ⟨by rw [herm_add_right, herm_smul_right, (hu₁ i).1, (hu₂ i).1, mul_zero, add_zero],
      by rw [herm_add_right, herm_smul_right, (hu₁ i).2, (hu₂ i).2, mul_zero, add_zero]⟩
  obtain ⟨y, hy⟩ := exists_herm_eq_one σ hz0
  have hzA : ∀ i, herm σ (u₁ + τ • u₂) (a i) = 0 := fun i =>
    herm_eq_zero_comm σ hσ.invol (hzo i).1
  have hzB : ∀ i, herm σ (u₁ + τ • u₂) (b i) = 0 := fun i =>
    herm_eq_zero_comm σ hσ.invol (hzo i).2
  have hzPy : herm σ (u₁ + τ • u₂) (P y) = 1 := by
    rw [hPy, herm_sub_right, h63_herm_sum_right, hy]
    simp [herm_add_right, herm_smul_right, hzA, hzB]
  obtain ⟨c, hc⟩ := exists_isotropize hσ hzz hzPy
  refine ⟨u₁ + τ • u₂, P y + c • (u₁ + τ • u₂), hzz, hc, ?_, hzo, ?_⟩
  · rw [herm_add_right, herm_smul_right, hzz, mul_zero, add_zero, hzPy]
  · intro i
    exact ⟨by rw [herm_add_right, herm_smul_right, (hPorth y i).1, (hzo i).1, mul_zero, add_zero],
      by rw [herm_add_right, herm_smul_right, (hPorth y i).2, (hzo i).2, mul_zero, add_zero]⟩

theorem herm_N_perp (hσ : ∀ c, σ (σ c) = c) {t : SUid σ 6} (ht : t * t = 1) {j : ℕ}
    {a b : Fin j → (Fin 6 → F)} (hN : ∀ i, t • a i - a i = 0)
    (hNb : ∀ i, t • b i - b i = a i ∨ t • b i - b i = 0) {y : Fin 6 → F}
    (hy : OrthPairs σ a b y) : OrthPairs σ a b (t • y - y) := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [herm_smul_sub_self_right hσ ht (a i) y, hN i, herm_zero_left]
  · rw [herm_smul_sub_self_right hσ ht (b i) y]
    rcases hNb i with h | h
    · rw [h]
      exact (hy i).1
    · rw [h, herm_zero_left]

private theorem h64_herm_sum_left {j : ℕ} (x : Fin j → (Fin 6 → F)) (z : Fin 6 → F) :
    herm σ (∑ i, x i) z = ∑ i, herm σ (x i) z := by
  simp only [herm, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem h64_herm_sum_right {j : ℕ} (z : Fin 6 → F) (x : Fin j → (Fin 6 → F)) :
    herm σ z (∑ i, x i) = ∑ i, herm σ z (x i) := by
  simp only [herm, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

private theorem h64_N_add (t : SUid σ 6) (x y : Fin 6 → F) :
    t • (x + y) - (x + y) = (t • x - x) + (t • y - y) := by
  rw [smul_add]
  abel

private theorem h64_N_add_smul (t : SUid σ 6) (x y : Fin 6 → F) (c : F) :
    t • (x + c • y) - (x + c • y) = (t • x - x) + c • (t • y - y) := by
  rw [smul_add, smul_comm t c y, smul_sub]
  abel

private theorem h64_N_smul (t : SUid σ 6) (c : F) (y : Fin 6 → F) :
    t • (c • y) - c • y = c • (t • y - y) := by
  rw [smul_sub, smul_comm t c y]

private theorem h64_Y_add {j : ℕ} {a b : Fin j → (Fin 6 → F)} {u v : Fin 6 → F}
    (hu : OrthPairs σ a b u) (hv : OrthPairs σ a b v) : OrthPairs σ a b (u + v) := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [herm_add_right, (hu i).1, (hv i).1, add_zero]
  · rw [herm_add_right, (hu i).2, (hv i).2, add_zero]

private theorem h64_Y_smul {j : ℕ} {a b : Fin j → (Fin 6 → F)} {u : Fin 6 → F} (c : F)
    (hu : OrthPairs σ a b u) : OrthPairs σ a b (c • u) := by
  intro i
  refine ⟨?_, ?_⟩
  · rw [herm_smul_right, (hu i).1, mul_zero]
  · rw [herm_smul_right, (hu i).2, mul_zero]

private theorem h64_proj_mem {j : ℕ} {a b : Fin j → (Fin 6 → F)} (hσ : IsUnitaryInvolution σ)
    (hab : IsHypPairs σ a b) (w : Fin 6 → F) :
    OrthPairs σ a b (w - ∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) := by
  obtain ⟨hAA, hBB, hAB⟩ := hab
  have hBA : ∀ i l, herm σ (b l) (a i) = if i = l then 1 else 0 := by
    intro i l
    rw [herm_conj σ hσ.invol (a i) (b l), hAB i l]
    split_ifs <;> simp
  intro l
  have hSa : herm σ (a l) (∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) =
      herm σ (a l) w := by
    rw [h64_herm_sum_right]
    simp [herm_add_right, herm_smul_right, hAA, hAB, mul_ite]
  have hSb : herm σ (b l) (∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) =
      herm σ (b l) w := by
    rw [h64_herm_sum_right]
    simp [herm_add_right, herm_smul_right, hBA, hBB, mul_ite]
  exact ⟨by rw [herm_sub_right, hSa, sub_self], by rw [herm_sub_right, hSb, sub_self]⟩

theorem exists_typeI_pair (hσ : IsUnitaryInvolution σ) {t : SUid σ 6} (ht : t * t = 1) {j : ℕ}
    {a b : Fin j → (Fin 6 → F)} (hab : IsHypPairs σ a b) (hN : ∀ i, t • a i - a i = 0)
    (hNb : ∀ i, t • b i - b i = a i ∨ t • b i - b i = 0) {y : Fin 6 → F}
    (hy : OrthPairs σ a b y) (hNy : t • y - y ≠ 0) :
    ∃ a' b' : Fin 6 → F, herm σ a' a' = 0 ∧ herm σ b' b' = 0 ∧ herm σ a' b' = 1 ∧
      OrthPairs σ a b a' ∧ OrthPairs σ a b b' ∧ t • a' - a' = 0 ∧ t • b' - b' = a' := by
  have hinv : ∀ c, σ (σ c) = c := hσ.invol
  have hNyP : OrthPairs σ a b (t • y - y) := herm_N_perp hinv ht hN hNb hy
  obtain ⟨u₀, hu₀, hd₀⟩ : ∃ u₀ : Fin 6 → F, OrthPairs σ a b u₀ ∧ herm σ (t • u₀ - u₀) u₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have pol : ∀ u v : Fin 6 → F, OrthPairs σ a b u → OrthPairs σ a b v →
        herm σ (t • u - u) v + herm σ (t • v - v) u = 0 := by
      intro u v hu hv
      have h0 := hcon (u + v) (h64_Y_add hu hv)
      rw [h64_N_add, herm_add_left, herm_add_right, herm_add_right, hcon u hu, hcon v hv] at h0
      linear_combination h0
    obtain ⟨lam, hlam⟩ := hσ.exists_ne
    have hlam' : lam - σ lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
    have key : ∀ u v : Fin 6 → F, OrthPairs σ a b u → OrthPairs σ a b v →
        herm σ (t • u - u) v = 0 := by
      intro u v hu hv
      have h1 := pol u v hu hv
      have h2 := pol u (lam • v) hu (h64_Y_smul lam hv)
      rw [h64_N_smul, herm_smul_right, herm_smul_left] at h2
      have h3 : (lam - σ lam) * herm σ (t • u - u) v = 0 := by
        linear_combination h2 - σ lam * h1
      exact (mul_eq_zero.mp h3).resolve_left hlam'
    have hw : ∀ w : Fin 6 → F, herm σ w (t • y - y) = 0 := by
      intro w
      have hP := h64_proj_mem hσ hab w
      have hPN : herm σ (w - ∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i))
          (t • y - y) = 0 := by
        rw [herm_smul_sub_self_right hinv ht]
        exact key _ y hP hy
      have hSN : herm σ (∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) (t • y - y) = 0 := by
        rw [h64_herm_sum_left]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [herm_add_left, herm_smul_left, herm_smul_left, (hNyP i).1, (hNyP i).2, mul_zero,
          mul_zero, add_zero]
      have hsplit : herm σ w (t • y - y) =
          herm σ (w - ∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) (t • y - y) +
            herm σ (∑ i, (herm σ (b i) w • a i + herm σ (a i) w • b i)) (t • y - y) := by
        rw [← herm_add_left, sub_add_cancel]
      rw [hsplit, hPN, hSN, add_zero]
    apply hNy
    exact eq_zero_of_herm σ fun w => herm_eq_zero_comm σ hinv (hw w)
  obtain ⟨c, hc⟩ := hσ.norm_surj (herm σ (t • u₀ - u₀) u₀)⁻¹
    (by rw [map_inv₀, herm_smul_sub_self_fixed hσ ht u₀]) (inv_ne_zero hd₀)
  obtain ⟨u, hu, hNu⟩ : ∃ u : Fin 6 → F, OrthPairs σ a b u ∧ herm σ (t • u - u) u = 1 :=
    ⟨c • u₀, h64_Y_smul c hu₀, by
      rw [h64_N_smul, herm_smul_left, herm_smul_right, ← mul_assoc, hc, inv_mul_cancel₀ hd₀]⟩
  have hA1 : herm σ u (t • u - u) = 1 := by
    rw [herm_smul_sub_self_right hinv ht]
    exact hNu
  have hA3 : herm σ (t • u - u) (t • u - u) = 0 := herm_smul_sub_self_self hinv ht u u
  obtain ⟨c', hc'⟩ := hσ.trace_surj (-herm σ u u) (by rw [map_neg, herm_self_fixed σ hinv u])
  have hb0 : herm σ (u + c' • (t • u - u)) (u + c' • (t • u - u)) = 0 := by
    have hexp : herm σ (u + c' • (t • u - u)) (u + c' • (t • u - u)) =
        herm σ u u + (c' + σ c') := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hA1, hNu, hA3,
        mul_zero, mul_one, add_zero]
      ring
    rw [hexp]
    linear_combination hc'
  have hab1 : herm σ (t • u - u) (u + c' • (t • u - u)) = 1 := by
    simp only [herm_add_right, herm_smul_right, hNu, hA3, mul_zero, add_zero]
  have hOa : OrthPairs σ a b (t • u - u) := herm_N_perp hinv ht hN hNb hu
  have hOb : OrthPairs σ a b (u + c' • (t • u - u)) := h64_Y_add hu (h64_Y_smul c' hOa)
  have hta : t • (t • u - u) - (t • u - u) = 0 := smul_sub_self_smul_sub_self ht u
  have htb : t • (u + c' • (t • u - u)) - (u + c' • (t • u - u)) = t • u - u := by
    rw [h64_N_add_smul, hta, smul_zero, add_zero]
  exact ⟨t • u - u, u + c' • (t • u - u), hA3, hb0, hab1, hOa, hOb, hta, htb⟩

private theorem h65_snoc_hyp {j : ℕ} {a b : Fin j → (Fin 6 → F)} {a' b' : Fin 6 → F}
    (hs : ∀ c, σ (σ c) = c) (hab : IsHypPairs σ a b) (ha' : herm σ a' a' = 0)
    (hb' : herm σ b' b' = 0) (hab' : herm σ a' b' = 1) (hoa : OrthPairs σ a b a')
    (hob : OrthPairs σ a b b') :
    IsHypPairs σ (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F))
      (Fin.snoc b b' : Fin (j + 1) → (Fin 6 → F)) := by
  obtain ⟨h1, h2, h3⟩ := hab
  have oa : ∀ i, herm σ a' (a i) = 0 := fun i =>
    CFSG.ClassicalGroups.Unitary.herm_eq_zero_comm σ hs (hoa i).1
  have ob : ∀ i, herm σ b' (b i) = 0 := fun i =>
    CFSG.ClassicalGroups.Unitary.herm_eq_zero_comm σ hs (hob i).2
  have oab : ∀ i, herm σ a' (b i) = 0 := fun i =>
    CFSG.ClassicalGroups.Unitary.herm_eq_zero_comm σ hs (hoa i).2
  refine ⟨?_, ?_, ?_⟩
  · intro i l
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl <;>
      rcases l.eq_castSucc_or_eq_last with ⟨l, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using h1 i l
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using (hoa i).1
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using oa l
    · simpa only [Fin.snoc_last] using ha'
  · intro i l
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl <;>
      rcases l.eq_castSucc_or_eq_last with ⟨l, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using h2 i l
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using (hob i).2
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using ob l
    · simpa only [Fin.snoc_last] using hb'
  · intro i l
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl <;>
      rcases l.eq_castSucc_or_eq_last with ⟨l, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using h3 i l
    · rw [Fin.snoc_castSucc, Fin.snoc_last, if_neg (Fin.castSucc_ne_last i)]
      exact (hob i).1
    · rw [Fin.snoc_last, Fin.snoc_castSucc, if_neg (Fin.castSucc_ne_last l).symm]
      exact oab l
    · rw [Fin.snoc_last, Fin.snoc_last, if_pos rfl]
      exact hab'

private theorem h65_snoc_orth {j : ℕ} {a b : Fin j → (Fin 6 → F)} {a' b' y : Fin 6 → F}
    (hy : OrthPairs σ (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F))
      (Fin.snoc b b' : Fin (j + 1) → (Fin 6 → F)) y) :
    OrthPairs σ a b y := by
  intro i
  simpa only [Fin.snoc_castSucc] using hy i.castSucc

private theorem h65_snoc_N {j : ℕ} {t : SUid σ 6} {a : Fin j → (Fin 6 → F)} {a' : Fin 6 → F}
    (hN : ∀ i, t • a i - a i = 0) (hN' : t • a' - a' = 0) :
    ∀ i : Fin (j + 1), t • (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F)) i -
      (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F)) i = 0 := by
  intro i
  rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc] using hN i
  · simpa only [Fin.snoc_last] using hN'

private theorem h65_induct (hσ : IsUnitaryInvolution σ) {t : SUid σ 6} (ht : t * t = 1) (j : ℕ) :
    j ≤ 3 → ∃ k ≤ j, ∃ a b : Fin j → (Fin 6 → F), IsHypPairs σ a b ∧ (∀ i, t • a i - a i = 0) ∧
      (∀ i, t • b i - b i = if i.val < k then a i else 0) ∧
      (k < j → ∀ y, OrthPairs σ a b y → t • y - y = 0) := by
  induction j with
  | zero =>
    intro _
    exact ⟨0, le_rfl, fun i => i.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0,
      fun i => i.elim0, fun h => absurd h (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    obtain ⟨k, hkj, a, b, hab, hN, hNb, hinv⟩ := ih (by omega)
    have hj2 : j ≤ 2 := by omega
    have hNb' : ∀ i, t • b i - b i = a i ∨ t • b i - b i = 0 := by
      intro i
      rw [hNb i]
      by_cases h : i.val < k
      · exact Or.inl (if_pos h)
      · exact Or.inr (if_neg h)
    by_cases hA : ∃ y, OrthPairs σ a b y ∧ t • y - y ≠ 0
    ·
      obtain ⟨y, hy, hNy⟩ := hA
      have hkj' : k = j := by
        by_contra hne
        exact hNy (hinv (by omega) y hy)
      obtain ⟨a', b', ha', hb', hab', hoa, hob, hNa', hNb''⟩ :=
        exists_typeI_pair hσ ht hab hN hNb' hy hNy
      refine ⟨j + 1, le_rfl, (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F)),
        (Fin.snoc b b' : Fin (j + 1) → (Fin 6 → F)),
        h65_snoc_hyp hσ.invol hab ha' hb' hab' hoa hob, h65_snoc_N hN hNa', ?_,
        fun h => absurd h (lt_irrefl _)⟩
      intro i
      rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
      · have hi := i.isLt
        simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        rw [hNb i, if_pos (show i.val < k by omega), if_pos (show i.val < j + 1 by omega)]
      · rw [Fin.snoc_last, Fin.snoc_last, Fin.val_last, hNb'', if_pos (show j < j + 1 by omega)]
    ·
      have hA' : ∀ y, OrthPairs σ a b y → t • y - y = 0 := fun y hy => by
        by_contra h
        exact hA ⟨y, hy, h⟩
      obtain ⟨a', b', ha', hb', hab', hoa, hob⟩ := exists_hyp_pair_perp hσ hj2 hab
      have hNa' : t • a' - a' = 0 := hA' a' hoa
      have hNb'' : t • b' - b' = 0 := hA' b' hob
      refine ⟨k, by omega, (Fin.snoc a a' : Fin (j + 1) → (Fin 6 → F)),
        (Fin.snoc b b' : Fin (j + 1) → (Fin 6 → F)),
        h65_snoc_hyp hσ.invol hab ha' hb' hab' hoa hob, h65_snoc_N hN hNa', ?_,
        fun _ y hy => hA' y (h65_snoc_orth hy)⟩
      intro i
      rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hNb i
      · rw [Fin.snoc_last, Fin.snoc_last, Fin.val_last, hNb'', if_neg (show ¬ (j < k) by omega)]

theorem exists_adapted_pairs (hσ : IsUnitaryInvolution σ) {t : SUid σ 6} (ht : t * t = 1) :
    ∃ (k : ℕ) (a b : Fin 3 → (Fin 6 → F)), k ≤ 3 ∧ IsHypPairs σ a b ∧
      (∀ i, t • a i - a i = 0) ∧
      (∀ i : Fin 3, t • b i - b i = if i.val < k then a i else 0) := by
  obtain ⟨k, hk, a, b, hab, hN, hNb, -⟩ := h65_induct hσ ht 3 le_rfl
  exact ⟨k, a, b, hk, hab, hN, hNb⟩

@[expose] def frameOf (a b : Fin 3 → (Fin 6 → F)) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun r c => if c.val % 2 = 0 then a ⟨c.val / 2, by omega⟩ r else b ⟨c.val / 2, by omega⟩ r

theorem conjTr_frameOf_mul (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → (Fin 6 → F)} (hab : IsHypPairs σ a b) :
    conjTr σ (frameOf a b) * frameOf a b = hypGram F :=
  conjTr_hypMat_mul (v := a) (w := b) hσ hab.1 hab.2.2 hab.2.1

private theorem h68_tInv1_val :
    (tInv1 F : Matrix (Fin 6) (Fin 6) F) = 1 + Matrix.single 0 1 1 := by
  rw [tInv1, transvGL_val, Matrix.transvection]

private theorem h68_tInv2_val :
    (tInv2 F : Matrix (Fin 6) (Fin 6) F) = 1 + (Matrix.single 0 1 1 + Matrix.single 2 3 1) := by
  rw [tInv2, Units.val_mul, h68_tInv1_val, transvGL_val, Matrix.transvection, add_mul, one_mul,
    mul_add, mul_one, Matrix.single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 2)),
    add_zero]
  abel

private theorem h68_tInv3_val :
    (tInv3 F : Matrix (Fin 6) (Fin 6) F) =
      1 + (Matrix.single 0 1 1 + Matrix.single 2 3 1 + Matrix.single 4 5 1) := by
  rw [tInv3, Units.val_mul, h68_tInv2_val, transvGL_val, Matrix.transvection, add_mul, one_mul,
    mul_add, mul_one, add_mul, Matrix.single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 4)),
    Matrix.single_mul_single_of_ne (h := (by decide : (3 : Fin 6) ≠ 4)), add_zero, add_zero]
  abel

theorem exists_frame_conj (hσ : IsUnitaryInvolution σ) {t : SUid σ 6} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ M : GL (Fin 6) F, conjTr σ (M : Matrix (Fin 6) (Fin 6) F) * (M : Matrix (Fin 6) (Fin 6) F) =
        hypGram F ∧
      (M⁻¹ * (t : GL (Fin 6) F) * M = tInv1 F ∨ M⁻¹ * (t : GL (Fin 6) F) * M = tInv2 F ∨
        M⁻¹ * (t : GL (Fin 6) F) * M = tInv3 F) := by
  obtain ⟨k, a, b, hk, hab, ha, hb⟩ := exists_adapted_pairs hσ ht
  have hG : conjTr σ (frameOf a b) * frameOf a b = hypGram F := conjTr_frameOf_mul hσ.invol hab
  have h2 : (hypGram F * conjTr σ (frameOf a b)) * frameOf a b = 1 := by
    rw [Matrix.mul_assoc, hG, hypGram_mul_self]
  have h1 : frameOf a b * (hypGram F * conjTr σ (frameOf a b)) = 1 :=
    mul_eq_one_comm.mpr h2
  obtain ⟨M, hMv, hMi⟩ : ∃ M : GL (Fin 6) F, (M : Matrix (Fin 6) (Fin 6) F) = frameOf a b ∧
      ((M⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = hypGram F * conjTr σ (frameOf a b) :=
    ⟨⟨frameOf a b, hypGram F * conjTr σ (frameOf a b), h1, h2⟩, rfl, rfl⟩
  refine ⟨M, by rw [hMv]; exact hG, ?_⟩
  have hconj : ∀ X : GL (Fin 6) F,
      ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameOf a b = frameOf a b * (X : Matrix (Fin 6) (Fin 6) F) →
        M⁻¹ * (t : GL (Fin 6) F) * M = X := by
    intro X hX
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hMi, hMv]
    calc (hypGram F * conjTr σ (frameOf a b)) * ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameOf a b
        = (hypGram F * conjTr σ (frameOf a b)) * (((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameOf a b) := by
          rw [Matrix.mul_assoc]
      _ = (hypGram F * conjTr σ (frameOf a b)) * (frameOf a b * (X : Matrix (Fin 6) (Fin 6) F)) := by
          rw [hX]
      _ = (hypGram F * (conjTr σ (frameOf a b) * frameOf a b)) * (X : Matrix (Fin 6) (Fin 6) F) := by
          simp only [Matrix.mul_assoc]
      _ = (X : Matrix (Fin 6) (Fin 6) F) := by
          rw [hG, hypGram_mul_self, Matrix.one_mul]
  have hA : ∀ i : Fin 3, ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ a i = a i := by
    intro i
    have h : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ a i - a i = 0 := ha i
    exact sub_eq_zero.mp h
  have hB : ∀ i : Fin 3,
      ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b i = b i + (if i.val < k then a i else 0) := by
    intro i
    have h : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b i - b i = (if i.val < k then a i else 0) := hb i
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  interval_cases k
  ·
    exfalso
    apply ht1
    have hB0 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 0 = b 0 := by simpa using hB 0
    have hB1 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 1 = b 1 := by simpa using hB 1
    have hB2 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 2 = b 2 := by simpa using hB 2
    have hX : M⁻¹ * (t : GL (Fin 6) F) * M = 1 := by
      apply hconj
      rw [Units.val_one, Matrix.mul_one]
      ext r c
      have e0 := congrFun hA0 r
      have e1 := congrFun hA1 r
      have e2 := congrFun hA2 r
      have f0 := congrFun hB0 r
      have f1 := congrFun hB1 r
      have f2 := congrFun hB2 r
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.add_apply] at e0 e1 e2 f0 f1 f2
      fin_cases c <;>
        simp [Matrix.mul_apply, Fin.sum_univ_six, frameOf, Matrix.single_apply, Matrix.one_apply,
          Matrix.add_apply] <;>
        (first | linear_combination e0 | linear_combination e1 | linear_combination e2 |
          linear_combination f0 | linear_combination f1 | linear_combination f2)
    have ht' : (t : GL (Fin 6) F) = 1 := by
      calc (t : GL (Fin 6) F) = M * (M⁻¹ * (t : GL (Fin 6) F) * M) * M⁻¹ := by group
        _ = 1 := by rw [hX]; group
    exact Subtype.ext ht'
  ·
    left
    apply hconj
    have hB0 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 0 = b 0 + a 0 := by simpa using hB 0
    have hB1 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 1 = b 1 := by simpa using hB 1
    have hB2 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 2 = b 2 := by simpa using hB 2
    rw [h68_tInv1_val]
    ext r c
    have e0 := congrFun hA0 r
    have e1 := congrFun hA1 r
    have e2 := congrFun hA2 r
    have f0 := congrFun hB0 r
    have f1 := congrFun hB1 r
    have f2 := congrFun hB2 r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.add_apply] at e0 e1 e2 f0 f1 f2
    fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, frameOf, Matrix.single_apply, Matrix.one_apply,
        Matrix.add_apply] <;>
      (first | linear_combination e0 | linear_combination e1 | linear_combination e2 |
        linear_combination f0 | linear_combination f1 | linear_combination f2)
  ·
    right
    left
    apply hconj
    have hB0 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 0 = b 0 + a 0 := by simpa using hB 0
    have hB1 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 1 = b 1 + a 1 := by simpa using hB 1
    have hB2 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 2 = b 2 := by simpa using hB 2
    rw [h68_tInv2_val]
    ext r c
    have e0 := congrFun hA0 r
    have e1 := congrFun hA1 r
    have e2 := congrFun hA2 r
    have f0 := congrFun hB0 r
    have f1 := congrFun hB1 r
    have f2 := congrFun hB2 r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.add_apply] at e0 e1 e2 f0 f1 f2
    fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, frameOf, Matrix.single_apply, Matrix.one_apply,
        Matrix.add_apply] <;>
      (first | linear_combination e0 | linear_combination e1 | linear_combination e2 |
        linear_combination f0 | linear_combination f1 | linear_combination f2)
  ·
    right
    right
    apply hconj
    have hB0 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 0 = b 0 + a 0 := by simpa using hB 0
    have hB1 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 1 = b 1 + a 1 := by simpa using hB 1
    have hB2 : ((t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ b 2 = b 2 + a 2 := by simpa using hB 2
    rw [h68_tInv3_val]
    ext r c
    have e0 := congrFun hA0 r
    have e1 := congrFun hA1 r
    have e2 := congrFun hA2 r
    have f0 := congrFun hB0 r
    have f1 := congrFun hB1 r
    have f2 := congrFun hB2 r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.add_apply] at e0 e1 e2 f0 f1 f2
    fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, frameOf, Matrix.single_apply, Matrix.one_apply,
        Matrix.add_apply] <;>
      (first | linear_combination e0 | linear_combination e1 | linear_combination e2 |
        linear_combination f0 | linear_combination f1 | linear_combination f2)

private theorem h69_det_norm {B : Matrix (Fin 6) (Fin 6) F} (hB : conjTr σ B * B = 1) :
    σ B.det * B.det = 1 := by
  have h1 : σ B.det = (conjTr σ B).det := by
    rw [conjTr, Matrix.det_transpose, RingEquiv.map_det]
    rfl
  rw [h1, ← Matrix.det_mul, hB, Matrix.det_one]

private theorem h69_unitary_mul {A S T H : Matrix (Fin 6) (Fin 6) F} (hA : conjTr σ A * A = H)
    (hS : conjTr σ S * S = H) (hST : S * T = 1) :
    conjTr σ (A * T) * (A * T) = 1 := by
  calc conjTr σ (A * T) * (A * T)
      = conjTr σ T * (conjTr σ A * A) * T := by
        rw [CFSG.LieType.Universal.Unitary.conjTr_mul]; simp only [Matrix.mul_assoc]
    _ = conjTr σ T * (conjTr σ S * S) * T := by rw [hA, hS]
    _ = conjTr σ (S * T) * (S * T) := by
        rw [CFSG.LieType.Universal.Unitary.conjTr_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hST, CFSG.LieType.Universal.Unitary.conjTr_one, Matrix.one_mul]

private theorem h69_diag_herm {lam : F} (hl : σ lam * lam = 1) :
    conjTr σ (Matrix.diagonal ![lam, lam, 1, 1, 1, 1]) * hypGram F *
      Matrix.diagonal ![lam, lam, 1, 1, 1, 1] = hypGram F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, hypGram, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal_apply] <;>
    linear_combination hl

private theorem h69_diag_ne {lam : F} (hl : lam ≠ 0) :
    ∀ i, (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) i ≠ 0 := by
  intro i
  fin_cases i <;> simp [hl]

private theorem h69_core (hsq : ∀ c : F, ∃ y : F, y * y = c) (Sf M t : GL (Fin 6) F)
    (hSH : conjTr σ (Sf : Matrix (Fin 6) (Fin 6) F) * (Sf : Matrix (Fin 6) (Fin 6) F) = hypGram F)
    (hMH : conjTr σ (M : Matrix (Fin 6) (Fin 6) F) * (M : Matrix (Fin 6) (Fin 6) F) = hypGram F)
    (hx : M⁻¹ * t * M = tInv1 F ∨ M⁻¹ * t * M = tInv2 F ∨ M⁻¹ * t * M = tInv3 F) :
    ∃ g : GL (Fin 6) F,
      (conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1 ∧
        (g : Matrix (Fin 6) (Fin 6) F).det = 1) ∧
      (g⁻¹ * t * g = Sf * tInv1 F * Sf⁻¹ ∨ g⁻¹ * t * g = Sf * tInv2 F * Sf⁻¹ ∨
        g⁻¹ * t * g = Sf * tInv3 F * Sf⁻¹) := by
  have hg0 : conjTr σ ((M : Matrix (Fin 6) (Fin 6) F) *
      ((Sf⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) *
      ((M : Matrix (Fin 6) (Fin 6) F) * ((Sf⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) = 1 :=
    h69_unitary_mul hMH hSH (Units.mul_inv Sf)
  obtain ⟨dd, hdd⟩ : ∃ dd : F, ((M : Matrix (Fin 6) (Fin 6) F) *
      ((Sf⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)).det = dd := ⟨_, rfl⟩
  have hnorm : σ dd * dd = 1 := by
    rw [← hdd]; exact h69_det_norm hg0
  have hdd0 : dd ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨lam, hlam⟩ := hsq dd⁻¹
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hlam
    exact (inv_ne_zero hdd0) hlam.symm
  have hσlam : σ lam * lam = 1 := by
    have hc : (σ lam * lam) * (σ lam * lam) = 1 := by
      have e1 : (σ lam * lam) * (σ lam * lam) = σ (lam * lam) * (lam * lam) := by
        rw [map_mul]; ring
      rw [e1, hlam, map_inv₀, ← mul_inv, hnorm, inv_one]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : (σ lam * lam - 1) * (σ lam * lam - 1) = 0 := by
      linear_combination hc - (σ lam * lam - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 6) F,
      D = CFSG.RankThree.GF2n.Smith81.A5Cube.diagGL ![lam, lam, 1, 1, 1, 1] (h69_diag_ne hlam0) :=
    ⟨_, rfl⟩
  have hDval : (D : Matrix (Fin 6) (Fin 6) F) = Matrix.diagonal ![lam, lam, 1, 1, 1, 1] := by
    rw [hDdef, CFSG.RankThree.GF2n.Smith81.A5Cube.diagGL_val]
  have hDdet : (D : Matrix (Fin 6) (Fin 6) F).det = lam * lam := by
    rw [hDdef, CFSG.RankThree.GF2n.Smith81.A5Cube.det_diagGL]
    simp [Fin.prod_univ_six]
  have hDH : conjTr σ (D : Matrix (Fin 6) (Fin 6) F) * hypGram F *
      (D : Matrix (Fin 6) (Fin 6) F) = hypGram F := by
    rw [hDval]; exact h69_diag_herm hσlam
  have hv0 : (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 0 = (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 1 := by
    simp
  have hv23 : (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 2 = (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 3 := by
    simp
  have hv45 : (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 4 = (![lam, lam, 1, 1, 1, 1] : Fin 6 → F) 5 := by
    simp
  have hc1 : Commute D (tInv1 F) := by
    rw [hDdef]
    exact CFSG.RankThree.GF2n.Smith81.A5Cube.diagGL_commute_transvGL _ (h69_diag_ne hlam0)
      0 1 (by decide) 1 hv0
  have hc2 : Commute D (transvGL F 2 3 (by decide) 1) := by
    rw [hDdef]
    exact CFSG.RankThree.GF2n.Smith81.A5Cube.diagGL_commute_transvGL _ (h69_diag_ne hlam0)
      2 3 (by decide) 1 hv23
  have hc3 : Commute D (transvGL F 4 5 (by decide) 1) := by
    rw [hDdef]
    exact CFSG.RankThree.GF2n.Smith81.A5Cube.diagGL_commute_transvGL _ (h69_diag_ne hlam0)
      4 5 (by decide) 1 hv45
  have hcI2 : Commute D (tInv2 F) := by
    show Commute D (tInv1 F * transvGL F 2 3 (by decide) 1)
    exact hc1.mul_right hc2
  have hcI3 : Commute D (tInv3 F) := by
    show Commute D (tInv2 F * transvGL F 4 5 (by decide) 1)
    exact hcI2.mul_right hc3
  have hinv : ∀ x : GL (Fin 6) F, Commute D x → D⁻¹ * x * D = x := by
    intro x hx'
    calc D⁻¹ * x * D = D⁻¹ * (x * D) := by rw [mul_assoc]
      _ = D⁻¹ * (D * x) := by rw [hx'.eq]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : GL (Fin 6) F, g₁ = M * D * Sf⁻¹ := ⟨_, rfl⟩
  have hMD : conjTr σ ((M : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F)) *
      ((M : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F)) = hypGram F := by
    rw [CFSG.LieType.Universal.Unitary.conjTr_mul]
    calc conjTr σ (D : Matrix (Fin 6) (Fin 6) F) * conjTr σ (M : Matrix (Fin 6) (Fin 6) F) *
          ((M : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F))
        = conjTr σ (D : Matrix (Fin 6) (Fin 6) F) *
            (conjTr σ (M : Matrix (Fin 6) (Fin 6) F) * (M : Matrix (Fin 6) (Fin 6) F)) *
              (D : Matrix (Fin 6) (Fin 6) F) := by simp only [Matrix.mul_assoc]
      _ = conjTr σ (D : Matrix (Fin 6) (Fin 6) F) * hypGram F * (D : Matrix (Fin 6) (Fin 6) F) := by
          rw [hMH]
      _ = hypGram F := hDH
  have hgu : conjTr σ (g₁ : Matrix (Fin 6) (Fin 6) F) * (g₁ : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [hg₁, Units.val_mul, Units.val_mul]
    exact h69_unitary_mul hMD hSH (Units.mul_inv Sf)
  have hdetg : (g₁ : Matrix (Fin 6) (Fin 6) F).det = dd * (D : Matrix (Fin 6) (Fin 6) F).det := by
    rw [← hdd, hg₁]
    simp only [Units.val_mul, Matrix.det_mul]
    ring
  have hdet : (g₁ : Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [hdetg, hDdet, hlam, mul_inv_cancel₀ hdd0]
  have hconj : g₁⁻¹ * t * g₁ = Sf * (D⁻¹ * (M⁻¹ * t * M) * D) * Sf⁻¹ := by
    rw [hg₁]; group
  refine ⟨g₁, ⟨hgu, hdet⟩, ?_⟩
  rcases hx with h | h | h
  · left
    rw [hconj, h, hinv _ hc1]
  · right; left
    rw [hconj, h, hinv _ hcI2]
  · right; right
    rw [hconj, h, hinv _ hcI3]

private theorem h69_exists_conj_tStd_sq (hsq : ∀ c : F, ∃ y : F, y * y = c) (hσ : IsUnitaryInvolution σ)
    {ω : F} (hω : ω + σ ω = 1) {t : SUid σ 6} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : SUid σ 6,
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv1 F * (frameGL σ ω hω)⁻¹ ∨
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv2 F * (frameGL σ ω hω)⁻¹ ∨
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv3 F * (frameGL σ ω hω)⁻¹ := by
  obtain ⟨M, hMH, hMx⟩ := exists_frame_conj hσ ht ht1
  obtain ⟨g, ⟨hu, hd⟩, heq⟩ := h69_core hsq (frameGL σ ω hω) M (t : GL (Fin 6) F)
    (conjTr_frameMat_mul hσ.invol hω) hMH hMx
  exact ⟨⟨g, mem_SUid.mpr ⟨hd, hu⟩⟩, heq⟩

theorem exists_conj_tStd [Finite F] (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {t : SUid σ 6} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : SUid σ 6,
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv1 F * (frameGL σ ω hω)⁻¹ ∨
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv2 F * (frameGL σ ω hω)⁻¹ ∨
      ((g⁻¹ * t * g : SUid σ 6) : GL (Fin 6) F) = frameGL σ ω hω * tInv3 F * (frameGL σ ω hω)⁻¹ := by
  refine h69_exists_conj_tStd_sq ?_ hσ hω ht ht1
  intro c
  have hinj : Function.Injective (fun y : F => y * y) := by
    intro y z hyz
    have hyz' : y * y = z * z := hyz
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h3 : (y - z) * (y - z) = 0 := by
      linear_combination hyz' + (z * z - y * z) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hinj) c
  exact ⟨y, hy⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube
