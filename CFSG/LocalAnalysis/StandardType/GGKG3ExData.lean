module

public import CFSG.LocalAnalysis.StandardType.GGKG3K3dCheck

public section

namespace CFSG.StandardType.GGKG3

open CFSG.StandardType.GGKG3.K3dCheck

@[expose] def k3Pair (y : Fin 6 → ZMod 7) (v : Fin 6 → ℤ) : ZMod 7 :=
  ∑ i, y i * ((v i : ℤ) : ZMod 7)

@[expose] def k3ActT (A : Matrix (Fin 6) (Fin 6) ℤ) (y : Fin 6 → ZMod 7) : Fin 6 → ZMod 7 :=
  fun i => ∑ k, y k * ((A k i : ℤ) : ZMod 7)

@[expose] def k3Ex : Set (Fin 6 → ZMod 7) :=
  {y | k3ActT (Matrix.of kMw) y = (2 : ZMod 7) • y}

@[expose] def k3M7 : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  Matrix.of fun i j => ((kMw i j : ℤ) : ZMod 7)

@[expose] def k3Q : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (3 : ZMod 7) • k3M7.transpose + (2 : ZMod 7) • (1 : Matrix (Fin 6) (Fin 6) (ZMod 7))

@[expose] def k3Par (a : Fin 3 → ZMod 7) : Fin 6 → ZMod 7 :=
  ![a 0, a 1, a 2, 6 * a 1 + 4 * a 2, 5 * a 1 + 3 * a 2, 2 * a 0 + 3 * a 1 + 2 * a 2]

theorem k3ActT_smul (A : Matrix (Fin 6) (Fin 6) ℤ) (a : ZMod 7) (y : Fin 6 → ZMod 7) :
    k3ActT A (a • y) = a • k3ActT A y := by
  funext i
  simp only [k3ActT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem k3ActT_sub (A : Matrix (Fin 6) (Fin 6) ℤ) (y z : Fin 6 → ZMod 7) :
    k3ActT A (y - z) = k3ActT A y - k3ActT A z := by
  funext i
  simp only [k3ActT, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem k3Ex_sub {y z : Fin 6 → ZMod 7} (hy : y ∈ k3Ex) (hz : z ∈ k3Ex) : y - z ∈ k3Ex := by
  show k3ActT (Matrix.of kMw) (y - z) = (2 : ZMod 7) • (y - z)
  rw [k3ActT_sub, show k3ActT (Matrix.of kMw) y = (2 : ZMod 7) • y from hy,
    show k3ActT (Matrix.of kMw) z = (2 : ZMod 7) • z from hz, smul_sub]

theorem k3Ex_smul (a : ZMod 7) {y : Fin 6 → ZMod 7} (hy : y ∈ k3Ex) : a • y ∈ k3Ex := by
  show k3ActT (Matrix.of kMw) (a • y) = (2 : ZMod 7) • (a • y)
  rw [k3ActT_smul, show k3ActT (Matrix.of kMw) y = (2 : ZMod 7) • y from hy, smul_comm]

theorem k3Par_mem (a : Fin 3 → ZMod 7) : k3Par a ∈ k3Ex := by
  have key : ∀ a : Fin 3 → ZMod 7, k3ActT (Matrix.of kMw) (k3Par a) = (2 : ZMod 7) • k3Par a := by
    decide +kernel
  exact key a

theorem k3Ex_eq_zero_of_coords {z : Fin 6 → ZMod 7} (hz : z ∈ k3Ex) (h0 : z 0 = 0) (h1 : z 1 = 0)
    (h2 : z 2 = 0) : z = 0 := by
  have key : ∀ u v w : ZMod 7,
      k3ActT (Matrix.of kMw) ![0, 0, 0, u, v, w] = (2 : ZMod 7) • ![0, 0, 0, u, v, w] →
        u = 0 ∧ v = 0 ∧ w = 0 := by
    decide +kernel
  have hz' : z = ![0, 0, 0, z 3, z 4, z 5] := by
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  have := key (z 3) (z 4) (z 5) (by rw [← hz']; exact hz)
  rw [hz']
  funext i
  fin_cases i <;> simp [this.1, this.2.1, this.2.2]

theorem k3Ex_eq_range : k3Ex = Set.range k3Par := by
  ext y
  constructor
  · intro hy
    refine ⟨![y 0, y 1, y 2], ?_⟩
    have hz := k3Ex_sub hy (k3Par_mem ![y 0, y 1, y 2])
    have h := k3Ex_eq_zero_of_coords hz (by simp [k3Par]) (by simp [k3Par]) (by simp [k3Par])
    exact (sub_eq_zero.mp h).symm
  · rintro ⟨a, rfl⟩
    exact k3Par_mem a

theorem k3Par_injective : Function.Injective k3Par := by
  intro a b h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

theorem k3Ex_ncard : k3Ex.ncard = 343 := by
  rw [k3Ex_eq_range, ← Set.image_univ, Set.ncard_image_of_injective _ k3Par_injective,
    Set.ncard_univ]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem mem_k3Ex_iff {y : Fin 6 → ZMod 7} :
    y ∈ k3Ex ↔ ∀ j, ∑ i, y i * ((kMw i j : ℤ) : ZMod 7) = 2 * y j := by
  show k3ActT (Matrix.of kMw) y = (2 : ZMod 7) • y ↔ _
  constructor
  · intro h j
    have := congrFun h j
    simpa [k3ActT] using this
  · intro h
    funext j
    simpa [k3ActT] using h j

private def kg3_img (γ : Fin 6 → ℤ) : ZMod 7 × ZMod 7 × ZMod 7 :=
  (k3Pair (k3Par ![1, 0, 0]) γ, k3Pair (k3Par ![0, 1, 0]) γ, k3Pair (k3Par ![0, 0, 1]) γ)

private theorem kg3_img_inj :
    (k3Roots.all fun γ => k3Roots.all fun δ => (γ == δ) || decide (kg3_img γ ≠ kg3_img δ)) =
      true := by
  decide +kernel

private theorem kg3_img_ne_zero :
    (k3Roots.all fun γ => decide (kg3_img γ ≠ (0, 0, 0))) = true := by
  decide +kernel

theorem k3_Ex_sep {γ δ : Fin 6 → ℤ} (hγ : γ ∈ k3Roots) (hδ : δ ∈ k3Roots)
    (h : ∀ y ∈ k3Ex, k3Pair y γ = k3Pair y δ) : γ = δ := by
  have h0 := h _ (k3Par_mem ![1, 0, 0])
  have h1 := h _ (k3Par_mem ![0, 1, 0])
  have h2 := h _ (k3Par_mem ![0, 0, 1])
  have himg : kg3_img γ = kg3_img δ := by
    simp only [kg3_img, h0, h1, h2]
  have key := kg3_img_inj
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at key
  rcases key γ hγ δ hδ with h' | h'
  · exact h'
  · exact absurd himg h'

theorem k3_Ex_ne {γ : Fin 6 → ℤ} (hγ : γ ∈ k3Roots) (h : ∀ y ∈ k3Ex, k3Pair y γ = 0) : False := by
  have h0 := h _ (k3Par_mem ![1, 0, 0])
  have h1 := h _ (k3Par_mem ![0, 1, 0])
  have h2 := h _ (k3Par_mem ![0, 0, 1])
  have himg : kg3_img γ = (0, 0, 0) := by
    simp only [kg3_img, h0, h1, h2]
  have key := kg3_img_ne_zero
  simp only [List.all_eq_true, decide_eq_true_eq] at key
  exact key γ hγ himg

end CFSG.StandardType.GGKG3
