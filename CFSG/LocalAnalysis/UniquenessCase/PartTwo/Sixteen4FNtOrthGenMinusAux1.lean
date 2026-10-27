module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.BorelTits CFSG.Open

@[expose] def w183MinusExt (m : ℕ) (K : Type) [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K :=
  Sum.elim
    (fun i => Fin.lastCases (0 : K) (fun i' => w (Sum.inl i')) i)
    (Sum.elim
      (fun i => Fin.lastCases (0 : K) (fun i' => w (Sum.inr (Sum.inl i'))) i)
      (fun j => w (Sum.inr (Sum.inr j))))

abbrev w183MinusIdx (m : ℕ) := Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2)

@[expose] def w183MinusPolarCore (m : ℕ) (K : Type) [Field K] (b c : K)
    (u v : Fin m ⊕ (Fin m ⊕ Fin 2) → K) : K :=
  ∑ i : Fin m,
      (u (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inl i) * u (Sum.inr (Sum.inl i))) +
    (2 * u (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 0)) +
      b * (u (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        v (Sum.inr (Sum.inr 0)) * u (Sum.inr (Sum.inr 1))) +
      2 * c * u (Sum.inr (Sum.inr 1)) * v (Sum.inr (Sum.inr 1)))

@[expose] def w183MinusX (m : ℕ) (K : Type) [Field K] :
    Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K :=
  Pi.single (Sum.inl (Fin.last (m + 1))) 1

@[expose] def w183MinusY (m : ℕ) (K : Type) [Field K] :
    Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K :=
  Pi.single (Sum.inr (Sum.inl (Fin.last (m + 1)))) 1

@[simp] theorem w183MinusExt_inl {m : ℕ} {K : Type} [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) (i : Fin (m + 1)) :
    w183MinusExt m K w (Sum.inl (Fin.castSucc i)) = w (Sum.inl i) := by
  simp [w183MinusExt]

@[simp] theorem w183MinusExt_inr_inl {m : ℕ} {K : Type} [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) (i : Fin (m + 1)) :
    w183MinusExt m K w (Sum.inr (Sum.inl (Fin.castSucc i))) = w (Sum.inr (Sum.inl i)) := by
  simp [w183MinusExt]

@[simp] theorem w183MinusExt_inr_inr {m : ℕ} {K : Type} [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) (j : Fin 2) :
    w183MinusExt m K w (Sum.inr (Sum.inr j)) = w (Sum.inr (Sum.inr j)) := by
  simp [w183MinusExt]

@[simp] theorem w183MinusExt_last_inl {m : ℕ} {K : Type} [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    w183MinusExt m K w (Sum.inl (Fin.last (m + 1))) = 0 := by
  simp [w183MinusExt]

@[simp] theorem w183MinusExt_last_inr {m : ℕ} {K : Type} [Field K]
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    w183MinusExt m K w (Sum.inr (Sum.inl (Fin.last (m + 1)))) = 0 := by
  simp [w183MinusExt]

@[simp] theorem w183MinusExt_zero {m : ℕ} {K : Type} [Field K] :
    w183MinusExt m K (0 : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) = 0 := by
  ext i
  rcases i with i | i
  · induction i using Fin.lastCases <;> simp [w183MinusExt]
  · rcases i with i | i
    · induction i using Fin.lastCases <;> simp [w183MinusExt]
    · induction i using Fin.lastCases <;> simp [w183MinusExt]

theorem w183MinusExt_injective (m : ℕ) (K : Type) [Field K] :
    Function.Injective (w183MinusExt m K) := by
  intro v w h
  ext p
  rcases p with i | i
  · have := congr_fun h (Sum.inl (Fin.castSucc i))
    simpa using this
  · rcases i with i | i
    · have := congr_fun h (Sum.inr (Sum.inl (Fin.castSucc i)))
      simpa using this
    · have := congr_fun h (Sum.inr (Sum.inr i))
      simpa using this

theorem w183MinusExt_add {m : ℕ} {K : Type} [Field K]
    (v w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    w183MinusExt m K (v + w) = w183MinusExt m K v + w183MinusExt m K w := by
  ext i
  rcases i with i | i
  · induction i using Fin.lastCases <;> simp [w183MinusExt]
  · rcases i with i | i
    · induction i using Fin.lastCases <;> simp [w183MinusExt]
    · induction i using Fin.lastCases <;> simp [w183MinusExt]

theorem w183MinusForm {m : ℕ} {K : Type} [Field K] {b c : K}
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) (a b' : K) :
    StatedQuadMinus (m + 3) K b c
        (w183MinusExt m K w + a • w183MinusX m K + b' • w183MinusY m K) =
      StatedQuadMinus (m + 2) K b c w + a * b' := by
  change CFSG.MatrixModel.minusQuadCore ((m + 1) + 1) K b c
      (w183MinusExt m K w + a • w183MinusX m K + b' • w183MinusY m K) =
    CFSG.MatrixModel.minusQuadCore (m + 1) K b c w + a * b'
  simp only [CFSG.MatrixModel.minusQuadCore, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, w183MinusExt_inl, w183MinusExt_inr_inl, w183MinusExt_inr_inr,
    w183MinusExt_last_inl, w183MinusExt_last_inr]
  simp [w183MinusX, w183MinusY, Pi.single_apply, add_mul]
  ring

theorem w183QuadMinusPolarForm {m : ℕ} {K : Type} [Field K] {b c : K}
    (a d : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) (α β γ δ : K) :
    quadMinusPolar (m + 3) K b c
        (w183MinusExt m K a + α • w183MinusX m K + β • w183MinusY m K)
        (w183MinusExt m K d + γ • w183MinusX m K + δ • w183MinusY m K) =
      quadMinusPolar (m + 2) K b c a d + (α * δ + γ * β) := by
  change w183MinusPolarCore ((m + 1) + 1) K b c
      (w183MinusExt m K a + α • w183MinusX m K + β • w183MinusY m K)
      (w183MinusExt m K d + γ • w183MinusX m K + δ • w183MinusY m K) =
    w183MinusPolarCore (m + 1) K b c a d + (α * δ + γ * β)
  simp only [w183MinusPolarCore, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    w183MinusExt_inl, w183MinusExt_inr_inl, w183MinusExt_inr_inr, w183MinusExt_last_inl,
    w183MinusExt_last_inr]
  simp [w183MinusX, w183MinusY, Pi.single_apply]
  ring

theorem w183QuadMinusPolarExt {m : ℕ} {K : Type} [Field K] {b c : K}
    (v w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 3) K b c (w183MinusExt m K v) (w183MinusExt m K w) =
      quadMinusPolar (m + 2) K b c v w := by
  have h := w183QuadMinusPolarForm (K := K) (b := b) (c := c) v w 0 0 0 0
  simpa using h

theorem w183QuadMinusPolarXExt {m : ℕ} {K : Type} [Field K] {b c : K}
    (v w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 3) K b c (w183MinusExt m K v + w183MinusX m K) (w183MinusExt m K w) =
      quadMinusPolar (m + 2) K b c v w := by
  have h := w183QuadMinusPolarForm (K := K) (b := b) (c := c) v w 1 0 0 0
  simpa using h

theorem w183QuadMinusPolarXY {m : ℕ} {K : Type} [Field K] {b c : K}
    (w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 3) K b c (w183MinusExt m K w + w183MinusX m K)
      (w183MinusX m K + w183MinusY m K) = 1 := by
  have h := w183QuadMinusPolarForm (K := K) (b := b) (c := c) w 0 1 0 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add, w183MinusExt_zero, mul_one, mul_zero] at h
  have hq : quadMinusPolar (m + 2) K b c w 0 = 0 := by simp [quadMinusPolar]
  rw [h, hq]
  norm_num

theorem w183QuadMinusPolarYX {m : ℕ} {K : Type} [Field K] {b c : K}
    (v w : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 3) K b c (w183MinusExt m K v + w183MinusX m K)
      (w183MinusExt m K w + w183MinusY m K) = quadMinusPolar (m + 2) K b c v w + 1 := by
  have h := w183QuadMinusPolarForm (K := K) (b := b) (c := c) v w 1 0 0 1
  simpa using h

theorem w183MinusDecomp {m : ℕ} {K : Type} [Field K]
    (z : Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K) :
    z = w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) +
        z (Sum.inl (Fin.last (m + 1))) • w183MinusX m K +
        z (Sum.inr (Sum.inl (Fin.last (m + 1)))) • w183MinusY m K := by
  ext i
  rcases i with i | i
  · induction i using Fin.lastCases <;>
      simp [w183MinusExt, w183MinusX, w183MinusY, Pi.single_apply]
  · rcases i with i | i
    · induction i using Fin.lastCases <;>
        simp [w183MinusExt, w183MinusX, w183MinusY, Pi.single_apply]
    · induction i using Fin.lastCases <;>
        simp [w183MinusExt, w183MinusX, w183MinusY, Pi.single_apply]

theorem w183QaddM {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a d : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    StatedQuadMinus (m + 2) K b c (a + d) =
      StatedQuadMinus (m + 2) K b c a + StatedQuadMinus (m + 2) K b c d +
        quadMinusPolar (m + 2) K b c a d :=
  (quadMinusForm (m + 2) K b c hirr).Q_add a d

theorem w183PaddM {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a d e : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 2) K b c a (d + e) =
      quadMinusPolar (m + 2) K b c a d + quadMinusPolar (m + 2) K b c a e :=
  (quadMinusForm (m + 2) K b c hirr).polar.add_right a d e

theorem w183PselfM {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0)
    (a : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 2) K b c a a = 0 := by
  have h : quadMinusPolar (m + 2) K b c a a = 2 * StatedQuadMinus (m + 2) K b c a :=
    QuadForm.polar_self (quadMinusForm (m + 2) K b c hirr) a
  rw [h, h2, zero_mul]

theorem w183PsymmM {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a d : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) :
    quadMinusPolar (m + 2) K b c a d = quadMinusPolar (m + 2) K b c d a :=
  QuadForm.polar_symm (quadMinusForm (m + 2) K b c hirr) a d

theorem w183QzeroM {m : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedQuadMinus (m + 2) K b c (0 : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) = 0 :=
  (quadMinusForm (m + 2) K b c hirr).Q_zero

theorem w183ExistsNormOnePerpMinus {m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : ∀ c : K, c = 0 ∨ c = 1) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {w : w183MinusIdx m → K} (hw : w ≠ 0) :
    ∃ c' : w183MinusIdx m → K, StatedQuadMinus (m + 2) K b c c' = 1 ∧
      quadMinusPolar (m + 2) K b c w c' = 0 := by
  have h3 : 3 ≤ Module.finrank K (w183MinusIdx m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨c', hc'q, hc'p⟩ :=
    w183ExistsNormOnePerp hK (quadMinusForm (m + 2) K b c hirr) h3 hw
  exact ⟨c', hc'q, hc'p⟩

theorem w183MinusStep {K : Type} [Field K] [Finite K] (hK : ∀ c : K, c = 0 ∨ c = 1)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ)
    (hconn : ∀ u v : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K,
      StatedQuadMinus (m + 2) K b c u = 1 → StatedQuadMinus (m + 2) K b c v = 1 → u ≠ v →
      quadMinusPolar (m + 2) K b c u v = 1 ∨
        ∃ w, StatedQuadMinus (m + 2) K b c w = 1 ∧
          quadMinusPolar (m + 2) K b c u w = 1 ∧
          quadMinusPolar (m + 2) K b c v w = 1)
    {S : Set (Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K)}
    {u₀ : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K}
    (hu₀ : StatedQuadMinus (m + 2) K b c u₀ = 1)
    (hS : ∀ v ∈ S, StatedQuadMinus (m + 2) K b c v = 1)
    (hgen : w183Gen (StatedQuadMinus (m + 2) K b c) (quadMinusPolar (m + 2) K b c) S) :
    ∃ S' : Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K), S'.ncard ≤ S.ncard + 2 ∧
      (∀ v ∈ S', StatedQuadMinus (m + 3) K b c v = 1) ∧
      w183Gen (StatedQuadMinus (m + 3) K b c) (quadMinusPolar (m + 3) K b c) S' := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases hK 2 with h | h
    · exact h
    · exfalso
      have h1 : (1 : K) = 0 := by
        have hh : (2 : K) = 1 + 1 := by norm_num
        rw [hh] at h
        have h' : (1 : K) + 1 = 1 + 0 := by rw [h, add_zero]
        exact add_left_cancel h'
      exact one_ne_zero h1
  have h11 : (1 : K) + 1 = 0 := by
    rw [← show (2 : K) = 1 + 1 by norm_num]; exact h2
  have hvvr : ∀ v : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  have hvvR : ∀ v : Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  refine ⟨w183MinusExt m K '' S ∪
    ({w183MinusExt m K u₀ + w183MinusX m K, w183MinusX m K + w183MinusY m K} :
      Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K)), ?_, ?_, ?_⟩
  · have hpair : Set.ncard ({w183MinusExt m K u₀ + w183MinusX m K,
        w183MinusX m K + w183MinusY m K} : Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K)) ≤ 2 := by
      calc Set.ncard ({w183MinusExt m K u₀ + w183MinusX m K,
            w183MinusX m K + w183MinusY m K} : Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K))
          = Set.ncard (insert (w183MinusExt m K u₀ + w183MinusX m K)
              ({w183MinusX m K + w183MinusY m K} :
                Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K))) := rfl
        _ ≤ Set.ncard ({w183MinusX m K + w183MinusY m K} :
              Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K)) + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    calc Set.ncard (w183MinusExt m K '' S ∪
            {w183MinusExt m K u₀ + w183MinusX m K, w183MinusX m K + w183MinusY m K})
        ≤ Set.ncard (w183MinusExt m K '' S) + Set.ncard
            ({w183MinusExt m K u₀ + w183MinusX m K, w183MinusX m K + w183MinusY m K} :
              Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K)) := Set.ncard_union_le _ _
      _ = Set.ncard S + Set.ncard ({w183MinusExt m K u₀ + w183MinusX m K,
            w183MinusX m K + w183MinusY m K} : Set (Fin (m + 2) ⊕ (Fin (m + 2) ⊕ Fin 2) → K)) := by
            rw [Set.ncard_image_of_injective _ (w183MinusExt_injective m K)]
      _ ≤ Set.ncard S + 2 := by omega
  · intro v hv
    rcases hv with ⟨w, hw, rfl⟩ | hv
    · have h := w183MinusForm (b := b) (c := c) w 0 0
      simp only [zero_smul, add_zero, mul_zero] at h
      rw [h, hS w hw]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · have h := w183MinusForm (b := b) (c := c) u₀ 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hu₀]
      · have h := w183MinusForm (m := m) (K := K) (b := b) (c := c)
          (0 : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) 1 1
        simp only [w183MinusExt_zero, zero_add, one_smul, mul_one] at h
        simpa [w183QzeroM hirr] using h
  · intro T hT hcl
    have hsub : S ⊆ {w | w183MinusExt m K w ∈ T} :=
      fun w hw => hT (Or.inl ⟨w, hw, rfl⟩)
    have hcl' : ∀ v ∈ {w | w183MinusExt m K w ∈ T},
        ∀ w ∈ {w | w183MinusExt m K w ∈ T},
        StatedQuadMinus (m + 2) K b c v = 1 → StatedQuadMinus (m + 2) K b c w = 1 →
        quadMinusPolar (m + 2) K b c v w = 1 → v + w ∈ {w | w183MinusExt m K w ∈ T} := by
      intro v hv w hw qv qw hp
      change w183MinusExt m K (v + w) ∈ T
      rw [w183MinusExt_add]
      refine hcl (w183MinusExt m K v) hv (w183MinusExt m K w) hw ?_ ?_ ?_
      · have h := w183MinusForm (b := b) (c := c) v 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, qv]
      · have h := w183MinusForm (b := b) (c := c) w 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, qw]
      · have h := w183QuadMinusPolarExt (b := b) (c := c) v w
        rw [h, hp]
    have hNW : ∀ (w : w183MinusIdx m → K),
        StatedQuadMinus (m + 2) K b c w = 1 → w183MinusExt m K w ∈ T :=
      hgen {w | w183MinusExt m K w ∈ T} hsub hcl'
    have hfin3 : 3 ≤ Module.finrank K (Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum]
      simp only [Fintype.card_fin]
      omega
    let A : Set (w183MinusIdx m → K) := {w |
      StatedQuadMinus (m + 2) K b c w = 1 ∧ w183MinusExt m K w + w183MinusX m K ∈ T}
    have hA_mem : u₀ ∈ A := ⟨hu₀, hT (Or.inr (by simp))⟩
    have hA_closed : ∀ w ∈ A, ∀ (w' : w183MinusIdx m → K),
        StatedQuadMinus (m + 2) K b c w' = 1 →
        quadMinusPolar (m + 2) K b c w w' = 1 → w' ∈ A := by
      intro w hw w' hw' hp
      obtain ⟨hqw, hxw⟩ := hw
      refine ⟨hw', ?_⟩
      have ht : StatedQuadMinus (m + 2) K b c (w + w') = 1 := by
        rw [w183QaddM hirr w w', hqw, hw', hp, h11, zero_add]
      have htT : w183MinusExt m K (w + w') ∈ T := hNW (w + w') ht
      have hz : StatedQuadMinus (m + 3) K b c (w183MinusExt m K w + w183MinusX m K) = 1 := by
        have h := w183MinusForm (b := b) (c := c) w 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hqw]
      have hzt : StatedQuadMinus (m + 3) K b c (w183MinusExt m K (w + w')) = 1 := by
        have h := w183MinusForm (b := b) (c := c) (w + w') 0 0
        simp only [zero_smul, add_zero, mul_zero] at h
        rw [h, ht]
      have hpv : quadMinusPolar (m + 3) K b c (w183MinusExt m K w + w183MinusX m K)
          (w183MinusExt m K (w + w')) = 1 := by
        rw [w183QuadMinusPolarXExt]
        rw [w183PaddM hirr w w w', w183PselfM hirr h2 w, zero_add, hp]
      have hres := hcl (w183MinusExt m K w + w183MinusX m K) hxw
        (w183MinusExt m K (w + w')) htT hz hzt hpv
      have hsum : (w183MinusExt m K w + w183MinusX m K) + w183MinusExt m K (w + w') =
          w183MinusExt m K w' + w183MinusX m K := by
        rw [show w183MinusExt m K w + w183MinusX m K + w183MinusExt m K (w + w') =
            w183MinusExt m K (w + (w + w')) + w183MinusX m K from by
          rw [show w183MinusExt m K (w + (w + w')) =
              w183MinusExt m K w + w183MinusExt m K (w + w') from w183MinusExt_add w (w + w')]
          abel]
        rw [show w + (w + w') = w' from by rw [← add_assoc, hvvr w, zero_add]]
      rwa [hsum] at hres
    have hN : ∀ (w : w183MinusIdx m → K), StatedQuadMinus (m + 2) K b c w = 1 → w ≠ u₀ →
        quadMinusPolar (m + 2) K b c u₀ w = 1 ∨ ∃ b', StatedQuadMinus (m + 2) K b c b' = 1 ∧
          quadMinusPolar (m + 2) K b c u₀ b' = 1 ∧
          quadMinusPolar (m + 2) K b c b' w = 1 := by
      intro w hw hwne
      rcases hconn u₀ w (hu₀) hw (Ne.symm hwne) with h | ⟨b', hb', hb1, hb2⟩
      · exact Or.inl h
      · exact Or.inr ⟨b', hb', hb1, (w183PsymmM hirr b' w) ▸ hb2⟩
    have hAall : ∀ (w : w183MinusIdx m → K), StatedQuadMinus (m + 2) K b c w = 1 → w ∈ A :=
      w183EqOfClosedAdj hA_mem hA_closed hN
    have hxT : ∀ (w : w183MinusIdx m → K), StatedQuadMinus (m + 2) K b c w = 1 →
        w183MinusX m K + w183MinusExt m K w ∈ T := by
      intro w hw
      have h := (hAall w hw).2
      simpa [add_comm] using h
    have hxy : w183MinusX m K + w183MinusY m K ∈ T := hT (Or.inr (by simp))
    have hyT : ∀ (w : w183MinusIdx m → K), StatedQuadMinus (m + 2) K b c w = 1 →
        w183MinusY m K + w183MinusExt m K w ∈ T := by
      intro w hw
      have hx := hxT w hw
      have h1 : StatedQuadMinus (m + 3) K b c (w183MinusX m K + w183MinusExt m K w) = 1 := by
        rw [show w183MinusX m K + w183MinusExt m K w = w183MinusExt m K w + w183MinusX m K
          from add_comm _ _]
        have h := w183MinusForm (b := b) (c := c) w 1 0
        simp only [one_smul, zero_smul, add_zero, mul_zero] at h
        rw [h, hw]
      have h2' : StatedQuadMinus (m + 3) K b c (w183MinusX m K + w183MinusY m K) = 1 := by
        have h := w183MinusForm (m := m) (K := K) (b := b) (c := c)
          (0 : Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin 2) → K) 1 1
        simp only [w183MinusExt_zero, zero_add, one_smul, mul_one] at h
        simpa [w183QzeroM hirr] using h
      have hp : quadMinusPolar (m + 3) K b c (w183MinusX m K + w183MinusExt m K w)
          (w183MinusX m K + w183MinusY m K) = 1 := by
        rw [show w183MinusX m K + w183MinusExt m K w = w183MinusExt m K w + w183MinusX m K
          from add_comm _ _]
        exact w183QuadMinusPolarXY w
      have hres := hcl (w183MinusX m K + w183MinusExt m K w) hx
        (w183MinusX m K + w183MinusY m K) hxy h1 h2' hp
      have hsum : (w183MinusX m K + w183MinusExt m K w) + (w183MinusX m K + w183MinusY m K) =
          w183MinusY m K + w183MinusExt m K w := by
        calc (w183MinusX m K + w183MinusExt m K w) + (w183MinusX m K + w183MinusY m K)
            = (w183MinusX m K + w183MinusX m K) + (w183MinusExt m K w + w183MinusY m K) := by abel
          _ = 0 + (w183MinusExt m K w + w183MinusY m K) := by rw [hvvR (w183MinusX m K)]
          _ = w183MinusY m K + w183MinusExt m K w := by rw [zero_add]; exact add_comm _ _
      rwa [hsum] at hres
    have hsingT : ∀ (w : w183MinusIdx m → K), StatedQuadMinus (m + 2) K b c w = 0 →
        w183MinusX m K + w183MinusY m K + w183MinusExt m K w ∈ T := by
      intro w hw0
      by_cases hw : w = 0
      · subst hw; rw [w183MinusExt_zero, add_zero]; exact hxy
      · obtain ⟨w₁, hw₁q, hw₁p⟩ := w183ExistsNormOnePerpMinus hK hirr hw
        have hw₁ : StatedQuadMinus (m + 2) K b c w₁ = 1 := hw₁q
        have hw₁p' : quadMinusPolar (m + 2) K b c w w₁ = 0 := hw₁p
        have hw₂ : StatedQuadMinus (m + 2) K b c (w + w₁) = 1 := by
          rw [w183QaddM hirr w w₁, hw0, hw₁, hw₁p', zero_add, add_zero]
        have hp12 : quadMinusPolar (m + 2) K b c w₁ (w + w₁) = 0 := by
          rw [w183PaddM hirr w₁ w w₁]
          rw [w183PsymmM hirr w₁ w, hw₁p', w183PselfM hirr h2 w₁, add_zero]
        have h1 : StatedQuadMinus (m + 3) K b c (w183MinusX m K + w183MinusExt m K w₁) = 1 := by
          rw [show w183MinusX m K + w183MinusExt m K w₁ = w183MinusExt m K w₁ + w183MinusX m K
            from add_comm _ _]
          have h := w183MinusForm (b := b) (c := c) w₁ 1 0
          simp only [one_smul, zero_smul, add_zero, mul_zero] at h
          rw [h, hw₁]
        have h2' : StatedQuadMinus (m + 3) K b c
            (w183MinusY m K + w183MinusExt m K (w + w₁)) = 1 := by
          rw [show w183MinusY m K + w183MinusExt m K (w + w₁) =
            w183MinusExt m K (w + w₁) + w183MinusY m K from add_comm _ _]
          have h := w183MinusForm (b := b) (c := c) (w + w₁) 0 1
          simp only [one_smul, zero_smul, add_zero, zero_mul, mul_zero] at h
          rw [h, hw₂]
        have hp : quadMinusPolar (m + 3) K b c (w183MinusX m K + w183MinusExt m K w₁)
            (w183MinusY m K + w183MinusExt m K (w + w₁)) = 1 := by
          rw [show w183MinusX m K + w183MinusExt m K w₁ = w183MinusExt m K w₁ + w183MinusX m K
            from add_comm _ _]
          rw [show w183MinusY m K + w183MinusExt m K (w + w₁) =
            w183MinusExt m K (w + w₁) + w183MinusY m K from add_comm _ _]
          rw [w183QuadMinusPolarYX, hp12, zero_add]
        have hres := hcl (w183MinusX m K + w183MinusExt m K w₁) (hxT w₁ hw₁)
          (w183MinusY m K + w183MinusExt m K (w + w₁)) (hyT (w + w₁) hw₂)
          h1 h2' hp
        have hsum : (w183MinusX m K + w183MinusExt m K w₁) +
            (w183MinusY m K + w183MinusExt m K (w + w₁)) =
            w183MinusX m K + w183MinusY m K + w183MinusExt m K w := by
          rw [show (w183MinusX m K + w183MinusExt m K w₁) +
              (w183MinusY m K + w183MinusExt m K (w + w₁)) =
              w183MinusX m K + w183MinusY m K + w183MinusExt m K (w₁ + (w + w₁)) from by
            rw [show w183MinusExt m K (w₁ + (w + w₁)) =
                w183MinusExt m K w₁ + w183MinusExt m K (w + w₁) from w183MinusExt_add w₁ (w + w₁)]
            abel]
          rw [show w₁ + (w + w₁) = w from by
            rw [add_comm w₁ (w + w₁), add_assoc, hvvr w₁, add_zero]]
        rwa [hsum] at hres
    intro z hz
    have hzdecomp : z =
        w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) +
        z (Sum.inl (Fin.last (m + 1))) • w183MinusX m K +
        z (Sum.inr (Sum.inl (Fin.last (m + 1)))) • w183MinusY m K := w183MinusDecomp z
    have hQz : StatedQuadMinus (m + 2) K b c
        (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) +
        z (Sum.inl (Fin.last (m + 1))) * z (Sum.inr (Sum.inl (Fin.last (m + 1)))) = 1 := by
      have h := w183MinusForm (b := b) (c := c)
        (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p))
        (z (Sum.inl (Fin.last (m + 1)))) (z (Sum.inr (Sum.inl (Fin.last (m + 1)))))
      rw [← hzdecomp] at h
      exact h.symm.trans hz
    rw [hzdecomp]
    rcases hK (z (Sum.inl (Fin.last (m + 1)))) with hα | hα <;>
      rcases hK (z (Sum.inr (Sum.inl (Fin.last (m + 1))))) with hβ | hβ
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, mul_zero] at hQz ⊢
      exact hNW _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, one_smul, mul_zero] at hQz ⊢
      rw [show w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) +
          w183MinusY m K = w183MinusY m K +
          w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p))
          from add_comm _ _]
      exact hyT _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [zero_smul, add_zero, one_smul, mul_zero] at hQz ⊢
      rw [show w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) +
          w183MinusX m K = w183MinusX m K +
          w183MinusExt m K (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p))
          from add_comm _ _]
      exact hxT _ (by simpa using hQz)
    · rw [hα, hβ] at hQz
      rw [hα, hβ]
      simp only [one_smul, mul_one] at hQz ⊢
      have hw : StatedQuadMinus (m + 2) K b c
          (fun p => z (Sum.map Fin.castSucc (Sum.map Fin.castSucc id) p)) = 0 := by
        exact add_right_cancel (by rw [hQz, zero_add])
      simpa [add_comm, add_left_comm, add_assoc] using hsingT _ hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
