module

public import CFSG.Quasithin.Background.FFC3Offender
public import CFSG.Quasithin.Background.B5FinWedge
public import CFSG.Quasithin.Background.JonesParshallWedge
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin

@[expose] def rowW {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (k : Fin d) : Fin d → ZMod 2 :=
  fun l => M k l - if k = l then 1 else 0

theorem rowW_dot {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) {v : Fin d → ZMod 2} (hv : M *ᵥ v = v)
    (k : Fin d) : rowW M k ⬝ᵥ v = 0 := by
  have h := congrFun hv k
  have e1 : ∑ l, rowW M k l * v l = ∑ l, M k l * v l - ∑ l, (if k = l then (1 : ZMod 2) else 0) * v l := by
    simp only [rowW, sub_mul]
    exact Finset.sum_sub_distrib _ _
  have e2 : ∑ l, (if k = l then (1 : ZMod 2) else 0) * v l = v k := by simp
  simp only [Matrix.mulVec, dotProduct] at h ⊢
  rw [e1, e2, h, sub_self]

theorem single_block {a i j : ℕ} (h : i < a → j < a) : ∀ d ∈ ({a} : Set ℕ), i < d → j < d := by
  intro d hd
  rw [Set.mem_singleton_iff] at hd
  subst hd
  exact h

theorem card_mul_fixN_le {n : ℕ} (hn : 1 ≤ n) (A : Subgroup (SLt n)) (hU : A ≤ Ut n)
    (hR : ∀ y ∈ A, ∀ i j : Fin n, i < j → (∀ d ∈ ({1} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0) :
    Nat.card A * Nat.card {v : Vt n | ∀ y ∈ A, mat y *ᵥ v = v} ≤ 2 ^ n := by
  classical
  let z : Fin n := ⟨0, hn⟩
  have hrow : ∀ y ∈ A, ∀ i j : Fin n, i ≠ z → i < j → mat y i j = 0 := by
    intro y hy i j hiz hij
    refine hR y hy i j hij fun d hd hid => ?_
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exfalso
    apply hiz
    apply Fin.ext
    show (i : ℕ) = 0
    omega
  have hinj : Function.Injective (fun y : ↥A => rowW (mat y.1) z) := by
    intro y y' h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    by_cases hiz : i = z
    · rw [hiz]
      by_cases hjz : j = z
      · rw [hjz]
        exact ((hU y.2).2 z).trans ((hU y'.2).2 z).symm
      · simpa [rowW, Ne.symm hjz] using congrFun h j
    · rcases lt_trichotomy i j with hij | hij | hij
      · exact (hrow y.1 y.2 i j hiz hij).trans (hrow y'.1 y'.2 i j hiz hij).symm
      · rw [hij]
        exact ((hU y.2).2 j).trans ((hU y'.2).2 j).symm
      · exact ((hU y.2).1 i j hij).trans ((hU y'.2).1 i j hij).symm
  exact FFC.card_mul_card_le_two_pow (S := ↥A) (fun y => rowW (mat y.1) z) hinj
    {v | ∀ y ∈ A, mat y *ᵥ v = v} fun y v hv => rowW_dot (mat y.1) (hv y.1 y.2) z

@[expose] def shape4 (t : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, t 0, t 1; 0, 1, t 2, t 3; 0, 0, 1, 0; 0, 0, 0, 1]

theorem shape4_facts :
    (∀ t t' : Fin 4 → ZMod 2, rowW (B5FinWedge.wedgeMat4 (shape4 t)) 0 =
        rowW (B5FinWedge.wedgeMat4 (shape4 t')) 0 → t = t') ∧
    (∀ t : Fin 4 → ZMod 2, t ≠ 0 → ∃ k : Fin 6, rowW (B5FinWedge.wedgeMat4 (shape4 t)) k ≠ 0 ∧
      ∀ t' : Fin 4 → ZMod 2, rowW (B5FinWedge.wedgeMat4 (shape4 t)) k ≠
        rowW (B5FinWedge.wedgeMat4 (shape4 t')) 0) := by
  decide +kernel

theorem eq_shape4 {y : SLt 4} (hU : y ∈ Ut 4)
    (hR : ∀ i j : Fin 4, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) :
    mat y = shape4 ![mat y 0 2, mat y 0 3, mat y 1 2, mat y 1 3] := by
  have h01 : mat y 0 1 = 0 := hR 0 1 (by decide) (single_block (by decide))
  have h23 : mat y 2 3 = 0 := hR 2 3 (by decide) (single_block (by decide))
  have h10 : mat y 1 0 = 0 := hU.1 1 0 (by decide)
  have h20 : mat y 2 0 = 0 := hU.1 2 0 (by decide)
  have h30 : mat y 3 0 = 0 := hU.1 3 0 (by decide)
  have h21 : mat y 2 1 = 0 := hU.1 2 1 (by decide)
  have h31 : mat y 3 1 = 0 := hU.1 3 1 (by decide)
  have h32 : mat y 3 2 = 0 := hU.1 3 2 (by decide)
  have h00 : mat y 0 0 = 1 := hU.2 0
  have h11 : mat y 1 1 = 1 := hU.2 1
  have h22 : mat y 2 2 = 1 := hU.2 2
  have h33 : mat y 3 3 = 1 := hU.2 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shape4, h01, h23, h10, h20, h30, h21, h31, h32, h00, h11, h22, h33]

theorem card_mul_fix_lt_of_shape {d m : ℕ} (hd0 : 0 < d) (A : Subgroup (SLt m)) (hA : A ≠ ⊥) {r : ℕ}
    (sh : (Fin r → ZMod 2) → Matrix (Fin m) (Fin m) (ZMod 2))
    (W : Matrix (Fin m) (Fin m) (ZMod 2) → Matrix (Fin d) (Fin d) (ZMod 2))
    (τ : ↥A → (Fin r → ZMod 2)) (hshape : ∀ y : ↥A, mat y.1 = sh (τ y))
    (hsh0 : sh 0 = 1)
    (hf1 : ∀ t t' : Fin r → ZMod 2, rowW (W (sh t)) ⟨0, hd0⟩ = rowW (W (sh t')) ⟨0, hd0⟩ → t = t')
    (hf2 : ∀ t : Fin r → ZMod 2, t ≠ 0 → ∃ k : Fin d, rowW (W (sh t)) k ≠ 0 ∧
      ∀ t' : Fin r → ZMod 2, rowW (W (sh t)) k ≠ rowW (W (sh t')) ⟨0, hd0⟩) :
    Nat.card A * Nat.card {v : Fin d → ZMod 2 | ∀ y ∈ A, W (mat y) *ᵥ v = v} < 2 ^ d := by
  classical
  have hτinj : ∀ y y' : ↥A, τ y = τ y' → y = y' := by
    intro y y' h
    apply Subtype.ext
    apply Subtype.ext
    have := hshape y
    rw [h, ← hshape y'] at this
    exact this
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  have hτ0 : τ a₀ ≠ 0 := by
    intro h0
    apply ha₀
    apply Subtype.ext
    apply Subtype.ext
    have := hshape a₀
    rw [h0, hsh0] at this
    rw [show (a₀.1 : Matrix (Fin m) (Fin m) (ZMod 2)) = mat a₀.1 from rfl, this]
    rfl
  obtain ⟨k, hk0, hkne⟩ := hf2 (τ a₀) hτ0
  let e₀ : Fin d → ZMod 2 := rowW (W (sh (τ a₀))) k
  let ι : Option ↥A → (Fin d → ZMod 2) := fun o =>
    Option.elim o e₀ (fun y => rowW (W (mat y.1)) ⟨0, hd0⟩)
  have hι : Function.Injective ι := by
    intro o o' h
    rcases o with _ | y <;> rcases o' with _ | y'
    · rfl
    · exfalso
      have h' : e₀ = rowW (W (sh (τ y'))) ⟨0, hd0⟩ := by
        rw [← hshape y']
        exact h
      exact hkne (τ y') h'
    · exfalso
      have h' : e₀ = rowW (W (sh (τ y))) ⟨0, hd0⟩ := by
        rw [← hshape y]
        exact h.symm
      exact hkne (τ y) h'
    · have h' : rowW (W (sh (τ y))) ⟨0, hd0⟩ = rowW (W (sh (τ y'))) ⟨0, hd0⟩ := by
        rw [← hshape y, ← hshape y']
        exact h
      rw [hτinj y y' (hf1 _ _ h')]
  have hC : ∀ o : Option ↥A, ∀ v ∈ {v : Fin d → ZMod 2 | ∀ y ∈ A, W (mat y) *ᵥ v = v}, ι o ⬝ᵥ v = 0 := by
    intro o v hv
    rcases o with _ | y
    · show rowW (W (sh (τ a₀))) k ⬝ᵥ v = 0
      rw [← hshape a₀]
      exact rowW_dot _ (hv a₀.1 a₀.2) k
    · exact rowW_dot _ (hv y.1 y.2) _
  have hcard := FFC.card_mul_card_le_two_pow ι hι
    {v : Fin d → ZMod 2 | ∀ y ∈ A, W (mat y) *ᵥ v = v} hC
  rw [Finite.card_option] at hcard
  have hpos : 0 < Nat.card {v : Fin d → ZMod 2 | ∀ y ∈ A, W (mat y) *ᵥ v = v} :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, fun y _ => by simp⟩⟩, inferInstance⟩
  nlinarith

theorem card_mul_fixW4_lt (A : Subgroup (SLt 4)) (hU : A ≤ Ut 4)
    (hR : ∀ y ∈ A, ∀ i j : Fin 4, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card {v : Fin 6 → ZMod 2 | ∀ y ∈ A, B5FinWedge.wedgeMat4 (mat y) *ᵥ v = v} <
      2 ^ 6 :=
  card_mul_fix_lt_of_shape (d := 6) (by norm_num) A hA shape4 B5FinWedge.wedgeMat4
    (fun y => ![mat y.1 0 2, mat y.1 0 3, mat y.1 1 2, mat y.1 1 3])
    (fun y => eq_shape4 (hU y.2) (hR y.1 y.2))
    (by decide +kernel) shape4_facts.1 shape4_facts.2

@[expose] def shape5 (t : Fin 6 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, t 0, t 1, t 2; 0, 1, t 3, t 4, t 5; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem shape5_facts :
    (∀ t t' : Fin 6 → ZMod 2, rowW (JonesParshall.wedgeMat (shape5 t)) 0 =
        rowW (JonesParshall.wedgeMat (shape5 t')) 0 → t = t') ∧
    (∀ t : Fin 6 → ZMod 2, t ≠ 0 → ∃ k : Fin 10, rowW (JonesParshall.wedgeMat (shape5 t)) k ≠ 0 ∧
      ∀ t' : Fin 6 → ZMod 2, rowW (JonesParshall.wedgeMat (shape5 t)) k ≠
        rowW (JonesParshall.wedgeMat (shape5 t')) 0) := by
  decide +kernel

theorem eq_shape5 {y : SLt 5} (hU : y ∈ Ut 5)
    (hR : ∀ i j : Fin 5, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) :
    mat y = shape5 ![mat y 0 2, mat y 0 3, mat y 0 4, mat y 1 2, mat y 1 3, mat y 1 4] := by
  have h01 : mat y 0 1 = 0 := hR 0 1 (by decide) (single_block (by decide))
  have h23 : mat y 2 3 = 0 := hR 2 3 (by decide) (single_block (by decide))
  have h24 : mat y 2 4 = 0 := hR 2 4 (by decide) (single_block (by decide))
  have h34 : mat y 3 4 = 0 := hR 3 4 (by decide) (single_block (by decide))
  have h10 : mat y 1 0 = 0 := hU.1 1 0 (by decide)
  have h20 : mat y 2 0 = 0 := hU.1 2 0 (by decide)
  have h30 : mat y 3 0 = 0 := hU.1 3 0 (by decide)
  have h40 : mat y 4 0 = 0 := hU.1 4 0 (by decide)
  have h21 : mat y 2 1 = 0 := hU.1 2 1 (by decide)
  have h31 : mat y 3 1 = 0 := hU.1 3 1 (by decide)
  have h41 : mat y 4 1 = 0 := hU.1 4 1 (by decide)
  have h32 : mat y 3 2 = 0 := hU.1 3 2 (by decide)
  have h42 : mat y 4 2 = 0 := hU.1 4 2 (by decide)
  have h43 : mat y 4 3 = 0 := hU.1 4 3 (by decide)
  have h00 : mat y 0 0 = 1 := hU.2 0
  have h11 : mat y 1 1 = 1 := hU.2 1
  have h22 : mat y 2 2 = 1 := hU.2 2
  have h33 : mat y 3 3 = 1 := hU.2 3
  have h44 : mat y 4 4 = 1 := hU.2 4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shape5, h01, h23, h24, h34, h10, h20, h30, h40, h21, h31, h41, h32,
    h42, h43, h00, h11, h22, h33, h44]

theorem card_mul_fixW5_lt (A : Subgroup (SLt 5)) (hU : A ≤ Ut 5)
    (hR : ∀ y ∈ A, ∀ i j : Fin 5, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card {v : Fin 10 → ZMod 2 | ∀ y ∈ A, JonesParshall.wedgeMat (mat y) *ᵥ v = v} <
      2 ^ 10 :=
  card_mul_fix_lt_of_shape (d := 10) (by norm_num) A hA shape5 JonesParshall.wedgeMat
    (fun y => ![mat y.1 0 2, mat y.1 0 3, mat y.1 0 4, mat y.1 1 2, mat y.1 1 3, mat y.1 1 4])
    (fun y => eq_shape5 (hU y.2) (hR y.1 y.2))
    (by decide +kernel) shape5_facts.1 shape5_facts.2

end CFSG.Quasithin.FLc
