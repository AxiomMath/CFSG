module

public import CFSG.LocalAnalysis.StandardType.GGZSMonShape

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}
  {b : Module.Basis (Fin n) (ZMod p) U}

private lemma eq_of_smul_basis_eq_smul_basis {k l : Fin n} {a a' : ZMod p} (ha : a ≠ 0)
    (h : a • b k = a' • b l) : k = l ∧ a = a' := by
  by_cases hkl : k = l
  · subst hkl
    refine ⟨rfl, ?_⟩
    have hc := congrArg (fun v => b.repr v k) h
    simpa [Module.Basis.repr_self_apply, Finsupp.smul_apply] using hc
  · exfalso
    apply ha
    have hc := congrArg (fun v => b.repr v k) h
    simpa [Module.Basis.repr_self_apply, Finsupp.smul_apply, hkl] using hc

private def word (u v : U ≃ₗ[ZMod p] U) : Fin 6 → U ≃ₗ[ZMod p] U :=
  ![1, u, v, u * v, v * u, u * v * u]

private def lineX (x y z : Fin n) : Fin 6 → Fin n := ![x, y, x, y, z, z]

private def lineY (x y z : Fin n) : Fin 6 → Fin n := ![y, x, z, z, x, y]

private def coeffX (α β : (ZMod p)ˣ) : Fin 6 → (ZMod p)ˣ :=
  ![1, α, 1, α, α * β, α * β]

private def coeffY (α β : (ZMod p)ˣ) : Fin 6 → (ZMod p)ˣ :=
  ![1, α⁻¹, β, β, α⁻¹, 1]

private lemma word_apply_x {x y z : Fin n} (hxz : x ≠ z) {α β : (ZMod p)ˣ}
    {u v : U ≃ₗ[ZMod p] U} (hu : IsTwistedSwap b u x y α)
    (hv : IsTwistedSwap b v y z β) (w : Fin 6) :
    word u v w (b x) = (coeffX α β w : ZMod p) • b (lineX x y z w) := by
  fin_cases w <;>
    simp [word, lineX, coeffX, LinearEquiv.mul_apply, hu.2.1, hv.2.1, hv.2.2.2 x hu.1 hxz,
      hu.2.2.2 z (Ne.symm hxz) (Ne.symm hv.1), smul_smul]

private lemma word_apply_y {x y z : Fin n} (hxz : x ≠ z) {α β : (ZMod p)ˣ}
    {u v : U ≃ₗ[ZMod p] U} (hu : IsTwistedSwap b u x y α)
    (hv : IsTwistedSwap b v y z β) (w : Fin 6) :
    word u v w (b y) = (coeffY α β w : ZMod p) • b (lineY x y z w) := by
  fin_cases w <;>
    simp [word, lineY, coeffY, LinearEquiv.mul_apply, hu.2.1, hv.2.1, hu.2.2.1,
      hu.2.2.2 z (Ne.symm hxz) (Ne.symm hv.1), hv.2.2.2 x hu.1 hxz, smul_smul]

private lemma word_mem {u v : U ≃ₗ[ZMod p] U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (huH : u ∈ H) (hvH : v ∈ H) (w : Fin 6) :
    word u v w ∈ H := by
  fin_cases w
  · simp [word]
  · simpa [word] using huH
  · simpa [word] using hvH
  · simpa [word] using H.mul_mem huH hvH
  · simpa [word] using H.mul_mem hvH huH
  · simpa [word] using H.mul_mem (H.mul_mem huH hvH) huH

private def diagWord (δ δ' : U ≃ₗ[ZMod p] U) (i j : ℕ) : U ≃ₗ[ZMod p] U :=
  δ ^ i * δ' ^ j

private lemma isDiagonal_diagWord {δ δ' : U ≃ₗ[ZMod p] U} {e e' : Fin n → (ZMod p)ˣ}
    (hδ : IsDiagonal b δ e) (hδ' : IsDiagonal b δ' e') (i j : ℕ) :
    IsDiagonal b (diagWord δ δ' i j) (fun k => e k ^ i * e' k ^ j) :=
  fun k => (hδ.pow i).mul (hδ'.pow j) k

private lemma diagWord_mem {δ δ' : U ≃ₗ[ZMod p] U} {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hδH : δ ∈ H) (hδ'H : δ' ∈ H) (i j : ℕ) : diagWord δ δ' i j ∈ H := by
  simpa [diagWord] using H.mul_mem (H.pow_mem hδH i) (H.pow_mem hδ'H j)

private lemma diagWord_apply_x {x y z : Fin n} {ζ : (ZMod p)ˣ} {δ δ' : U ≃ₗ[ZMod p] U}
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    (hxy : x ≠ y) (hxz : x ≠ z) (i j : ℕ) :
    diagWord δ δ' i j (b x) = ((ζ ^ (i + j) : (ZMod p)ˣ) : ZMod p) • b x := by
  rw [isDiagonal_diagWord hδ hδ' i j x]
  congr 1
  simp [pairUnit, Equiv.swap_apply_def, hxy, hxz, ← pow_add]

private lemma diagWord_apply_y {x y z : Fin n} {ζ : (ZMod p)ˣ} {δ δ' : U ≃ₗ[ZMod p] U}
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (i j : ℕ) :
    diagWord δ δ' i j (b y) = (((ζ⁻¹) ^ i : (ZMod p)ˣ) : ZMod p) • b y := by
  rw [isDiagonal_diagWord hδ hδ' i j y]
  congr 1
  simp [pairUnit, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

private lemma diagWord_apply_z {x y z : Fin n} {ζ : (ZMod p)ˣ} {δ δ' : U ≃ₗ[ZMod p] U}
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (i j : ℕ) :
    diagWord δ δ' i j (b z) = (((ζ⁻¹) ^ j : (ZMod p)ˣ) : ZMod p) • b z := by
  rw [isDiagonal_diagWord hδ hδ' i j z]
  congr 1
  simp [pairUnit, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

private lemma eq_of_lineX_eq_lineY_eq {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {w w' : Fin 6} (hX : lineX x y z w = lineX x y z w')
    (hY : lineY x y z w = lineY x y z w') : w = w' := by
  fin_cases w <;> fin_cases w' <;>
    simp [lineX, lineY, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz] at hX hY ⊢

private lemma inv_pow_inj {ζ : (ZMod p)ˣ} (hζ : ζ ^ 2 ≠ 1) {i j : Fin 3}
    (h : (ζ⁻¹) ^ (i : ℕ) = (ζ⁻¹) ^ (j : ℕ)) : i = j := by
  wlog hij : (i : ℕ) ≤ (j : ℕ) generalizing i j
  · exact (this h.symm (by omega)).symm
  have hd : (j : ℕ) - (i : ℕ) = 0 ∨ (j : ℕ) - (i : ℕ) = 1 ∨ (j : ℕ) - (i : ℕ) = 2 := by
    omega
  have h1 : (ζ⁻¹) ^ ((j : ℕ) - (i : ℕ)) = 1 := by
    have h2 : (ζ⁻¹) ^ (j : ℕ) =
        (ζ⁻¹) ^ (i : ℕ) * (ζ⁻¹) ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2] at h
    have hh : (ζ⁻¹) ^ (i : ℕ) * 1 =
        (ζ⁻¹) ^ (i : ℕ) * (ζ⁻¹) ^ ((j : ℕ) - (i : ℕ)) := by
      simpa using h
    exact (mul_left_cancel hh).symm
  rcases hd with hd | hd | hd
  · apply Fin.ext
    omega
  · exfalso
    apply hζ
    have hζi : ζ = 1 := by
      have : ζ⁻¹ = 1 := by simpa [hd] using h1
      simpa using congrArg Inv.inv this
    rw [hζi]
    norm_num
  · exfalso
    apply hζ
    have : (ζ⁻¹) ^ 2 = 1 := by simpa [hd] using h1
    simpa using congrArg Inv.inv this

private lemma line_eq_of_mul_diagWord_eq [Fact p.Prime] {x y z : Fin n} (hxz : x ≠ z)
    {u v δ δ' : U ≃ₗ[ZMod p] U} {α β ζ : (ZMod p)ˣ}
    (hu : IsTwistedSwap b u x y α) (hv : IsTwistedSwap b v y z β)
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    {w w' : Fin 6} {i j i' j' : ℕ}
    (h : word u v w * diagWord δ δ' i j = word u v w' * diagWord δ δ' i' j') :
    lineX x y z w = lineX x y z w' ∧ lineY x y z w = lineY x y z w' := by
  have hxy : x ≠ y := hu.1
  have hyz : y ≠ z := hv.1
  have hWx : ∀ w, word u v w (b x) =
      (coeffX α β w : ZMod p) • b (lineX x y z w) := word_apply_x hxz hu hv
  have hWy : ∀ w, word u v w (b y) =
      (coeffY α β w : ZMod p) • b (lineY x y z w) := word_apply_y hxz hu hv
  have hDx : ∀ i j, diagWord δ δ' i j (b x) =
      ((ζ ^ (i + j) : (ZMod p)ˣ) : ZMod p) • b x :=
    diagWord_apply_x hδ hδ' hxy hxz
  have hDy : ∀ i j, diagWord δ δ' i j (b y) =
      (((ζ⁻¹) ^ i : (ZMod p)ˣ) : ZMod p) • b y :=
    diagWord_apply_y hδ hδ' hxy hxz hyz
  constructor
  · have hx := congrArg (fun f : U ≃ₗ[ZMod p] U => f (b x)) h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hDx, hDx,
      LinearEquiv.map_smul, LinearEquiv.map_smul, hWx, hWx, smul_smul, smul_smul] at hx
    have hx' : ((ζ ^ (i + j) * coeffX α β w : (ZMod p)ˣ) : ZMod p) •
        b (lineX x y z w) =
        ((ζ ^ (i' + j') * coeffX α β w' : (ZMod p)ˣ) : ZMod p) •
          b (lineX x y z w') := by
      simpa [Units.val_mul] using hx
    exact (eq_of_smul_basis_eq_smul_basis (Units.ne_zero _) hx').1
  · have hy := congrArg (fun f : U ≃ₗ[ZMod p] U => f (b y)) h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hDy, hDy,
      LinearEquiv.map_smul, LinearEquiv.map_smul, hWy, hWy, smul_smul, smul_smul] at hy
    have hy' : (((ζ⁻¹) ^ i * coeffY α β w : (ZMod p)ˣ) : ZMod p) •
        b (lineY x y z w) =
        (((ζ⁻¹) ^ i' * coeffY α β w' : (ZMod p)ˣ) : ZMod p) •
          b (lineY x y z w') := by
      simpa [Units.val_mul] using hy
    exact (eq_of_smul_basis_eq_smul_basis (Units.ne_zero _) hy').1

private lemma eq_of_diagWord_eq [Fact p.Prime] {x y z : Fin n} (hxz : x ≠ z)
    {δ δ' : U ≃ₗ[ZMod p] U} {ζ : (ZMod p)ˣ}
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    (hxy : x ≠ y) (hyz : y ≠ z) (hζ : ζ ^ 2 ≠ 1)
    {i i' j j' : Fin 3}
    (h : diagWord δ δ' (i : ℕ) (j : ℕ) = diagWord δ δ' (i' : ℕ) (j' : ℕ)) :
    i = i' ∧ j = j' := by
  have hDy : ∀ i j, diagWord δ δ' i j (b y) =
      (((ζ⁻¹) ^ i : (ZMod p)ˣ) : ZMod p) • b y :=
    diagWord_apply_y hδ hδ' hxy hxz hyz
  have hDz : ∀ i j, diagWord δ δ' i j (b z) =
      (((ζ⁻¹) ^ j : (ZMod p)ˣ) : ZMod p) • b z :=
    diagWord_apply_z hδ hδ' hxy hxz hyz
  have hy := congrArg (fun f : U ≃ₗ[ZMod p] U => f (b y)) h
  rw [hDy, hDy] at hy
  obtain ⟨-, hcy⟩ := eq_of_smul_basis_eq_smul_basis (Units.ne_zero _) hy
  have hi : i = i' := inv_pow_inj hζ (Units.ext hcy)
  have hz := congrArg (fun f : U ≃ₗ[ZMod p] U => f (b z)) h
  rw [hDz, hDz] at hz
  obtain ⟨-, hcz⟩ := eq_of_smul_basis_eq_smul_basis (Units.ne_zero _) hz
  have hj : j = j' := inv_pow_inj hζ (Units.ext hcz)
  exact ⟨hi, hj⟩

private lemma countMap_injective [Fact p.Prime] {x y z : Fin n} (hxz : x ≠ z)
    {u v δ δ' : U ≃ₗ[ZMod p] U} {α β ζ : (ZMod p)ˣ}
    (hu : IsTwistedSwap b u x y α) (hv : IsTwistedSwap b v y z β)
    (hδ : IsDiagonal b δ (pairUnit p x y ζ))
    (hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z))
    (hζ : ζ ^ 2 ≠ 1) :
    Function.Injective (fun q : Fin 6 × Fin 3 × Fin 3 =>
      word u v q.1 * diagWord δ δ' q.2.1 q.2.2) := by
  rintro ⟨w, i, j⟩ ⟨w', i', j'⟩ h
  obtain ⟨hX, hY⟩ := line_eq_of_mul_diagWord_eq hxz hu hv hδ hδ' h
  have hw : w = w' := eq_of_lineX_eq_lineY_eq hu.1 hxz hv.1 hX hY
  subst w'
  have hD : diagWord δ δ' (i : ℕ) (j : ℕ) = diagWord δ δ' (i' : ℕ) (j' : ℕ) :=
    mul_left_cancel h
  obtain ⟨hi, hj⟩ := eq_of_diagWord_eq hxz hδ hδ' hu.1 hv.1 hζ hD
  rw [hi, hj]

theorem le_card_of_isTwistedSwap [Fact p.Prime] {x y z : Fin n} (hxz : x ≠ z)
    {u v δ : U ≃ₗ[ZMod p] U} {α β ζ : (ZMod p)ˣ} (hu : IsTwistedSwap b u x y α)
    (hv : IsTwistedSwap b v y z β) (hδ : IsDiagonal b δ (pairUnit p x y ζ)) (hζ : ζ ^ 2 ≠ 1)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (huH : u ∈ H) (hvH : v ∈ H) (hδH : δ ∈ H) :
    54 ≤ Nat.card H := by
  let δ' : U ≃ₗ[ZMod p] U := v * δ * v⁻¹
  have hδ' : IsDiagonal b δ' (pairUnit p x y ζ ∘ Equiv.swap y z) := hv.conj_isDiagonal hδ
  have hδ'H : δ' ∈ H := by
    dsimp [δ']
    exact H.mul_mem (H.mul_mem hvH hδH) (H.inv_mem hvH)
  let F : Fin 6 × Fin 3 × Fin 3 → H := fun q =>
    ⟨word u v q.1 * diagWord δ δ' q.2.1 q.2.2,
      H.mul_mem (word_mem huH hvH q.1) (diagWord_mem hδH hδ'H q.2.1 q.2.2)⟩
  have hF : Function.Injective F := fun q q' h =>
    countMap_injective hxz hu hv hδ hδ' hζ (congrArg Subtype.val h)
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis b
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun f : U ≃ₗ[ZMod p] U => (f : U → U)) DFunLike.coe_injective
  have : Finite H :=
    Finite.of_injective (fun h : H => (h : U ≃ₗ[ZMod p] U)) Subtype.coe_injective
  have hle := Nat.card_le_card_of_injective F hF
  have h54 : Nat.card (Fin 6 × Fin 3 × Fin 3) = 54 := by
    simp
  rw [h54] at hle
  exact hle

end CFSG.StandardType.ZS

end
