module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.RankThree.Classical.SemilinearFixedBasis
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48DescentEigen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.Descent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Restrict

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def restrictForm {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K) (k₀ : Subfield K)
    (C : Submodule k₀ V) (σ₀ : k₀ →+* k₀) (hσ₀ : ∀ c : k₀, (σ₀ c : K) = σ (c : K))
    (hmem : ∀ x ∈ C, ∀ y ∈ C, B x y ∈ k₀) : C →ₛₗ[σ₀] C →ₗ[k₀] k₀ :=
  LinearMap.mk₂'ₛₗ σ₀ (RingHom.id k₀) (fun x y => ⟨B x y, hmem x x.2 y y.2⟩)
    (fun x x' y => Subtype.ext (by
      change B ((x : V) + x') y = B x y + B x' y
      rw [map_add, LinearMap.add_apply]))
    (fun c x y => Subtype.ext (by
      change B ((c : K) • (x : V)) y = (σ₀ c : K) * B x y
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ₀]))
    (fun x y y' => Subtype.ext (by
      change B x ((y : V) + y') = B x y + B x y'
      rw [map_add]))
    (fun c x y => Subtype.ext (by
      change B x ((c : K) • (y : V)) = (c : K) * B x y
      rw [map_smul, smul_eq_mul]))

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {k₀ : Subfield K} {C : Submodule k₀ V}
  {σ₀ : k₀ →+* k₀} {hσ₀ : ∀ c : k₀, (σ₀ c : K) = σ (c : K)}
  {hmem : ∀ x ∈ C, ∀ y ∈ C, B x y ∈ k₀}

theorem restrictForm_apply (x y : C) :
    ((restrictForm B k₀ C σ₀ hσ₀ hmem x y : k₀) : K) = B x y :=
  rfl

theorem restrictForm_isSymm (hB : B.IsSymm) : (restrictForm B k₀ C σ₀ hσ₀ hmem).IsSymm :=
  ⟨fun x y => Subtype.ext
    ((hσ₀ _).trans ((congrArg σ (restrictForm_apply x y)).trans (hB.eq x y)))⟩

theorem restrictForm_separatingLeft (hB : B.SeparatingLeft)
    (hspan : Submodule.span K (C : Set V) = ⊤) :
    (restrictForm B k₀ C σ₀ hσ₀ hmem).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  apply hB
  intro v
  have hv : v ∈ Submodule.span K (C : Set V) := by rw [hspan]; trivial
  have hle : Submodule.span K (C : Set V) ≤ LinearMap.ker (B x) :=
    Submodule.span_le.mpr fun y hy => by
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
  exact hle hv

end Restrict

section Semilinear

variable {K : Type} [Field K]

@[expose] def aFun (g₀ : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (v : Fin 4 → K) : Fin 4 → K :=
  g₀ *ᵥ fun i => φ (v i)

theorem map_mulVec_ringEquiv (φ : K ≃+* K) (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    (fun i => φ ((M *ᵥ v) i)) = M.map φ *ᵥ fun j => φ (v j) := by
  funext i
  exact RingHom.map_mulVec (φ : K →+* K) M v i

theorem aFun_add (g₀ : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (v w : Fin 4 → K) :
    aFun g₀ φ (v + w) = aFun g₀ φ v + aFun g₀ φ w := by
  unfold aFun
  rw [← mulVec_add]
  congr 1
  funext i
  exact φ.map_add (v i) (w i)

theorem aFun_smul (g₀ : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (c : K) (v : Fin 4 → K) :
    aFun g₀ φ (c • v) = φ c • aFun g₀ φ v := by
  unfold aFun
  rw [← mulVec_smul]
  congr 1
  funext i
  exact φ.map_mul c (v i)

theorem aFun_aFun (g₀ : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (v : Fin 4 → K) :
    aFun g₀ φ (aFun g₀ φ v) = (g₀ * g₀.map φ) *ᵥ fun i => φ (φ (v i)) := by
  unfold aFun
  rw [map_mulVec_ringEquiv, mulVec_mulVec]

theorem aFun_aFun_aFun (g₀ : Matrix (Fin 4) (Fin 4) K) {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1)
    (hN : g₀ * g₀.map φ * (g₀.map φ).map φ = 1) (v : Fin 4 → K) :
    aFun g₀ φ (aFun g₀ φ (aFun g₀ φ v)) = v := by
  have hφv : ∀ x, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : K ≃+* K => ψ x) hφ3
    simpa [pow_succ] using this
  rw [aFun_aFun g₀ φ v]
  unfold aFun
  rw [map_mulVec_ringEquiv, mulVec_mulVec]
  have h1 : (g₀ * g₀.map φ).map φ = g₀.map φ * (g₀.map φ).map φ :=
    Matrix.map_mul (f := (φ : K →+* K))
  rw [h1, ← Matrix.mul_assoc, hN]
  simp [hφv]

end Semilinear

section Form

variable {K : Type} [Field K] (hK : UnitaryFieldData 2 3 K)

noncomputable abbrev stdForm : (Fin 4 → K) →ₛₗ[hK.bar] (Fin 4 → K) →ₗ[K] K :=
  gramForm hK (1 : Matrix (Fin 4) (Fin 4) K)

theorem stdForm_apply (x y : Fin 4 → K) : stdForm hK x y = ∑ r, hK.bar (x r) * y r := by
  simp [stdForm, gramForm_apply, dotProduct]

theorem stdForm_mulVec {M : Matrix (Fin 4) (Fin 4) K} (hM : (M.map hK.bar)ᵀ * M = 1)
    (x y : Fin 4 → K) : stdForm hK (M *ᵥ x) (M *ᵥ y) = stdForm hK x y := by
  simp only [stdForm]
  rw [gramForm_mulVec, Matrix.mul_one, hM]

theorem map_stdForm (φ : K ≃+* K) (x y : Fin 4 → K) :
    φ (stdForm hK x y) = stdForm hK (fun i => φ (x i)) (fun i => φ (y i)) := by
  have hbarφ : ∀ c, φ (hK.bar c) = hK.bar (φ c) := fun c => by
    simp [UnitaryFieldData.bar_apply, map_pow]
  simp only [stdForm_apply, map_sum, map_mul, hbarφ]

end Form

section FixedField

theorem coe_bar_subfield {K : Type} [Field K] (hK : UnitaryFieldData 2 3 K) {k₀ : Subfield K}
    (h₀ : UnitaryFieldData 2 1 k₀) (c : k₀) : ((h₀.bar c : k₀) : K) = hK.bar (c : K) := by
  have : Finite K := hK.finite
  have : Fintype k₀ := Fintype.ofFinite k₀
  have hc : c ^ 4 = c := by
    have h1 := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, h₀.card] at h1
  have hc' : (c : K) ^ 4 = c := by exact_mod_cast congrArg Subtype.val hc
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply]
  push_cast
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hc']

end FixedField

section Columns

variable {K : Type} [Field K]

theorem exists_matrix_of_columns (hK : UnitaryFieldData 2 3 K)
    {g₀ p : Matrix (Fin 4) (Fin 4) K} {φ : K ≃+* K} (w : Fin 4 → Fin 4 → K) (d : Fin 4 → K)
    (hon : ∀ i j, stdForm hK (w i) (w j) = if i = j then 1 else 0)
    (hfixed : ∀ j, g₀ *ᵥ (fun s => φ (w j s)) = w j) (hd3 : ∀ j, d j ^ 3 = 1)
    (hev : ∀ j, p *ᵥ w j = d j • w j) :
    ∃ H : Matrix (Fin 4) (Fin 4) K, (H.map hK.bar)ᵀ * H = 1 ∧ g₀ * H.map φ = H ∧
      ∃ d : Fin 4 → K, (∀ i, d i ^ 3 = 1) ∧ p * H = H * diagonal d := by
  refine ⟨Matrix.of fun r j => w j r, ?_, ?_, d, hd3, ?_⟩
  · ext i j
    rw [Matrix.one_apply, ← hon, stdForm_apply]
    simp [Matrix.mul_apply]
  · ext r j
    have := congrFun (hfixed j) r
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this
  · ext r j
    have h1 := congrFun (hev j) r
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_comm]
    exact h1

end Columns

section Main

variable {K : Type} [Field K]

theorem exists_fixed_orthonormal_eigenbasis_gen
    (hK : UnitaryFieldData 2 3 K)
    {g₀ : Matrix (Fin 4) (Fin 4) K} (hg₀ : (g₀.map hK.bar)ᵀ * g₀ = 1)
    {φ : K ≃+* K} (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1)
    (hN : g₀ * g₀.map φ * (g₀.map φ).map φ = 1)
    {p : Matrix (Fin 4) (Fin 4) K} (hp : (p.map hK.bar)ᵀ * p = 1) (hp3 : p ^ 3 = 1)
    (hfix : g₀ * p.map φ = p * g₀) :
    ∃ H : Matrix (Fin 4) (Fin 4) K, (H.map hK.bar)ᵀ * H = 1 ∧ g₀ * H.map φ = H ∧
      ∃ d : Fin 4 → K, (∀ i, d i ^ 3 = 1) ∧ p * H = H * diagonal d := by
  classical
  have h3 : ∀ v, aFun g₀ φ (aFun g₀ φ (aFun g₀ φ v)) = v := aFun_aFun_aFun g₀ hφ3 hN
  let a : (Fin 4 → K) ≃+ (Fin 4 → K) :=
    { toFun := aFun g₀ φ
      invFun := fun v => aFun g₀ φ (aFun g₀ φ v)
      left_inv := h3
      right_inv := h3
      map_add' := aFun_add g₀ φ }
  have ha : ∀ (c : K) (v : Fin 4 → K), a (c • v) = φ c • a v := aFun_smul g₀ φ
  have hah : ∀ v, (⇑a)^[3] v = v := fun v => h3 v
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have := hK.finite
  obtain ⟨-, k₀, hk₀, hk₀card, b, hb, C, hC, ⟨b₀, -⟩, hfin, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two (e := 6) (by norm_num) hK.card φ
      hord (Module.finrank_fin_fun K) a ha hah
  have hk₀mem : ∀ c : K, c ∈ k₀ ↔ φ c = c := fun c => by
    rw [← SetLike.mem_coe, hk₀]
    rfl
  have hCmem : ∀ v : Fin 4 → K, v ∈ C ↔ g₀ *ᵥ (fun i => φ (v i)) = v := fun v => by
    rw [← SetLike.mem_coe, hC]
    rfl
  have hk₀card' : Nat.card k₀ = 2 ^ (2 * 1) := by rw [hk₀card]
  have h₀ : UnitaryFieldData 2 1 k₀ := ⟨Nat.prime_two, le_rfl, hk₀card'⟩
  have hBmem : ∀ x ∈ C, ∀ y ∈ C, stdForm hK x y ∈ k₀ := by
    intro x hx y hy
    rw [hk₀mem, map_stdForm, ← stdForm_mulVec hK hg₀, (hCmem x).mp hx, (hCmem y).mp hy]
  let B₀ : C →ₛₗ[h₀.bar] C →ₗ[k₀] k₀ :=
    restrictForm (stdForm hK) k₀ C h₀.bar (coe_bar_subfield hK h₀) hBmem
  have hspan : Submodule.span K (C : Set (Fin 4 → K)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact (hCmem _).mpr (hb i))
  have hB₀symm : B₀.IsSymm := restrictForm_isSymm (gramForm_isSymm hK (by simp))
  have hB₀sep : B₀.SeparatingLeft :=
    restrictForm_separatingLeft (gramForm_separatingLeft hK (by simp)) hspan
  have hpC : ∀ x ∈ C, p *ᵥ x ∈ C := by
    intro x hx
    rw [hCmem, map_mulVec_ringEquiv, mulVec_mulVec, hfix, ← mulVec_mulVec, (hCmem x).mp hx]
  let P : C →ₗ[k₀] C := ((Matrix.toLin' p).restrictScalars k₀).restrict hpC
  have hPx : ∀ x : C, ((P x : C) : Fin 4 → K) = p *ᵥ (x : Fin 4 → K) := fun x => rfl
  have hP3 : ∀ x : C, P (P (P x)) = x := fun x => Subtype.ext (by
    rw [hPx, hPx, hPx, mulVec_mulVec, mulVec_mulVec, ← pow_three', hp3, one_mulVec])
  have hPiso : ∀ x y : C, B₀ (P x) (P y) = B₀ x y := fun x y =>
    Subtype.ext (stdForm_mulVec hK hp _ _)
  have : Module.Finite k₀ C := Module.Finite.of_basis b₀
  obtain ⟨u, μ, hon, hev, hμ3⟩ := exists_orthonormal_eigenvectors h₀ hfin hB₀symm hB₀sep hP3 hPiso
  refine exists_matrix_of_columns hK (fun j => ((u j : C) : Fin 4 → K))
    (fun j => ((μ j : k₀) : K)) (fun i j => ?_) (fun j => (hCmem _).mp (u j).2)
    (fun j => ?_) (fun j => ?_)
  ·
    have h1 : stdForm hK (u i : Fin 4 → K) (u j : Fin 4 → K) =
        ((B₀ (u i) (u j) : k₀) : K) := rfl
    rw [h1, hon]
    split_ifs <;> simp
  ·
    have := congrArg Subtype.val (hμ3 j)
    simpa using this
  ·
    have := congrArg Subtype.val (hev j)
    simpa [hPx, Subfield.smul_def] using this

end Main

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.Descent
