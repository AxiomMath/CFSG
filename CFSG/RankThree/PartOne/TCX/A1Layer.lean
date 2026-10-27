module

public import CFSG.RankThree.PartOne.KLCE.A1TypeII
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.KGD.D4Twist
public import CFSG.RankThree.PartOne.TCX.F4.LayerClaims
public import CFSG.Mathlib.RingTheory.UnitOrderOf

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial (sl2_closure_upper_lower)

open scoped MatrixGroups

section SL2

variable {K : Type} [Field K] [CharP K 2]

theorem wsl_conj_uSL (c : K) : WSL * uSL c * WSL⁻¹ = vSL c := by
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, hneg]

theorem wsl_conj_vSL (c : K) : WSL * vSL c * WSL⁻¹ = uSL c := by
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, hneg]

theorem wsl_mul_self : (WSL : SL2 K) * WSL = 1 := by
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, Matrix.mul_apply, Fin.sum_univ_two, hneg]

omit [CharP K 2] in
theorem map_wsl {L : Type} [Field L] (f : K →+* L) :
    Matrix.SpecialLinearGroup.map f (WSL : SL2 K) = WSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WSL]

theorem eq_one_of_commute_transvections (d : SL2 K)
    (h1 : d * uSL 1 = uSL 1 * d) (h2 : d * vSL 1 = vSL 1 * d) : d = 1 := by
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  have e1 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K)) h1
  have e2 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e1 e2
  have h11 := congrFun (congrFun e1 1) 1
  have h01 := congrFun (congrFun e1 0) 1
  have h00 := congrFun (congrFun e2 0) 0
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h11 h01 h00
  have hdet := d.2
  rw [Matrix.det_fin_two] at hdet
  have hd : (d : Matrix (Fin 2) (Fin 2) K) 1 1 = (d : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    linear_combination -h01
  have hsq : (d : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 = 1 := by
    rw [h00, h11, hd] at hdet
    linear_combination hdet
  have ha : (d : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 :=
    CharTwo.sq_injective (show (d : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 = 1 ^ 2 by
      rw [hsq, one_pow])
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, h00, h11, hd]

end SL2

section Rep

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem conj_rootSL2_of_neg_rep {n : ModGL τ L}
    (hn : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∀ c : L,
      n * pinnedX τ L α c * n⁻¹ = pinnedX τ L (-α) c)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (B : SL2 L) :
    n * rootSL2 τ L θ B * n⁻¹ = rootSL2 τ L θ (WSL * B * WSL⁻¹) := by
  let f : SL2 L →* ModGL τ L := (MulAut.conj n).toMonoidHom.comp (rootSL2 τ L θ)
  let g : SL2 L →* ModGL τ L := (rootSL2 τ L θ).comp (MulAut.conj (WSL : SL2 L)).toMonoidHom
  have hfg : f = g := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change n * rootSL2 τ L θ (uSL c) * n⁻¹ = rootSL2 τ L θ (WSL * uSL c * WSL⁻¹)
      rw [wsl_conj_uSL, rootSL2_uSL_of_charTwo hθ, rootSL2_vSL_of_charTwo hθ]
      exact hn θ hθ c
    · change n * rootSL2 τ L θ (vSL c) * n⁻¹ = rootSL2 τ L θ (WSL * vSL c * WSL⁻¹)
      rw [wsl_conj_vSL, rootSL2_uSL_of_charTwo hθ, rootSL2_vSL_of_charTwo hθ]
      have := hn (-θ) (IsRoot.neg hθ) c
      rwa [neg_neg] at this
  exact DFunLike.congr_fun hfg B

omit [CharP L 2] in
theorem exists_P0_wsl {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosed L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ P₀ : GL (Fin 2) L, P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ =
      Matrix.SpecialLinearGroup.toGL (WSL : SL2 L) := by
  refine CFSG.RankThree.PartOne.KGD.exists_twist_antidiag (K := K) Fr hFr 1 (-1)
    (Matrix.SpecialLinearGroup.toGL (WSL : SL2 L)) ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  fin_cases i <;> fin_cases j <;> simp [WSL]

end Rep

section Layer

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]

theorem a1_layer_of_frame {p f₀ : ℕ} (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ (p * f₀)) {σ : K ≃+* K} (hσ1 : σ ≠ 1) {θ : Fin τ.rank → ℤ}
    {n₀ : ModGL τ L} {J₀ : SL(2, L)}
    (hn₀ : ∀ B : SL(2, L), n₀ * rootSL2 τ L θ B * n₀⁻¹ = rootSL2 τ L θ (J₀ * B * J₀⁻¹))
    {Φ₀ : L →+* L} (hσ : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c))
    {P₀ : GL (Fin 2) L}
    (hP₀ : P₀ * Matrix.GeneralLinearGroup.map Φ₀ P₀⁻¹ = Matrix.SpecialLinearGroup.toGL J₀) :
    ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D), Function.Injective ρ' ∧
      ρ'.range = (a1HomConj τ K L θ P₀).range ∧
      (∀ d, n₀ * Units.map (entrywiseHom Φ₀) (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaimsF4 p α Q := by
  refine ⟨SL(2, K), inferInstance, a1HomConj τ K L θ P₀,
    Matrix.SpecialLinearGroup.map σ.toRingHom, a1HomConj_injective θ P₀, rfl,
    fun B => a1_F0_compat_II hn₀ hσ hP₀ B, ?_⟩
  intro G _ α φ hφ hαφ Q hQ
  obtain ⟨-, hmove, -, hmodel, hfix⟩ := sl_type_claims (m := 0) hp5 hf₀ hK hσ1 α φ hφ hαφ Q hQ
  refine ⟨?_, hmodel, hfix⟩
  subst hQ
  have hu : Matrix.SpecialLinearGroup.map σ.toRingHom (uSL (1 : K)) = uSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL]
  have hv : Matrix.SpecialLinearGroup.map σ.toRingHom (vSL (1 : K)) = vSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vSL]
  rintro e ⟨d₀, rfl⟩ hin
  have hcomm : ∀ d : SL(2, K), Matrix.SpecialLinearGroup.map σ.toRingHom d = d →
      d₀ * d = d * d₀ := by
    intro d hd
    have h1 := hin (φ d) ⟨d, rfl⟩
    rw [hαφ, hd] at h1
    apply hφ
    rw [map_mul, map_mul]
    calc φ d₀ * φ d = (φ d₀ * φ d * (φ d₀)⁻¹) * φ d₀ := by group
      _ = φ d * φ d₀ := by rw [← h1]
  have hd₀ : d₀ = 1 := eq_one_of_commute_transvections d₀ (hcomm _ hu) (hcomm _ hv)
  obtain ⟨g, hgQ, hg⟩ := hmove
  apply hg
  have := hin g hgQ
  rw [hd₀, map_one] at this
  simpa using this

end Layer

end CFSG.RankThree.PartOne.TCX
