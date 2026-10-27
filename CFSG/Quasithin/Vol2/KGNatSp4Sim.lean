module

public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K]

theorem spB_mulVec {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ StatedSp 2 K)
    (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x)
      ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y) = Matrix.toBilin' (spJ K) x y := by
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp hA
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem statedSp_mulVec_inv (γ : ↥(StatedSp 2 K)) (y : Fin 2 ⊕ Fin 2 → K) :
    ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((((γ⁻¹ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem exists_similitude (L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      L (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ L x) :
    ∃ c : K, ∀ x y, Matrix.toBilin' (spJ K) (L x) (L y) = c * Matrix.toBilin' (spJ K) x y := by
  set B := Matrix.toBilin' (spJ K) with hBdef
  have hB : B.Nondegenerate := toBilin'_spJ_nondegenerate
  set B' : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) := B.compl₁₂ L L with hB'
  have hB'apply : ∀ x y, B' x y = B (L x) (L y) := fun x y => rfl
  have hinv : ∀ (γ : ↥(StatedSp 2 K)) (x y : Fin 2 ⊕ Fin 2 → K),
      B' (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x)
        (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y) =
      B' x y := by
    intro γ x y
    obtain ⟨γ', hγ'⟩ := hL γ
    rw [hB'apply, hB'apply, hγ', hγ']
    exact spB_mulVec γ'.2 (L x) (L y)
  set Φ : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    (B.toDual hB).symm.toLinearMap ∘ₗ B' with hΦ
  have hΦB : ∀ x y, B (Φ x) y = B' x y := by
    intro x y
    rw [← LinearMap.BilinForm.toDual_def hB, hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hBinj : ∀ u u' : Fin 2 ⊕ Fin 2 → K, (∀ y, B u y = B u' y) → u = u' := by
    intro u u' h
    apply (B.toDual hB).injective
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def]
    exact h y
  have hcomm : ∀ (γ : ↥(StatedSp 2 K)) (x : Fin 2 ⊕ Fin 2 → K),
      Φ (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Φ x := by
    intro γ x
    refine hBinj _ _ fun y => ?_
    rw [hΦB, ← statedSp_mulVec_inv γ y, hinv γ x, ← hΦB, spB_mulVec γ.2]
  obtain ⟨c, hc⟩ := commutant_statedSp Φ.toAddMonoidHom (fun γ x => by
    simp only [LinearMap.toAddMonoidHom_coe, linModelNat_lin]
    exact hcomm γ x)
  refine ⟨c, fun x y => ?_⟩
  have hcx : Φ x = c • x := hc x
  rw [← hB'apply, ← hΦB, hcx, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem similitude_eq_one [CharP K 2] {L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    (hLL : ∀ x, L (L x) = x) {c : K}
    (hc : ∀ x y, Matrix.toBilin' (spJ K) (L x) (L y) = c * Matrix.toBilin' (spJ K) x y) :
    c = 1 := by
  set x : Fin 2 ⊕ Fin 2 → K := Pi.single (.inl 0) 1
  set y : Fin 2 ⊕ Fin 2 → K := Pi.single (.inr 0) 1
  have hxy : Matrix.toBilin' (spJ K) x y = 1 := by
    rw [toBilin'_spJ_apply]
    simp [x, y, Fin.sum_univ_two]
  have h := hc (L x) (L y)
  rw [hLL, hLL, hc, hxy, mul_one] at h
  have h2 : (c + 1) ^ 2 = 0 := by
    have h2z : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination -h + (c + 1) * h2z
  have h3 := pow_eq_zero_iff two_ne_zero |>.mp h2
  linear_combination h3 - CharP.cast_eq_zero K 2

theorem card_le_of_isometry_fix [Finite K] {ι : Type*}
    (L : ι → (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hLinj : Function.Injective L)
    (hLB : ∀ i x y, Matrix.toBilin' (spJ K) (L i x) (L i y) = Matrix.toBilin' (spJ K) x y)
    {D₀ : Set (Fin 2 ⊕ Fin 2 → K)} (hfix : ∀ i, ∀ d ∈ D₀, L i d = d)
    (hD₀ : Nat.card K ^ 3 ≤ Nat.card D₀) : Nat.card ι ≤ Nat.card K := by
  classical
  set B := Matrix.toBilin' (spJ K) with hBdef
  have hB : B.Nondegenerate := toBilin'_spJ_nondegenerate
  set D := Submodule.span K D₀ with hD
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hD3 : 3 ≤ Module.finrank K D := by
    have h1 : Nat.card D₀ ≤ Nat.card D := Nat.card_mono (Set.toFinite _) Submodule.subset_span
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥D)] at h1
    exact (pow_le_pow_iff_right₀ hq).mp (hD₀.trans h1)
  have hfixD : ∀ i, ∀ d ∈ D, L i d = d := fun i d hd =>
    LinearMap.eqOn_span (f := L i) (g := LinearMap.id) (fun d hd => hfix i d hd) hd
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, D ⊔ K ∙ v₀ = ⊤ := by
    by_cases hDt : D = ⊤
    · exact ⟨0, by rw [hDt, top_sup_eq]⟩
    · obtain ⟨v₀, hv₀⟩ : ∃ v, v ∉ D := by
        by_contra h
        push Not at h
        exact hDt (eq_top_iff.mpr fun v _ => h v)
      refine ⟨v₀, Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)⟩
      have hlt : D < D ⊔ K ∙ v₀ := lt_of_le_of_ne le_sup_left fun h =>
        hv₀ (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := Submodule.finrank_lt hDt
      omega
  set R := B.orthogonal D with hR
  have hRcard : Nat.card R ≤ Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥R),
      LinearMap.BilinForm.finrank_orthogonal hB, hV]
    calc Nat.card K ^ (4 - Module.finrank K D) ≤ Nat.card K ^ 1 :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ = Nat.card K := pow_one _
  have hmem : ∀ i, L i v₀ - v₀ ∈ R := by
    intro i
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro d hd
    rw [map_sub, ← hLB i d v₀, hfixD i d hd, sub_self]
  refine (Nat.card_le_card_of_injective (fun i => (⟨L i v₀ - v₀, hmem i⟩ : R))
    fun i j hij => ?_).trans hRcard
  apply hLinj
  have hv : L i v₀ = L j v₀ := sub_left_inj.mp (congrArg Subtype.val hij)
  have hspan : Submodule.span K (D₀ ∪ {v₀}) = ⊤ := by
    rw [Submodule.span_union, ← hD, hv₀]
  refine LinearMap.ext_on hspan ?_
  rintro x (hx | hx)
  · rw [hfix i x hx, hfix j x hx]
  · rw [Set.mem_singleton_iff.mp hx, hv]

end CFSG.Quasithin.Vol2.KGNat
