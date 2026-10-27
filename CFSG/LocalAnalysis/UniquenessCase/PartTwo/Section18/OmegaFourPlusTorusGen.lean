module

public import CFSG.Quasithin.Background.TorusComplementH1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RModel
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.H CFSG.Open.StatedAPI
open CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData
open scoped MatrixGroups Matrix

theorem diagonalSL_mul_eq_self_of_ne_one {K : Type} [Field K] {lam : Kˣ} (hlam : lam ≠ 1)
    {X : Matrix (Fin 2) (Fin 2) K}
    (hX : (diagonalSL K lam : Matrix (Fin 2) (Fin 2) K) * X = X) : X = 0 := by
  have hlamK : ((lam : K) - 1) ≠ 0 := by
    intro h
    exact hlam (Units.ext (sub_eq_zero.mp h))
  have hlaminvK : (((lam⁻¹ : Kˣ) : K) - 1) ≠ 0 := by
    intro h
    have h1 : (lam⁻¹ : Kˣ) = 1 := Units.ext (sub_eq_zero.mp h)
    exact hlam (inv_eq_one.mp h1)
  ext i j
  fin_cases i
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 j) hX
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagonalSL_apply_zero_zero,
      diagonalSL_apply_zero_one] at h
    have h0 : ((lam : K) - 1) * X 0 j = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hlamK
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 j) hX
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagonalSL_apply_one_zero,
      diagonalSL_apply_one_one] at h
    have h' : ((lam⁻¹ : Kˣ) : K) * X 1 j = X 1 j := by
      simpa using h
    have h0 : (((lam⁻¹ : Kˣ) : K) - 1) * X 1 j = 0 := by
      rw [sub_mul, one_mul, h', sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hlaminvK

theorem hasFpfTorusGen_statedOmegaPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) : HasFpfTorusGen (StatedOmega (StatedQuadPlus 2 K)) := by
  classical
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedOmega (StatedQuadPlus 2 K)
  let S : OmegaModel (StdMod (Fin 2 ⊕ Fin 2) K) := stdOmegaModel h4
  have hSω : S.omega = natImage Γ := stdOmegaModel.omega h4
  have hcard : Nat.card S.omega = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
    rw [hSω, natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
    obtain ⟨e⟩ := CFSG.RankThree.GF2n.Stroth80.statedOmega_plus_four_nonempty_equiv K h4
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_statedSL_two K]
    exact (pow_two _).symm
  have hSω0 : S.omega = S.omega0 := OmegaModel.omega_eq_omega0_of_card S hcard
  obtain ⟨lam, hlamgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hlamcard : orderOf lam = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hlamgen, Nat.card_units]
  have hlamne : lam ≠ 1 := by
    intro h
    have h1 : orderOf lam = 1 := by rw [h, orderOf_one]
    rw [hlamcard] at h1
    omega
  have hqEven : Even (Nat.card K) := by
    letI := Fintype.ofFinite K
    rw [Nat.even_iff, Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hoddq : Odd (Nat.card K - 1) :=
    Nat.Even.sub_odd (by omega) hqEven odd_one
  let d : Matrix.SpecialLinearGroup (Fin 2) K := diagonalSL K lam
  have hdPow : d ^ (Nat.card K - 1) = 1 := by
    rw [show d = diagonalSL K lam from rfl, ← map_pow, ← hlamcard, pow_orderOf_eq_one, map_one]
  have hdT : (d : Matrix (Fin 2) (Fin 2) K)ᵀ = (d : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, diagonalSL_apply_zero_zero, diagonalSL_apply_one_one,
        diagonalSL_apply_zero_one, diagonalSL_apply_one_zero]
  have hof0 : OmegaModel.ofMat (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [OmegaModel.ofMat]
  let x₁ : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := S.jHom (d, 1)
  let x₂ : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) := S.jHom (1, d)
  have hx₁ω0 : x₁ ∈ S.omega0 := ⟨(d, 1), rfl⟩
  have hx₂ω0 : x₂ ∈ S.omega0 := ⟨(1, d), rfl⟩
  have hx₁ω : x₁ ∈ natImage Γ := by
    rw [← hSω, hSω0]
    exact hx₁ω0
  have hx₂ω : x₂ ∈ natImage Γ := by
    rw [← hSω, hSω0]
    exact hx₂ω0
  rw [natImage_eq_map] at hx₁ω hx₂ω
  obtain ⟨γ₁, hγ₁Γ, hx₁⟩ := Subgroup.mem_map.mp hx₁ω
  obtain ⟨γ₂, hγ₂Γ, hx₂⟩ := Subgroup.mem_map.mp hx₂ω
  let γ₁' : ↥Γ := ⟨γ₁, hγ₁Γ⟩
  let γ₂' : ↥Γ := ⟨γ₂, hγ₂Γ⟩
  have hx₁' : matHom (γ₁' : GL (Fin 2 ⊕ Fin 2) K) = x₁ := hx₁
  have hx₂' : matHom (γ₂' : GL (Fin 2 ⊕ Fin 2) K) = x₂ := hx₂
  let T₀ : Set ↥Γ := {γ₁', γ₂'}
  have hx₁pow : x₁ ^ (Nat.card K - 1) = 1 := by
    rw [show x₁ = S.jHom (d, 1) from rfl, ← map_pow, Prod.pow_mk, hdPow, one_pow]
    exact map_one S.jHom
  have hx₂pow : x₂ ^ (Nat.card K - 1) = 1 := by
    rw [show x₂ = S.jHom (1, d) from rfl, ← map_pow, Prod.pow_mk, hdPow, one_pow]
    exact map_one S.jHom
  have hodd₁ : Odd (orderOf γ₁') := by
    have hdvd : orderOf x₁ ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hx₁pow
    have hoddx : Odd (orderOf x₁) := hoddq.of_dvd_nat hdvd
    rw [← Subgroup.orderOf_coe γ₁',
      ← orderOf_injective matHom matHom_injective (γ₁' : GL (Fin 2 ⊕ Fin 2) K), hx₁']
    exact hoddx
  have hodd₂ : Odd (orderOf γ₂') := by
    have hdvd : orderOf x₂ ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hx₂pow
    have hoddx : Odd (orderOf x₂) := hoddq.of_dvd_nat hdvd
    rw [← Subgroup.orderOf_coe γ₂',
      ← orderOf_injective matHom matHom_injective (γ₂' : GL (Fin 2 ⊕ Fin 2) K), hx₂']
    exact hoddx
  have hx₁f : x₁ ∈ S.factor 0 := ⟨d, rfl⟩
  have hx₂f : x₂ ∈ S.factor 1 := ⟨d, rfl⟩
  have hcomm₁₂ : Commute γ₁' γ₂' := by
    apply Subtype.ext
    apply matHom_injective
    change matHom ((γ₁' : GL (Fin 2 ⊕ Fin 2) K) * (γ₂' : GL (Fin 2 ⊕ Fin 2) K)) =
      matHom ((γ₂' : GL (Fin 2 ⊕ Fin 2) K) * (γ₁' : GL (Fin 2 ⊕ Fin 2) K))
    rw [map_mul, map_mul, hx₁', hx₂']
    exact S.factor_commute (by decide) x₁ hx₁f x₂ hx₂f
  have hfpf₁ : ∀ v : Fin 2 ⊕ Fin 2 → K,
      ((γ₁' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
        v → v = 0 := by
    intro v hv
    have hfix : x₁ (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
      rw [← hx₁']
      change Multiplicative.ofAdd (((γ₁' : GL (Fin 2 ⊕ Fin 2) K) : Matrix
        (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = Multiplicative.ofAdd v
      rw [hv]
    have hvec : S.vec (S.jHom (d, 1) (Multiplicative.ofAdd v)) =
        S.vec (Multiplicative.ofAdd v) := congrArg S.vec hfix
    rw [S.vec_jHom] at hvec
    rw [show S.vec (Multiplicative.ofAdd v) = v from stdOmegaModel.vec v] at hvec
    have hX : (d : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat v = OmegaModel.toMat v := by
      have h := congrArg OmegaModel.toMat hvec
      simpa [OmegaModel.toMat_ofMat] using h
    have hX0 : OmegaModel.toMat v = 0 := diagonalSL_mul_eq_self_of_ne_one hlamne hX
    have hv0 : v = 0 := by
      have h := congrArg OmegaModel.ofMat hX0
      rw [OmegaModel.ofMat_toMat] at h
      rw [h, hof0]
    exact hv0
  have hfpf₂ : ∀ v : Fin 2 ⊕ Fin 2 → K,
      ((γ₂' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
        v → v = 0 := by
    intro v hv
    have hfix : x₂ (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
      rw [← hx₂']
      change Multiplicative.ofAdd (((γ₂' : GL (Fin 2 ⊕ Fin 2) K) : Matrix
        (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = Multiplicative.ofAdd v
      rw [hv]
    have hvec : S.vec (S.jHom (1, d) (Multiplicative.ofAdd v)) =
        S.vec (Multiplicative.ofAdd v) := congrArg S.vec hfix
    rw [S.vec_jHom] at hvec
    rw [show S.vec (Multiplicative.ofAdd v) = v from stdOmegaModel.vec v] at hvec
    have hX : OmegaModel.toMat v * (d : Matrix (Fin 2) (Fin 2) K)ᵀ = OmegaModel.toMat v := by
      have h := congrArg OmegaModel.toMat hvec
      simpa [OmegaModel.toMat_ofMat] using h
    have hX0 : OmegaModel.toMat v = 0 := by
      have hXt : (d : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v)ᵀ =
          (OmegaModel.toMat v)ᵀ := by
        have h := congrArg Matrix.transpose hX
        simpa [Matrix.transpose_mul, hdT] using h
      have h0 : (OmegaModel.toMat v)ᵀ = 0 :=
        diagonalSL_mul_eq_self_of_ne_one hlamne hXt
      simpa using congrArg Matrix.transpose h0
    have hv0 : v = 0 := by
      have h := congrArg OmegaModel.ofMat hX0
      rw [OmegaModel.ofMat_toMat] at h
      rw [h, hof0]
    exact hv0
  have hgen : (⊤ : Subgroup ↥Γ) ≤
      Subgroup.closure {g : ↥Γ | ∃ γ ∈ T₀, Commute g γ} := by
    intro g _
    let C : Subgroup ↥Γ := Subgroup.closure {g : ↥Γ | ∃ γ ∈ T₀, Commute g γ}
    change g ∈ C
    have hgω : matHom (g : GL (Fin 2 ⊕ Fin 2) K) ∈ S.omega0 := by
      rw [← hSω0, hSω, natImage_eq_map]
      exact Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩
    change matHom (g : GL (Fin 2 ⊕ Fin 2) K) ∈ (S.jHom).range at hgω
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hgω
    let y₀ := S.jHom (p.1, 1)
    let y₁ := S.jHom (1, p.2)
    have hy₀ : y₀ ∈ S.factor 0 := ⟨p.1, rfl⟩
    have hy₁ : y₁ ∈ S.factor 1 := ⟨p.2, rfl⟩
    have hprod : matHom (g : GL (Fin 2 ⊕ Fin 2) K) = y₀ * y₁ := by
      rw [← hp]
      change S.jHom p = S.jHom (p.1, 1) * S.jHom (1, p.2)
      rw [← map_mul]
      congr 1
      ext <;> simp
    have hy₀ω0 : y₀ ∈ S.omega0 := by
      rw [← S.factor_sup]
      exact Subgroup.mem_sup_left hy₀
    have hy₁ω0 : y₁ ∈ S.omega0 := by
      rw [← S.factor_sup]
      exact Subgroup.mem_sup_right hy₁
    have hy₀ω : y₀ ∈ natImage Γ := by
      rw [← hSω, hSω0]
      exact hy₀ω0
    have hy₁ω : y₁ ∈ natImage Γ := by
      rw [← hSω, hSω0]
      exact hy₁ω0
    rw [natImage_eq_map] at hy₀ω hy₁ω
    obtain ⟨δ₀, hδ₀Γ, hδ₀⟩ := Subgroup.mem_map.mp hy₀ω
    obtain ⟨δ₁, hδ₁Γ, hδ₁⟩ := Subgroup.mem_map.mp hy₁ω
    let δ₀' : ↥Γ := ⟨δ₀, hδ₀Γ⟩
    let δ₁' : ↥Γ := ⟨δ₁, hδ₁Γ⟩
    have hδ₀C : δ₀' ∈ C := by
      refine Subgroup.subset_closure ⟨γ₂', ?_, ?_⟩
      · simp [T₀]
      · apply Subtype.ext
        apply matHom_injective
        change matHom ((δ₀' : GL (Fin 2 ⊕ Fin 2) K) * (γ₂' : GL (Fin 2 ⊕ Fin 2) K)) =
          matHom ((γ₂' : GL (Fin 2 ⊕ Fin 2) K) * (δ₀' : GL (Fin 2 ⊕ Fin 2) K))
        rw [map_mul, map_mul, hδ₀, hx₂']
        exact S.factor_commute (by decide) y₀ hy₀ x₂ hx₂f
    have hδ₁C : δ₁' ∈ C := by
      refine Subgroup.subset_closure ⟨γ₁', ?_, ?_⟩
      · simp [T₀]
      · apply Subtype.ext
        apply matHom_injective
        change matHom ((δ₁' : GL (Fin 2 ⊕ Fin 2) K) * (γ₁' : GL (Fin 2 ⊕ Fin 2) K)) =
          matHom ((γ₁' : GL (Fin 2 ⊕ Fin 2) K) * (δ₁' : GL (Fin 2 ⊕ Fin 2) K))
        rw [map_mul, map_mul, hδ₁, hx₁']
        exact S.factor_commute (by decide) y₁ hy₁ x₁ hx₁f
    have hgprod : g = δ₀' * δ₁' := by
      apply Subtype.ext
      apply matHom_injective
      change matHom (g : GL (Fin 2 ⊕ Fin 2) K) =
        matHom ((δ₀' : GL (Fin 2 ⊕ Fin 2) K) * (δ₁' : GL (Fin 2 ⊕ Fin 2) K))
      rw [hprod, map_mul, hδ₀, hδ₁]
    rw [hgprod]
    exact C.mul_mem hδ₀C hδ₁C
  refine ⟨T₀, ⟨γ₁', by simp [T₀]⟩, ?_, ?_, ?_, hgen⟩
  · intro γ hγ
    simp only [T₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact hodd₁
    · exact hodd₂
  · intro γ hγ v hv
    simp only [T₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact hfpf₁ v hv
    · exact hfpf₂ v hv
  · intro γ hγ γ' hγ'
    simp only [T₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ hγ'
    rcases hγ with rfl | rfl <;> rcases hγ' with rfl | rfl
    · exact Commute.refl γ₁'
    · exact hcomm₁₂
    · exact hcomm₁₂.symm
    · exact Commute.refl γ₂'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
