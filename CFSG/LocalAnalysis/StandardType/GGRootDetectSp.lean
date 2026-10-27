module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag TauCeti.GLSymplecticFin Matrix

namespace RootDetectSp

variable {r : ℕ} {K : Type} [Field K]

theorem E_map (σ : K ≃+* K) (ρ : RootSubgroupIndex r) :
    (Symplectic.SpExtras.E K ρ).map σ = Symplectic.SpExtras.E K ρ := by
  cases ρ <;>
    simp only [Symplectic.SpExtras.E, Matrix.map_sub _ (map_sub σ), Matrix.map_add _ (map_add σ),
      Matrix.map_single, map_one]

theorem coe_elt (ρ : RootSubgroupIndex r) (t : K) :
    (((Symplectic.SpExtras.elt ρ t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + t • Symplectic.SpExtras.E K ρ :=
  Symplectic.SpExtras.mat_elt ρ t

theorem fieldSp_elt (σ : K ≃+* K) (ρ : RootSubgroupIndex r) (t : K) :
    fieldSp r K σ (Symplectic.SpExtras.elt ρ t) = Symplectic.SpExtras.elt ρ (σ t) := by
  apply Symplectic.SpExtras.mat_injective
  rw [Symplectic.SpExtras.mat_apply, Symplectic.SpExtras.mat_apply, coe_fieldSp, coe_elt, coe_elt,
    Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.map_smul' _ _ _ (map_mul σ), E_map]

theorem E_ne_zero (ρ : RootSubgroupIndex r) : Symplectic.SpExtras.E K ρ ≠ 0 := by
  intro h0
  have h1 := Symplectic.SpExtras.E_pos1 (F := K) ρ
  rw [h0] at h1
  exact zero_ne_one h1

theorem eq_one_of_mem_spScalars [CharP K 2] (hr : 1 ≤ r) {z : StatedSp r K}
    (hz : z ∈ spScalars r K) : z = 1 := by
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨u, hu⟩ := hz
  have hm : ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (u : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp z.2
  rw [hm] at hsp
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul] at hsp
  have h1 := congrFun (congrFun hsp (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₂, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h1
  have hu1 : (u : K) = 1 := HypSixTypeA.eq_one_of_mul_self_eq_one h1
  apply Subtype.ext
  apply Units.ext
  rw [hm, hu1, one_smul]
  rfl

theorem eq_of_proj_eq [CharP K 2] (hr : 1 ≤ r) {y₁ y₂ : StatedSp r K}
    (h : proj r K y₁ = proj r K y₂) : y₁ = y₂ := by
  have h1 : y₁⁻¹ * y₂ = 1 := eq_one_of_mem_spScalars hr (QuotientGroup.eq.mp h)
  exact (inv_mul_eq_one.mp h1)

theorem field_eq_one_sp {ρ : RootSubgroupIndex r} {A : gsp r K} {σ : K ≃+* K}
    {u W : StatedSp r K}
    (h : ∀ t : K, conjSp r K A (fieldSp r K σ (u * Symplectic.SpExtras.elt ρ t * u⁻¹)) =
      W * Symplectic.SpExtras.elt ρ t * W⁻¹) : σ = 1 := by
  obtain ⟨N, hN⟩ : ∃ N : GL (Fin r ⊕ Fin r) K, N = (W : GL (Fin r ⊕ Fin r) K)⁻¹ *
      (A : GL (Fin r ⊕ Fin r) K) * ((fieldSp r K σ u : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :=
    ⟨_, rfl⟩
  refine RootDetect.ringEquiv_eq_one_of_mul_conj (E := Symplectic.SpExtras.E K ρ)
    (M := (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (M' := ((N⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (E_ne_zero ρ) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) fun t => ?_
  have e : ((conjSp r K A (fieldSp r K σ (u * Symplectic.SpExtras.elt ρ t * u⁻¹)) :
      StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      ((W * Symplectic.SpExtras.elt ρ t * W⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :=
    congrArg Subtype.val (h t)
  rw [coe_conjSp, map_mul, map_mul, map_inv, fieldSp_elt] at e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
  have e' : ((Symplectic.SpExtras.elt ρ t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * N =
      N * ((Symplectic.SpExtras.elt ρ (σ t) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) := by
    rw [hN]
    exact HypSixTypeA.mul_conj_rel e.symm
  have e'' := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul, coe_elt, coe_elt] at e''
  exact e''

theorem exists_sp_conj_eq [Finite K] [CharP K 2] (A : gsp r K) :
    ∃ a : StatedSp r K, ∀ y : StatedSp r K, conjSp r K A y = a * y * a⁻¹ := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (μ : K)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact μ.ne_zero hs
  obtain ⟨S, hS⟩ : ∃ S : GL (Fin r ⊕ Fin r) K,
      S = Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 s hs0)⁻¹ := ⟨_, rfl⟩
  have hSm : (S : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      s⁻¹ • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hS, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
    simp
  have hSc : S ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, hS]
    exact ⟨_, rfl⟩
  have hss : s⁻¹ * s⁻¹ * (s * s) = 1 := by field_simp
  have ha : S * (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, Units.val_mul, hSm]
    have hμ' : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
        fromBlocks 0 1 (-1) 0 * ((A : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (μ : K) • fromBlocks 0 1 (-1) 0 := hμ
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_smul, Matrix.mul_smul, smul_smul]
    rw [hμ', smul_smul, hs, hss, one_smul]
  refine ⟨⟨S * A, ha⟩, fun y => Subtype.ext ?_⟩
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show (A : GL (Fin r ⊕ Fin r) K) * y * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
    S * A * y * (S * A)⁻¹
  have hcomm := Subgroup.mem_center_iff.mp hSc
  calc (A : GL (Fin r ⊕ Fin r) K) * y * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
      S * ((A : GL (Fin r ⊕ Fin r) K) * y * (A : GL (Fin r ⊕ Fin r) K)⁻¹) * S⁻¹ := by
        rw [← hcomm ((A : GL (Fin r ⊕ Fin r) K) * y * (A : GL (Fin r ⊕ Fin r) K)⁻¹)]
        group
    _ = S * A * y * (S * A)⁻¹ := by group

theorem commutator_statedSp_eq_top [Finite K] (hr : 3 ≤ r ∨ (2 ≤ r ∧ 4 ≤ Nat.card K)) :
    ⁅(⊤ : Subgroup (StatedSp r K)), (⊤ : Subgroup (StatedSp r K))⁆ = ⊤ := by
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  have hr1 : 1 ≤ r := by rcases hr with hr | hr <;> omega
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    by_cases h4 : 4 ≤ Nat.card K
    · exact Or.inl (Or.inr h4)
    · by_cases h3 : Nat.card K = 3
      · exact Or.inr (Or.inl ⟨h3, by rcases hr with hr | hr <;> omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by rcases hr with hr | hr <;> omega⟩)
  exact (Symplectic.isQuasisimple r K hr1 hF).1.commutator_eq_top

theorem ggPsiInnerDiag_sp_of_aut [Finite K] [CharP K 2] (hr : 1 ≤ r)
    (hperf : ⁅(⊤ : Subgroup (StatedSp r K)), (⊤ : Subgroup (StatedSp r K))⁆ = ⊤) {p : ℕ}
    (hform : ∀ α : MulAut (StatedProj (StatedSp r K)), α ^ p = 1 →
      ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ)
    {G : Type*} [Group G] {ψ : StatedSp r K →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp r K)) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin r → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum r K).roots) {u : StatedSp r K}
    (hT : GGTorusOnRoot (Symplectic.rootDatum r K) ψ c γ u) :
    GGPsiInnerDiag (Symplectic.rootDatum r K) ψ c := by
  have hN : spScalars r K = Subgroup.center (StatedSp r K) := (Symplectic.center_eq r K).symm
  obtain ⟨α, hα⟩ := RootDetect.exists_quotAut hN hperf hker hc
  obtain ⟨A, σ, hαeq⟩ := hform α (RootDetect.quotAut_pow_eq_one hN.ge hker hc hα hcp)
  obtain ⟨W, hW⟩ := RootDetect.exists_conj_of_torusOnRoot _ hT
  obtain ⟨ρ, hρ⟩ := Symplectic.SpExtras.exists_stdVec_of_mem_roots hγ
  have hσ : σ = 1 := by
    refine field_eq_one_sp (ρ := ρ) (A := A) (u := u) (W := W) fun t => ?_
    apply eq_of_proj_eq hr
    have h1 := hα _ _ (hW _ (Symplectic.SpExtras.elt_mem_rootGroup hρ t))
    rw [hαeq, MulAut.mul_apply] at h1
    exact h1
  rw [hσ, map_one, mul_one] at hαeq
  obtain ⟨a, ha⟩ := exists_sp_conj_eq A
  have ha' : ∀ y : StatedSp r K, α (y : StatedSp r K ⧸ spScalars r K) =
      ((a * y * a⁻¹ : StatedSp r K) : StatedSp r K ⧸ spScalars r K) := by
    intro y
    rw [hαeq]
    show conjAut r K A (proj r K y) = proj r K (a * y * a⁻¹)
    rw [conjAut_proj, ha y]
  exact RootDetect.ggPsiInnerDiag_of_centralizes _
    (RootDetect.centralizes_of_quotAut_conj hN hperf hc hα ha')

theorem ggPsiInnerDiag_sp [Finite K] [CharP K 2] (hr : 3 ≤ r) {G : Type*} [Group G]
    {ψ : StatedSp r K →* G} (hker : ψ.ker ≤ Subgroup.center (StatedSp r K)) {p : ℕ} {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin r → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum r K).roots) {u : StatedSp r K}
    (hT : GGTorusOnRoot (Symplectic.rootDatum r K) ψ c γ u) :
    GGPsiInnerDiag (Symplectic.rootDatum r K) ψ c :=
  ggPsiInnerDiag_sp_of_aut (by omega) (commutator_statedSp_eq_top (Or.inl hr))
    (fun α _ => (automorphism_generation (K := K) hr).2 α) hker hc hcp hγ hT

theorem sp_two_form_of_pow_eq_one [Finite K] {p : ℕ} (hp : Odd p)
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα : α ^ p = 1) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  obtain ⟨-, -, -, hindex⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  apply mem_spSemilinearAutGroup_iff.mp
  have h0 : (spSemilinearAutGroup 2 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hsq : α ^ 2 ∈ spSemilinearAutGroup 2 K := by
    rcases (show (spSemilinearAutGroup 2 K).index = 1 ∨ (spSemilinearAutGroup 2 K).index = 2 by
      omega) with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      exact Subgroup.mem_top _
    · exact Subgroup.sq_mem_of_index_two h2 α
  obtain ⟨k, rfl⟩ := hp
  have h : α = ((α ^ 2) ^ k)⁻¹ * α ^ (2 * k + 1) := by
    rw [pow_succ α (2 * k), pow_mul, inv_mul_cancel_left]
  rw [h, hα, mul_one]
  exact inv_mem (pow_mem hsq k)

theorem ggPsiInnerDiag_sp_two [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {G : Type*}
    [Group G] {ψ : StatedSp 2 K →* G} (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 K)) {p : ℕ}
    (hp : Odd p) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin 2 → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum 2 K).roots) {u : StatedSp 2 K}
    (hT : GGTorusOnRoot (Symplectic.rootDatum 2 K) ψ c γ u) :
    GGPsiInnerDiag (Symplectic.rootDatum 2 K) ψ c :=
  ggPsiInnerDiag_sp_of_aut (by norm_num) (commutator_statedSp_eq_top (Or.inr ⟨le_rfl, hK⟩))
    (fun α hα => sp_two_form_of_pow_eq_one hp α hα) hker hc hcp hγ hT

end RootDetectSp

section Family

theorem ggRootDetect_psp : GGRootDetect .PSp := by
  intro G _ _ n f ψ hadm hrk hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, hn, hne⟩ := hadm
  rcases (show 3 ≤ n ∨ n = 2 by omega) with h3 | rfl
  · exact RootDetectSp.ggPsiInnerDiag_sp (K := GaloisField 2 f) h3 hker hc hcp hγ hT
  · have hf2 : 2 ≤ f := by
      by_contra h
      obtain rfl : f = 1 := by omega
      exact hne rfl
    have hK : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    exact RootDetectSp.ggPsiInnerDiag_sp_two (K := GaloisField 2 f) hK hker
      (hp.odd_of_ne_two hp2) hc hcp hγ hT

end Family

end CFSG.StandardType
