module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Matrix LayerCores

theorem card_comap_of_le_range {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {S : Subgroup G'} (hS : S ≤ f.range) :
    Nat.card (S.comap f) = Nat.card S := by
  rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hS]

section Adj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_coreFamily_adjCent_pDiv [Finite K] [CharP K 2] {A : Subgroup (GL ι K)}
    (hA : (Nat.card A : K) ≠ 0) {adj : Matrix ι ι K → Matrix ι ι K} (hadj : IsInvol adj)
    (hadjK : ∀ (c : K) (X : Matrix ι ι K), adj (c • X) = c • adj X)
    (hstab : ∀ X : Matrix ι ι K, (∀ g ∈ A, X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * X) →
      ∀ g ∈ A, adj X * (g : Matrix ι ι K) = (g : Matrix ι ι K) * adj X)
    (hsymd : ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + adj Y = 1) {p : ℕ} (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (β : Type) (S : β → Subgroup (GL ι K)), IsCoreFamily (adjCent A hadj) S ∧
      ∀ c, p ∣ Nat.card (S c) := by
  classical
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR hadj fun X hX =>
    (hR _).mpr (hstab X ((hR X).mp hX))
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  have hτF : ∀ a : K, τ (algebraMap K (PiMat D d) a) = algebraMap K (PiMat D d) a := by
    intro a
    apply hΦ
    rw [hτΦ, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, hadjK, hadj.map_one]
  have hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine altCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
      have h1 := congrFun hY b
      rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
    · push Not at hk
      exact hermCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk
  have hpair : ∀ b, π b ≠ b → HasCore (⊤ : Subgroup (GL (Fin (d b)) (D b))) :=
    fun b _ => hasCore_top_GL (d b)
  have hcore := hasCore_factorGroup hτ hπ hfix hpair
  have hX : ∀ b, b ≤ π b → Group.IsSolvable (factorGroup π hτ hπ b) ∨
      ∃ X : Subgroup (GL (Fin (d b)) (D b)), X ≤ factorGroup π hτ hπ b ∧ ⁅X, X⁆ = X ∧
        p ∣ Nat.card X := by
    intro b _
    have hpD2 : p ∣ Nat.card (D b) ^ 2 - 1 := hpK.trans sq_sub_one_dvd_of_algebra
    by_cases hb : π b = b
    · have hfg : factorGroup π hτ hπ b = matUnitary (isInvol_tauFix hτ hπ hb) := by
        unfold factorGroup
        split_ifs
        rfl
      rw [hfg]
      by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
          Matrix.scalar (Fin (d b)) c
      · obtain ⟨Y, hY⟩ := hy
        have hYb : Y b + tauFix τ b (Y b) = 1 := by
          have h1 := congrFun hY b
          rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
        rcases altFactorPDivInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, hYb⟩
          with h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · exact Or.inr ⟨X, hX1, hX2, hpD2.trans hX3⟩
      · push Not at hk
        rcases hermFactorPDivInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk with
          h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · refine Or.inr ⟨X, hX1, hX2, (hpK.trans ?_).trans hX3⟩
          obtain ⟨ρ, hρ, hρ2⟩ := (isInvol_tauFix hτ hπ hb).exists_rho
          refine sq_sub_one_dvd_card_sub_one_of_invol ρ hρ2 ?_ fun a => ?_
          · obtain ⟨c, hc⟩ := hk
            exact ⟨c, fun h => hc (by rw [hρ, h])⟩
          · apply scalar_injective (d := d b)
            rw [← hρ, tauFix_scalar_algebraMap hτ hπ hb hτF]
    · have hfg : factorGroup π hτ hπ b = ⊤ := by
        unfold factorGroup
        split_ifs
        rfl
      rw [hfg]
      rcases glFactor_pDiv (E := D b) (d b) with h | ⟨X, hX1, hX2, hX3⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, hX1, hX2, hpD2.trans hX3⟩
  obtain ⟨β, S, h1, h2, h3, h4, h5⟩ := exists_core_of_factors hτ hπ hfix hpair
  have hS : IsCoreFamily (unitaryOf hτ) S := ⟨h1, h2, h3, h4, h5⟩
  have hSadj := hS.map _ (Units.map_injective (f := Φ.toMonoidHom) hΦ)
  rw [himg] at hSadj
  refine ⟨β, fun c => (S c).map (Units.map Φ.toMonoidHom), hSadj, fun c => ?_⟩
  rw [Subgroup.card_map_of_injective (Units.map_injective (f := Φ.toMonoidHom) hΦ)]
  exact dvd_card_of_conj_mem_unitaryOf hτ hπ hcore hX (h1 c) (h2 c) (h3 c)

end Adj

open QuadraticMap CFSG.ClassicalGroups.Orthogonal in
theorem exists_coreFamily_orthFree_pDiv {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (W ≃ₗ[K] W)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A))
    (hfree : ∀ w : W, (∀ a ∈ A, a w = w) → w = 0) {p : ℕ} (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsCoreFamily (Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  set b := Module.finBasis K W with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (polar_map_of_mem (hAO ha))
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (matEquiv b).injective).toEquiv.symm]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  obtain ⟨β, S, hS, hSp⟩ := exists_coreFamily_adjCent_pDiv hcard hadj (gramAdj_smul M)
    (fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hA'U hX hg) ⟨Y, hYc, hY⟩ hpK
  have hsurj : ∀ T : Subgroup (GL (Fin (Module.finrank K W)) K),
      T ≤ ((matEquiv b).toMonoidHom).range := fun _ g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective (hsurj _)
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hcent : (matEquiv b).toMonoidHom g ∈ Subgroup.centralizer (A' : Set (GL (Fin _) K)) ↔
        g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) := by
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        exact (matEquiv b).injective (by
          rw [map_mul, map_mul]
          exact h _ ⟨a, ha, rfl⟩)
      · rintro h _ ⟨a, ha, rfl⟩
        show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
        rw [← map_mul, ← map_mul, h a ha]
    rw [hcent]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfree hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (polar_map_of_mem hgO)⟩
  rw [hC] at h
  refine ⟨β, _, h, fun c => ?_⟩
  rw [card_comap_of_le_range (matEquiv b).injective (hsurj _)]
  exact hSp c

end LayerPDiv

end CFSG.StandardType
