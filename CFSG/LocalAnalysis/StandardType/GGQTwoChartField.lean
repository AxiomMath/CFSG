module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

private lemma qTwoChartField_map_unitaryInvolution {F0 K : Type} [Field F0] [Field K]
    [Finite F0] [Finite K] [CharP F0 2] [CharP K 2] (φ : F0 ≃+* K) (c : F0) :
    φ (unitaryInvolution F0 2 1 c) = unitaryInvolution K 2 1 (φ c) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply]
  exact map_pow φ c (2 ^ 1)

private lemma qTwoChartField_suidCongr_coe {F0 K : Type} [Field F0] [Field K]
    {σ : F0 ≃+* F0} {σ' : K ≃+* K} (φ : F0 ≃+* K) (he : ∀ c, φ (σ c) = σ' (φ c))
    (t : ℕ) (g : SUid σ t) :
    (((suidCongr φ he t g : SUid σ' t) : GL (Fin t) K) : Matrix (Fin t) (Fin t) K) =
      (((g : GL (Fin t) F0) : Matrix (Fin t) (Fin t) F0)).map φ :=
  coe_suidGLMap φ (g : GL (Fin t) F0)

private lemma qTwoChartField_suidCongr_symm_coe {F0 K : Type} [Field F0] [Field K]
    {σ : F0 ≃+* F0} {σ' : K ≃+* K} (φ : F0 ≃+* K) (he : ∀ c, φ (σ c) = σ' (φ c))
    (t : ℕ) (g : SUid σ' t) :
    ((((suidCongr φ he t).symm g : SUid σ t) : GL (Fin t) F0) :
        Matrix (Fin t) (Fin t) F0) =
      (((g : GL (Fin t) K) : Matrix (Fin t) (Fin t) K)).map φ.symm :=
  coe_suidGLMap φ.symm (g : GL (Fin t) K)

private lemma qTwoChartField_mem_coordBlockSU {F0 K : Type} [Field F0] [Field K]
    [Finite F0] [Finite K] [CharP F0 2] [CharP K 2] (φ : F0 ≃+* K) (t : ℕ)
    {J : Finset (Fin t)} {g : Su F0 2 1 t} (hg : g ∈ coordBlockSU F0 2 1 J) :
    suidCongr φ (qTwoChartField_map_unitaryInvolution φ) t g ∈ coordBlockSU K 2 1 J := by
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  rw [qTwoChartField_suidCongr_coe, Matrix.map_apply, hg i j hij]
  by_cases h : i = j <;> simp [h]

private lemma qTwoChartField_mem_coordBlockSU_symm {F0 K : Type} [Field F0] [Field K]
    [Finite F0] [Finite K] [CharP F0 2] [CharP K 2] (φ : F0 ≃+* K) (t : ℕ)
    {J : Finset (Fin t)} {g : Su K 2 1 t} (hg : g ∈ coordBlockSU K 2 1 J) :
    (suidCongr φ (qTwoChartField_map_unitaryInvolution φ) t).symm g ∈
      coordBlockSU F0 2 1 J := by
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  rw [qTwoChartField_suidCongr_symm_coe, Matrix.map_apply, hg i j hij]
  by_cases h : i = j <;> simp [h]

theorem qTwoChart_fieldTransport {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hF0 : Nat.card F0 = 4) (hK : Nat.card K = 4)
    (t : ℕ) :
    ∃ e : Su F0 2 1 t ≃* Su K 2 1 t,
      ∀ J : Finset (Fin t),
        (coordBlockSU F0 2 1 J).map e.toMonoidHom = coordBlockSU K 2 1 J := by
  haveI := Fintype.ofFinite F0
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card F0 = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF0, hK]
  let φ : F0 ≃+* K := FiniteField.ringEquivOfCardEq hcard
  refine ⟨suidCongr φ (qTwoChartField_map_unitaryInvolution φ) t, fun J => ?_⟩
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact qTwoChartField_mem_coordBlockSU φ t hg
  · intro g hg
    exact ⟨(suidCongr φ (qTwoChartField_map_unitaryInvolution φ) t).symm g,
      qTwoChartField_mem_coordBlockSU_symm φ t hg, by simp⟩

end CFSG.StandardType.QTwo

end
