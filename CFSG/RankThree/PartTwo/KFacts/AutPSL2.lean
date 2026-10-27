module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable (K : Type*) [Field K]

theorem innAut_le_range_pglAction :
    (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range ≤ (pglAction K).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, pglAction_toPGL K x⟩

@[expose] noncomputable def stdPinnedPSL2 : PinnedAut (PSL2 K) where
  inndiag := (pglAction K).range
  inn_le := innAut_le_range_pglAction K
  field := (psl2FieldAut K).range
  graph := ∅

variable {K}

theorem psl2FieldAut_mul_pglAction_mul_inv (σ : K ≃+* K) (g : PGL2 K) :
    psl2FieldAut K σ * pglAction K g * (psl2FieldAut K σ)⁻¹ = pglAction K (pgl2FieldAut K σ g) := by
  have h := DFunLike.congr_fun (pglAction_fieldAut K σ) g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact h.symm

theorem exists_pglAction_mul_psl2FieldAut [Finite K] (α : MulAut (PSL2 K)) :
    ∃ (g : PGL2 K) (σ : K ≃+* K), α = pglAction K g * psl2FieldAut K σ := by
  obtain ⟨x, rfl⟩ := semilinearAction_surjective K α
  refine ⟨x.left, x.right, ?_⟩
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, semilinearAction_inl, semilinearAction_inr]

theorem stdPinnedPSL2_stable [Finite K] : (stdPinnedPSL2 K).Stable := by
  have hcomm : ∀ σ τ : K ≃+* K,
      psl2FieldAut K σ * psl2FieldAut K τ = psl2FieldAut K τ * psl2FieldAut K σ :=
    fun σ τ => by
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  have hconj : ∀ α : MulAut (PSL2 K), ∃ g : PGL2 K, ∀ τ : K ≃+* K,
      α * psl2FieldAut K τ * α⁻¹ = pglAction K g * psl2FieldAut K τ * (pglAction K g)⁻¹ := by
    intro α
    obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
    refine ⟨g, fun τ => ?_⟩
    have h1 := hcomm σ τ
    calc pglAction K g * psl2FieldAut K σ * psl2FieldAut K τ *
          (pglAction K g * psl2FieldAut K σ)⁻¹ =
        pglAction K g * (psl2FieldAut K σ * psl2FieldAut K τ) * (psl2FieldAut K σ)⁻¹ *
          (pglAction K g)⁻¹ := by group
      _ = pglAction K g * psl2FieldAut K τ * (pglAction K g)⁻¹ := by rw [h1]; group
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨h, rfl⟩ := hd
    obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
    refine ⟨g * pgl2FieldAut K σ h * g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← psl2FieldAut_mul_pglAction_mul_inv]
    group
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨g, hg⟩ := hconj α
    exact ⟨psl2FieldAut K τ, ⟨τ, rfl⟩, h1, pglAction K g, ⟨g, rfl⟩, hg τ⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (K) in
@[expose] def InducesKindPSL2 (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K, InducesKind L (stdPinnedPSL2 K) e x k

theorem inducesKindPSL2_iff [Finite K] (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) (x : G)
    (k : AutKind) : InducesKindPSL2 K L x k ↔ InducesKind L (stdPinnedPSL2 K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L stdPinnedPSL2_stable e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
